#!/usr/bin/env python
"""Swiper for console

TODO:
  - validate that loop is not `kqueue` based
  - close if `reader` or `writer` fails (better errors)
  - use lighter queues?
  - disable signals
  - handle resize with loop.add_signal_handler(signal.SIGWINCH, self._on_resize)
  - typing
  - see colors methods

  - `aenter` to make sure that tty ready (ECHO is set correctly for example)
  - handle CPR (current possition request) '\x1b[6n' -> '\x1b[{line};{column}R'
  - resetore terminal even in case of `KeyboardInterrupt`
"""
import array
import asyncio
import fcntl
import os
import sys
import termios
import warnings
from functools import partial

from typing import (
    Generator,
    Iterable,
    NamedTuple,
    Tuple,
    Union,
)

Color = Tuple[int, int, int]


def coro(fn):
    """Create lite double barrel contiuation from generator

    - generator must yield continuation `ContT r a = ((a -> r), (e -> r)) -> r`
    """
    def coro_fn(*args, **kwargs):
        def cont_fn(on_done, on_error):
            def coro_next(ticket, is_error, result):
                nonlocal gen_ticket
                if gen_ticket != ticket:
                    warnings.warn(
                        f'coro_next called with incorrect ticket: '
                        f'{ticket} != {gen_ticket} '
                        f'[{fn}(*{args}, **{kwargs})]',
                        RuntimeWarning,
                    )
                    return
                gen_ticket += 1

                try:
                    cont = gen.throw(result) if is_error else gen.send(result)
                except StopIteration as ret:
                    gen.close()
                    return on_done(ret.args[0] if ret.args else None)
                except Exception:
                    gen.close()
                    return on_error(sys.exc_info())
                else:
                    return cont(partial(coro_next, ticket + 1, False),
                                partial(coro_next, ticket + 1, True))

            try:
                gen = fn(*args, **kwargs)
                gen_ticket = 0
                return coro_next(0, False, None)
            except Exception:
                return on_error(sys.exc_info())
        return cont_fn
    return coro_fn


def cont(done, error=None):
    def cont(on_done, on_error):
        done(on_done)
        if error is not None:
            error(on_error)
    return cont


class Event:
    def __init__(self):
        self.queue = []

    def __call__(self, on_done, on_error):
        self.queue.append((on_done, on_error))

    def error(self, error):
        self.queue, queue = [], self.queue
        for _, on_error in queue:
            on_error((type(error), error, None))

    def done(self, result):
        self.queue, queue = [], self.queue
        for on_done, _ in queue:
            on_done(result)


class Key(NamedTuple):
    key: bytes
    data: bytes


class TTYParser:
    __slots__ = ('_parser_coro',)

    def __init__(self) -> None:
        self._parser_coro = self._parser()
        self._parser_coro.send(None)

    def __call__(self, chunk: bytes) -> Iterable[Key]:
        return self._parser_coro.send(chunk)

    def _parser(self) -> Generator[Iterable[Key], bytes, None]:
        result: Iterable[Key] = []
        while True:
            chunk = yield result
            # TODO: actual parsing
            result = [Key(chunk, chunk)]


class TTY:
    __slots__ = ('fd', 'input', 'output', 'loop', 'closed',)

    DEFAULT_FILE = '/dev/tty'
    ATTR_BY_NAME = {
        'bold': b'01;',
        'italic': b'03;',
        'underline': b'04;',
        'blink': b'05;',
        'negative': b'07;',
    }

    def __init__(self, file: Union[int, str] = None, *, loop=None) -> None:
        if isinstance(file, int):
            self.fd = file
        else:
            self.fd = os.open(file or self.DEFAULT_FILE, os.O_RDWR)
        assert os.isatty(self.fd), f'file must be a tty: {file}'

        self.loop = asyncio.get_event_loop() if loop is None else loop
        self.input: asyncio.Queue[Key] = asyncio.Queue()
        self.output = open(self.fd, mode='wb', closefd=False)

        async def reader() -> None:
            parser = TTYParser()
            while True:
                try:
                    chunk = os.read(self.fd, 1024)
                    if not chunk or chunk == b'q':  # TODO: better quiting handler
                        return None
                except (BlockingIOError,):
                    fut = loop.create_future()
                    self.loop.add_reader(
                        self.fd,
                        lambda fut: fut.cancelled() or fut.set_result(None),
                        fut,
                    )
                    await fut
                    self.loop.remove_reader(self.fd)
                else:
                    keys = parser(chunk)
                    for key in keys:
                        await self.input.put(key)

        @coro
        def reader_coro():
            parser = TTYParser()
            while True:
                try:
                    chunk = os.read(self.fd, 1024)
                    if not chunk or chunk == b'q':
                        return None
                except (BlockingIOError,):
                    try:
                        yield cont(partial(self.loop.add_reader, self.fd))
                    finally:
                        self.loop.remove_reader(self.fd)
                else:
                    keys = parser(chunk)
                    for key in keys:
                        self.input.put_nowait(key)

        async def writer() -> None:
            while True:
                await asyncio.sleep(1)

        async def closer() -> None:
            fd = self.fd
            os.set_blocking(self.fd, False)

            attrs_old = termios.tcgetattr(fd)
            attrs_new = termios.tcgetattr(fd)

            IFLAG, LFLAG = 0, 3
            attrs_new[IFLAG] = attrs_new[IFLAG] & ~termios.ICRNL
            attrs_new[LFLAG] = attrs_new[LFLAG] & ~(
                termios.ICANON |
                termios.ECHO  # |
                # termios.ISIG
            )

            tasks = []
            try:
                # set tty attributes
                termios.tcsetattr(fd, termios.TCSADRAIN, attrs_new)

                # schedule tasks
                tasks.append(self.loop.create_task(reader()))
                tasks.append(self.loop.create_task(writer()))
                for task in tasks:
                    task.add_done_callback(lambda _: self.close())

                await self.closed
            finally:
                # stop tasks
                for task in tasks:
                    task.cancel()
                # restore tty attributes
                termios.tcsetattr(fd, termios.TCSADRAIN, attrs_old)
                # close descriptors
                self.output.close()
                os.close(fd)
        self.closed = self.loop.create_future()
        self.loop.create_task(closer())

    def __enter__(self):
        return self

    def __exit__(self, et, eo, tb):
        self.close(eo)
        return False

    def __del__(self):
        self.close()

    def __await__(self):
        return self.closed

    def __aiter__(self):
        return self

    def __anext__(self):
        return self.input.get()

    def close(self, error=None) -> None:
        if not self.closed.done():
            if error is None:
                self.closed.set_result(None)
            else:
                self.closed.set_exception(error)

    def write(self, input: bytes) -> None:
        self.output.write(input)

    def flush(self) -> None:
        self.output.flush()

    def fileno(self) -> int:
        return self.fd

    def size(self) -> Tuple[int, int]:
        """Console size (rows, columns)
        """
        buf = array.array('H', (0, 0, 0, 0))
        if fcntl.ioctl(self.fileno(), termios.TIOCGWINSZ, buf):
            return (0, 0)  # ioctl failed
        else:
            return (buf[0], buf[1])

    def cursor_up(self, count: int) -> None:
        if count == 0:
            pass
        elif count == 1:
            self.write(b'\x1b[A')
        elif count > 1:
            self.write(f'\x1b[{count}A'.encode())
        else:
            self.cursor_down(-count)

    def cursor_down(self, count: int) -> None:
        if count == 0:
            pass
        elif count == 1:
            self.write(b'\x1b[B')
        elif count > 1:
            self.write(f'\x1b[{count}B'.encode())
        else:
            self.cursor_up(-count)

    def cursor_to_column(self, index: int) -> None:
        if index == 0:
            self.write(b'\x1b[G')
        elif index > 1:
            self.write(f'\x1b[{index}'.encode())
        else:
            raise ValueError(f'column index can not be negative: {index}')

    def cursor_forward(self, count: int) -> None:
        if count == 0:
            pass
        elif count == 1:
            self.write(b'\x1b[C')
        elif count > 1:
            self.write(f'\x1b[{count}C'.encode())
        else:
            self.cursor_backward(-count)

    def cursor_backward(self, count: int) -> None:
        if count == 0:
            pass
        elif count == 1:
            self.write(b'\x1b[D')
        elif count > 1:
            self.write(f'\x1b[{count}D'.encode())
        else:
            self.cursor_forward(-count)

    def erase_line(self) -> None:
        self.write(b'\x1b[K')

    def color(
        self,
        fg: Color = None,
        bg: Color = None,
        attrs: Iterable[str] = None,
    ) -> None:
        # TODO:
        #  - support non true-color terminals
        #  - add color caching?
        seq = [b'\x1b[']
        if attrs:
            for attr in attrs:
                attr_code = self.ATTR_BY_NAME.get(attr)
                if attr_code is None:
                    raise ValueError(f'unknown color attribute: {attr}')
                seq.append(attr_code)
        if fg:
            seq.append('38;2;{};{};{};'.format(*fg).encode())
        if bg:
            seq.append('48;2;{};{};{};'.format(*bg).encode())
        seq.append(b'm')
        self.write(b''.join(seq))


def main() -> None:
    import sys
    if sys.platform in ('darwin',):
        # kqueue does not support devices
        import selectors
        asyncio.set_event_loop(
            asyncio.SelectorEventLoop(selectors.SelectSelector()))
    loop = asyncio.get_event_loop()
    loop.set_debug(True)

    import logging
    logging.getLogger('asyncio').setLevel(logging.WARNING)

    orange = (255, 128, 0)
    grey = (128, 128, 128)
    with TTY(loop=loop) as tty:
        # TODO: this is suppored to called after `closer` coro blocks
        tty.write(f'SIZE: {tty.size()}\n'.encode())
        tty.color(orange, attrs=('bold', 'underline'))
        tty.write(b'test')
        tty.color()
        tty.write(b'\n')
        tty.flush()

        async def printer():
            async for key in tty:
                print(key)
        task = loop.create_task(printer())
        loop.run_until_complete(tty)
        task.cancel()
        loop.run_until_complete(task)

    loop.close()
    # loop.run_until_complete(loop.shutdown_asyncgens())
    # import pdb; pdb.set_trace()
    # import gc; gc.collect()


if __name__ == '__main__':
    main()
