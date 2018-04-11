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


# ------------------------------------------------------------------------------
# Coroutine
# ------------------------------------------------------------------------------
def coro(fn):
    """Create lite double barrel contiuation from generator

    - generator must yield continuation `ContT r a = ((a -> r), (e -> r)) -> r`
    """
    def coro_fn(*args, **kwargs):
        def cont_fn(on_done, on_error):
            def coro_next(ticket, is_error, result=None):
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


def thunk(fn):
    """Decorate function, it will be executed only once
    """
    def fn_thunk(*args, **kwargs):
        if not cell:
            cell.append(fn(*args, **kwargs))
        return cell[0]
    cell = []
    return fn_thunk


def cont(in_done, in_error=None):
    """Create continuation from (done, error) pair
    """
    def cont(out_done, out_error):
        def safe_out_done(result=None):
            return out_done(result)
        in_done(safe_out_done)

        if in_error is not None:
            def safe_out_error(error=None):
                if error is None:
                    try:
                        raise asyncio.CancelError()
                    except Exception:
                        out_error(sys.exc_info())
                else:
                    out_error(error)
            in_error(safe_out_error)
    return cont


def cont_run(cont, in_done=None, in_error=None):
    nothing = lambda _: None
    return cont(
        nothing if in_done is None else in_done,
        nothing if in_error is None else in_error,
    )


def cont_any(*conts):
    """Create continuatino which is equal to first completed continuation
    """
    def cont_any(out_done, out_error):
        @thunk
        def callback(is_error, result=None):
            return out_error(result) if is_error else out_done(result)
        on_error = partial(callback, True)
        on_done = partial(callback, False)

        for cont in conts:
            cont(on_done, on_error)
    return cont_any


def cont_finally(cont, callback):
    """Add `finally` callback to continuation
    """
    def cont_finally(out_done, out_error):
        def with_callback(fn, arg):
            try:
                return fn(arg)
            finally:
                callback()
        return cont(partial(with_callback, out_done),
                    partial(with_callback, out_error))
    return cont_finally

def cont_from_future(future):
    """Create continuation from `Future` object
    """
    def cont_from_future(out_done, out_error):
        def done_callback(future):
            try:
                out_done(future.result())
            except Exception:
                out_error(sys.exc_info())
        future.add_done_callback(done_callback)
    return cont_from_future


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


# ------------------------------------------------------------------------------
# TTY
# ------------------------------------------------------------------------------
MODE_ALT = 0b001
MODE_CTRL = 0b010
MODE_SHIFT = 0b100
MODE_BITS = 3


class Key(tuple):
    def __new__(cls, key, mode=0, attrs=None):
        return tuple.__new__(cls, (key, mode, attrs))

    def __repr__(self):
        key, mode, attrs = self
        name = []
        if mode & MODE_CTRL:
            name.append('ctrl')
        if mode & MODE_ALT:
            name.append('alt')
        name.append(key)
        return 'Key({}{})'.format(
            '-'.join(name),
            '' if attrs is None else f', attrs={attrs}',
        )


class TTYParser:
    __slots__ = ('_parser_coro',)

    def __init__(self) -> None:
        self._parser_coro = self._parser()
        self._parser_coro.send(None)

    def __call__(self, chunk: bytes) -> Iterable[Key]:
        keys = []
        for byte in chunk:
            key = self._parser_coro.send(byte)
            while key is not None:
                keys.append(key)
                key = self._parser_coro.send(None)
        return keys


    def _parser(self) -> Generator[Iterable[Key], bytes, None]:
        buffer = bytearray()
        index = 0

        def get():
            if len(buffer) == index + 1:
                buffer.append((yield))
            index += 1
            return buffer[index]

        def back(count):
            nonlocal index
            index -= count

        def drop():
            nonlocal index
            def buffer[:-index]
            index = 0

        while True:
            if buffer:
                for byte in buffer:
                    yield Key('char', 0, byte)
                del buffer[:]

            buffer.append((yield))

            yield from self._parse_utf8(buffer, index)
            if not buffer:
                pass

            save = index
            if (yield from self._parse_cpr(buffer)) is None:
                index = save
                continue

            if 0 < buffer[-1] < 27:
                yield Key(chr(buffer[-1] + 96), MODE_CTRL)
                del buffer[:]
                continue
            elif buffer[-1] == 27:  # \x1b
                buffer.append((yield))
                if buffer[-1] == 91:  # [
                    buffer.append((yield))
                    # arrows
                    if 64 < buffer[-1] < 69:  # {A, B, C, D}
                        arrow = ('up', 'down', 'right', 'left')[buffer[-1] - 65]
                        yield Key(arrow)
                        del buffer[:]
                        continue
                    # alt + arrows
                    elif buffer[-1] == 49:
                        buffer.append((yield))
                        if buffer[-1] == 59:  # ;
                            buffer.append((yield))
                            if buffer[-1] == 57:  # 9
                                buffer.append((yield))
                                if 64 < buffer[-1] < 69:
                                    arrow = ('up', 'down', 'right', 'left')[buffer[-1] - 65]
                                    yield Key(arrow, MODE_ALT)
                                    del buffer[:]
                                    continue
                    else:
                        continue

    def _parse_utf8(self, buffer, index):
        if buffer[-1] >> 5 == 0b110:  # 2 bytes UTF-8
            ordinal = buffer[-1] & 0b11111
            count = (1,)
        elif buffer[-1] >> 4 == 0b1110:  # 3 bytes UTF-8
            ordinal = buffer[-1] & 0b1111
            count = (1, 2)
        elif buffer[-1] >> 3 == 0b11110:  # 4 bytes UTF-8
            ordinal = buffer[-1] & 0b111
            count = (1, 2, 3)
        else:
            return

        for _ in count:
            buffer.append((yield))
            if buffer[-1] >> 6 != 0b10:
                return
            ordinal = (ordinal << 6) | (buffer[-1] & 0b111111)

        try:
            char = chr(ordinal)
        except ValueError:
            return
        else:
            yield Key('utf8', attrs=chr(ordinal))
            del buffer[:]

    def _parse_number(self, get, back):
        value = None
        while True:
            byte = yield from get()
            if 47 < byte < 58:
                if value is None:
                    value = byte - 48
                else:
                    value = value * 10 - 48 + byte
            else:
                back(1)
        return value

    def _parse_cpr(self, get, back):
        """Parse CPR (current position request)

        format: \x1b[{line};{column}R
        """
        if (yield from get()) != 27:  # \x1b
            return
        if (yield from get()) != 91:  # [
            return
        line = yield from self._parse_number(get, back)
        if line is None:
            return
        if (yield from get()) != 59:  # ;
            return
        column = yield from self._parse_number(get, back)
        if column is None:
            return
        if (yield from get()) != 82:  # R
            return
        yield Key('cpr', attrs=(line, column))


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

        self.closed = self.loop.create_future()
        cont_run(
            self._closer(),
            partial(print, 'closer done:'),
            partial(print, 'closer error:'),
        )

        # self.loop.create_task(closer())

    @coro
    def _closer(self):
        os.set_blocking(self.fd, False)

        attrs_old = termios.tcgetattr(self.fd)
        attrs_new = termios.tcgetattr(self.fd)
        IFLAG, LFLAG = 0, 3
        attrs_new[IFLAG] = attrs_new[IFLAG] & ~termios.ICRNL
        attrs_new[LFLAG] = attrs_new[LFLAG] & ~(
            termios.ICANON # |
            # termios.ECHO |
            # termios.ISIG
        )

        try:
            # set tty attributes
            termios.tcsetattr(self.fd, termios.TCSADRAIN, attrs_new)

            cont_run(cont_finally(self._reader(), self.close))
            yield cont_from_future(self.closed)
        finally:
            # restore tty attributes
            termios.tcsetattr(self.fd, termios.TCSADRAIN, attrs_old)

            # close descriptors
            self.output.close()
            os.close(self.fd)

    @coro
    def _reader(self):
        parser = TTYParser()
        while True:
            try:
                chunk = os.read(self.fd, 1024)
                if not chunk or chunk == b'q':
                    return None
                print(chunk)
            except (BlockingIOError,):
                try:
                    yield cont_any(
                        cont(partial(self.loop.add_reader, self.fd)),
                        cont_from_future(self.closed),
                    )
                finally:
                    self.loop.remove_reader(self.fd)
            else:
                keys = parser(chunk)
                for key in keys:
                    self.input.put_nowait(key)

    # async def _reader_old() -> None:
    #     parser = TTYParser()
    #     while True:
    #         try:
    #             chunk = os.read(self.fd, 1024)
    #             if not chunk or chunk == b'q':  # TODO: better quiting handler
    #                 return None
    #         except (BlockingIOError,):
    #             fut = loop.create_future()
    #             self.loop.add_reader(
    #                 self.fd,
    #                 lambda fut: fut.cancelled() or fut.set_result(None),
    #                 fut,
    #             )
    #             await fut
    #             self.loop.remove_reader(self.fd)
    #         else:
    #             keys = parser(chunk)
    #             for key in keys:
    #                 await self.input.put(key)

    # async def _writer(self) -> None:
    #     while True:
    #         await asyncio.sleep(1)

    # async def _closer(self) -> None:
    #     fd = self.fd
    #     os.set_blocking(self.fd, False)

    #     attrs_old = termios.tcgetattr(fd)
    #     attrs_new = termios.tcgetattr(fd)

    #     IFLAG, LFLAG = 0, 3
    #     attrs_new[IFLAG] = attrs_new[IFLAG] & ~termios.ICRNL
    #     attrs_new[LFLAG] = attrs_new[LFLAG] & ~(
    #         termios.ICANON |
    #         termios.ECHO  # |
    #         # termios.ISIG
    #     )

    #     tasks = []
    #     try:
    #         # set tty attributes
    #         termios.tcsetattr(fd, termios.TCSADRAIN, attrs_new)

    #         # schedule tasks
    #         tasks.append(self.loop.create_task(self._reader()))
    #         tasks.append(self.loop.create_task(self._writer()))
    #         for task in tasks:
    #             task.add_done_callback(lambda _: self.close())

    #         await self.closed
    #     finally:
    #         # stop tasks
    #         for task in tasks:
    #             task.cancel()
    #         # restore tty attributes
    #         termios.tcsetattr(fd, termios.TCSADRAIN, attrs_old)
    #         # close descriptors
    #         self.output.close()
    #         os.close(fd)

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

    def cursor_cpr(self):
        self.write(b'\x1b[6n')

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
                if key == Key('a', MODE_CTRL):
                    tty.cursor_cpr()
                    tty.flush()
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
