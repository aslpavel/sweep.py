#!/usr/bin/env python
"""Swiper for console

TODO:
  - validate that loop is not `kqueue` based
  - use lighter queues?
  - disable signals
  - unittests
  - more renering modes for `Text` including `bash PS` mode
  - add types
"""
import array
import asyncio
import fcntl
import io
import itertools as it
import operator as op
import os
import re
import signal
import string
import sys
import termios
import traceback
import tty
import warnings
from functools import (partial, reduce)

from typing import (
    Generator,
    Iterable,
    NamedTuple,
    Tuple,
    Union,
)


# ------------------------------------------------------------------------------
# Utils
# ------------------------------------------------------------------------------
def apply(fn, *args, **kwargs):
    return fn(*args, **kwargs)


def const(value):
    return lambda _: value


def debug(fn):
    def fn_debug(*args, **kwargs):
        try:
            return fn(*args, **kwargs)
        except Exception as error:
            sys.stderr.write(f'\x1b[31;01m{repr(error)}\x1b[m\n')
            pdb.post_mortem()
            raise
    import sys
    import pdb
    return fn_debug


def thunk(fn):
    """Decorate function, it will be executed only once
    """
    def fn_thunk(*args, **kwargs):
        if not cell:
            cell.append(fn(*args, **kwargs))
        return cell[0]
    cell = []
    return fn_thunk


# ------------------------------------------------------------------------------
# Matcher
# ------------------------------------------------------------------------------
class Pattern:
    STATE_START = 0
    STATE_FAIL = -1

    def __init__(self, table, finals, epsilons=None):
        assert all(-1 <= s < len(table) for ss in table for s in ss.values()),\
            f'invalid transition state found: {table}'
        assert all(-1 <= s <= len(table) for s in finals),\
            f'invalid final state found: {finals}'

        self.table = table
        self.finals = finals
        self.epsilons = epsilons or {}

    def __call__(self):
        pattern = self
        if self.epsilons:
            pattern = self.optimize()
        table = pattern.table
        finals = pattern.finals

        STATE_START, STATE_FAIL = self.STATE_START, self.STATE_FAIL

        def parse(input):
            nonlocal state, results, buffer, consumed

            if input is None:
                # initialize state
                state = STATE_START
                results = []
                buffer = bytearray()
                consumed = 0
            else:
                buffer.append(input)
                if state != STATE_FAIL:
                    state = table[state].get(input, STATE_FAIL)

            fs = finals.get(state)
            if fs:
                results.extend(f(buffer) for f in fs)
                consumed = len(buffer)

            return (
                state != STATE_FAIL and bool(table[state]),  # alive
                results,
                buffer[consumed:],
            )

        # state variables
        state = STATE_FAIL  # expect first input as `None`
        results = None
        buffer = None
        consumed = None

        return parse

    def map(self, fn):
        """Replace mappers for finals (not sequencable after this)
        """
        table, _, (finals,), epsilons = self._merge((self,))
        return Pattern(table, {f: (fn,) for f, _ in finals.items()}, epsilons)

    @classmethod
    def choice(cls, patterns):
        assert len(patterns) > 0, 'pattern set must be non empyt'
        table, starts, finals, epsilons = cls._merge(patterns, table=[{}])
        epsilons[0] = set(starts)
        return Pattern(table, {f: cb for fs in finals for f, cb in fs.items()}, epsilons)

    def __or__(self, other):
        return self.choice((self, other))

    @classmethod
    def sequence(cls, patterns):
        assert len(patterns) > 0, 'patterns set must be non empyt'
        table, starts, finals, epsilons = cls._merge(patterns)

        for s, fs in zip(starts[1:], finals):
            for f, cb in fs.items():
                assert not cb, 'only last pattern can have callback'
                epsilons.setdefault(f, set()).add(s)
        finals = finals[-1]

        return Pattern(table, finals, epsilons)

    def __add__(self, other):
        return self.sequence((self, other))

    def some(self):
        table, _, (finals,), epsilons = self._merge((self,))
        for final in finals:
            epsilons.setdefault(final, set()).add(0)
        return Pattern(table, finals, epsilons)

    def many(self):
        pattern = self.some()
        for final in pattern.finals:
            pattern.epsilons.setdefault(0, set()).add(final)
        return pattern

    @classmethod
    def _merge(cls, patterns, table=None):
        """(Merge|Copy) multiple patterns into single one

        Puts all states from all patterns into a single table, and updates
        all states with appropriate offset.
        """
        table = table or []
        starts = []
        finals = []
        epsilons = {}

        for pattern in patterns:
            offset = len(table)
            starts.append(offset)
            for tran in pattern.table:
                table.append({i: s + offset for i, s in tran.items()})
            for s_in, s_outs in pattern.epsilons.items():
                epsilons[s_in + offset] = {s_out + offset for s_out in s_outs}
            finals.append({final + offset: cb
                           for final, cb in pattern.finals.items()})

        return (table, starts, finals, epsilons)

    def optimize(self):
        """Convert NFA to DFA (eleminate epsilons) using powerset construnction
        """
        # NOTE:
        #  - `n_` contains NFA states (indices in table)
        #  - `d_` constains DFA state (subset of all indices in table)
        def epsilon_closure(n_states):
            """Epsilon closure (all state reachable with epsilon move) of set of states
            """
            d_state = set()
            queue = set(n_states)
            while queue:
                n_out = queue.pop()
                n_ins = self.epsilons.get(n_out)
                if n_ins is not None:
                    for n_in in n_ins:
                        if n_in in d_state:
                            continue
                        queue.add(n_in)
                d_state.add(n_out)
            return tuple(sorted(d_state))

        d_start = epsilon_closure({0})
        d_table = {}
        d_finals = {}

        d_queue = [d_start]
        d_found = set()
        while d_queue:
            d_state = d_queue.pop()
            # finals
            for n_state in d_state:
                if n_state in self.finals:
                    d_finals.setdefault(d_state, []).append(self.finals[n_state])
            # transitions
            n_trans = [self.table[n_state] for n_state in d_state]
            d_tran = {}
            for i in {i for n_tran in n_trans for i in n_tran}:
                d_state_new = epsilon_closure(
                    {n_tran[i] for n_tran in n_trans if i in n_tran})
                if d_state_new not in d_found:
                    d_found.add(d_state_new)
                    d_queue.append(d_state_new)
                d_tran[i] = d_state_new
            d_table[d_state] = d_tran

        # normalize (use indicies instead of sets to identify states)
        d_ss_sn = {d_start: 0}  # state-set -> state-norm
        for d_state in d_table.keys():
            d_ss_sn.setdefault(d_state, len(d_ss_sn))
        d_sn_ss = {v: k for k, v in d_ss_sn.items()}  # state-norm -> state-set
        d_table_norm = [
            {i: d_ss_sn[ss] for i, ss in d_table[d_sn_ss[sn]].items()}
            for sn in d_sn_ss
        ]
        d_finals_norm = {d_ss_sn[ss]: tuple(it.chain.from_iterable(cb))
                         for ss, cb in d_finals.items()}

        return Pattern(
            d_table_norm,
            d_finals_norm,
        )

    def show(self, render=True, size=384):
        from graphviz import Digraph

        dot = Digraph(format='png')
        dot.graph_attr['rankdir'] = 'LR'

        for state in range(len(self.table)):
            attrs = {'shape': 'circle'}
            if state in self.finals:
                attrs['shape'] = 'doublecircle'
            dot.node(str(state), **attrs)

        edges = {}
        for state, row in enumerate(self.table):
            for input, state_new in row.items():
                edges.setdefault((state, state_new), []).append(chr(input))
        for (src, dst), inputs in edges.items():
            dot.edge(str(src), str(dst), label=''.join(inputs))

        for epsilon_out, epsilon_ins in self.epsilons.items():
            for epsilon_in in epsilon_ins:
                dot.edge(str(epsilon_out), str(epsilon_in), color='red')

        if sys.platform == 'darwin' and os.environ['TERM'] and render:
            import base64
            iterm_format = '\x1b]1337;File=inline=1;width={width}px:{data}\a\n'
            with open(dot.render(), 'rb') as file:
                sys.stdout.write(iterm_format.format(
                    width=size,
                    data=base64.b64encode(file.read()).decode(),
                ))
        else:
            return dot


def p_byte(b):
    assert 0 <= b <= 255, f'byte expected: {b}'
    return Pattern([{b: 1}, {}], {1: tuple()})


def p_byte_pred(pred):
    return Pattern([{b: 1 for b in range(256) if pred(b)}, {}], {1: tuple()})


@apply
def p_utf8():
    printable_set = set(ord(c) for c in (
        string.ascii_letters + string.digits + string.punctuation + '\t '))
    printable = p_byte_pred(lambda b: b in printable_set)
    utf8_two = p_byte_pred(lambda b: b >> 5 == 0b110)
    utf8_three = p_byte_pred(lambda b: b >> 4 == 0b1110)
    utf8_four = p_byte_pred(lambda b: b >> 3 == 0b11110)
    utf8_tail = p_byte_pred(lambda b: b >> 6 == 0b10)
    return Pattern.choice((
        printable,
        utf8_two + utf8_tail,
        utf8_three + utf8_tail + utf8_tail,
        utf8_four + utf8_tail + utf8_tail + utf8_tail,
    ))


@apply
def p_digit():
    return p_byte_pred(lambda b: ord('0') <= b <= ord('9'))


@apply
def p_number():
    return p_digit.some()


def p_string(bs):
    if isinstance(bs, str):
        bs = bs.encode()
    table = [{b: i + 1} for i, b in enumerate(bs)] + [{}]
    return Pattern(table, {len(table) - 1: tuple()})


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
                    cont = gen.throw(*result) if is_error else gen.send(result)
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


def cont_print_exception(name, source, error):
    et, eo, tb = error
    message = io.StringIO()
    message.write(f'coroutine <{name or ""}> at:\n')
    message.write(source)
    message.write(f'failed with {et.__name__}: {eo}\n')
    traceback.print_tb(tb, file=message)
    sys.stderr.write(message.getvalue())


def cont_run(cont, on_done=None, on_error=None, name=None):
    if on_error is None:
        source = traceback.format_stack()[-2]
        on_error = partial(cont_print_exception, name, source)
    return cont(
        const(None) if on_done is None else on_done,
        on_error,
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
    __slots__ = ('handlers',)

    def __init__(self):
        self.handlers = []

    def __call__(self, event):
        handlers, self.handlers = self.handlers, []
        for handler in handlers:
            if handler(event):
                self.handlers.append(handler)

    def on(self, handler):
        self.handlers.append(handler)

    def on_once(self, handler):
        def handler_once(event):
            handler(event)
            return False
        self.handlers.append(handler)


# ------------------------------------------------------------------------------
# TTY
# ------------------------------------------------------------------------------
TTY_KEY = 0
TTY_CHAR = 1
TTY_CPR = 2
TTY_SIZE = 3
TTY_CLOSE = 4

KEY_MODE_ALT = 0b001
KEY_MODE_CTRL = 0b010
KEY_MODE_SHIFT = 0b100
KEY_MODE_BITS = 3


class TTYEvent(tuple):
    def __new__(cls, type, attrs):
        return tuple.__new__(cls, (type, attrs))

    def __repr__(self):
        type, attrs = self
        if type == TTY_KEY:
            key_name, mode = attrs
            names = []
            for mask, mode_name in (
                    (KEY_MODE_ALT, 'alt'),
                    (KEY_MODE_CTRL, 'ctrl'),
                    (KEY_MODE_SHIFT, 'shift'),
            ):
                if mode & mask:
                    names.append(mode_name)
            names.append(key_name)
            return f'Key({"-".join(names)})'
        elif type == TTY_CHAR:
            return f'Char({attrs})'
        elif type == TTY_CPR:
            line, column = attrs
            return f'Postion(line={line}, column={column})'
        elif type == TTY_CLOSE:
            return 'Close()'
        elif type == TTY_SIZE:
            rows, columns = attrs
            return f'Size(rows={rows}, columns={columns})'


@apply
def p_tty():
    def add(pattern, mapper):
        if isinstance(pattern, (str, bytes)):
            pattern = p_string(pattern)
        if mapper is not None:
            pattern = pattern.map(mapper)
        patterns.append(pattern)
    patterns = []

    def key(name, mode=0):
        return const(TTYEvent(TTY_KEY, (name, mode)))

    # F{X}
    add('\x1bOP', key('f1'))
    add('\x1bOQ', key('f2'))
    add('\x1bOR', key('f3'))
    add('\x1bOS', key('f4'))
    add('\x1b[15~', key('f5'))
    for i in range(6, 11):
        add(f'\x1b[{i + 11}~', key(f'f{i}'))
    add('\x1b[23~', key('f11'))
    add('\x1b[24~', key('f12'))

    # special
    add('\x1b', key('esc'))
    add('\x1b[5~', key('pageup'))
    add('\x1b[6~', key('pagedown'))
    add('\x1b[H', key('home'))
    add('\x1b[F', key('end'))

    # arrows
    add('\x1b[A', key('up'))
    add('\x1b[B', key('down'))
    add('\x1b[C', key('right'))
    add('\x1b[D', key('left'))
    add('\x1b[1;9A', key('up', KEY_MODE_ALT))
    add('\x1b[1;9B', key('donw', KEY_MODE_ALT))
    add('\x1b[1;9C', key('right', KEY_MODE_ALT))
    add('\x1b[1;9D', key('left', KEY_MODE_ALT))

    # alt-letter
    for b in range(ord('a'), ord('z') + 1):
        add(p_byte(27) + p_byte(b), key(chr(b), KEY_MODE_ALT))
    for b in range(ord('0'), ord('9') + 1):
        add(p_byte(27) + p_byte(b), key(chr(b), KEY_MODE_ALT))

    # ctrl-letter
    for b in range(1, 27):
        add(p_byte(b), key(chr(b + 96), KEY_MODE_CTRL))
    add('\x7f', key('h', KEY_MODE_CTRL))  # backspace

    # CPR (current position report)
    def extract_cpr(buf):
        line, column = (int(v) for v in bytes(buf[2:-1]).decode().split(';'))
        return TTYEvent(TTY_CPR, (line, column))
    add(Pattern.sequence((
        p_string('\x1b['),
        p_number,
        p_string(';'),
        p_number,
        p_string('R'),
    )), extract_cpr)

    # chars
    add(p_utf8, lambda buf: TTYEvent(TTY_CHAR, buf.decode()))

    return Pattern.choice(patterns).optimize()


class TTYParser:
    __slots__ = ('_parse',)

    def __init__(self) -> None:
        self._parse = p_tty()
        self._parse(None)

    def __call__(self, chunk: bytes) -> Iterable[TTYEvent]:
        keys = []
        while True:
            for index, byte in enumerate(chunk):
                alive, results, unconsumed = self._parse(byte)
                if not alive:
                    if results:
                        keys.append(results[-1])
                        self._parse(None)
                        # reschedule unconsumed for parsing
                        unconsumed.extend(chunk[index + 1:])
                        chunk = unconsumed
                        break
                    else:
                        sys.stderr.write(
                            f'[ERROR] failed to process: {bytes(unconsumed)}\n')
                        self._parse(None)
            else:
                # all consumed (no break in for loop)
                break
        return keys


class TTY:
    __slots__ = ('fd', 'size', 'output', 'events', 'events_queue', 'loop', 'closed',)
    DEFAULT_FILE = '/dev/tty'

    def __init__(self, file: Union[int, str] = None, *, loop=None) -> None:
        if isinstance(file, int):
            self.fd = file
        else:
            self.fd = os.open(file or self.DEFAULT_FILE, os.O_RDWR)
        assert os.isatty(self.fd), f'file must be a tty: {file}'

        self.loop = asyncio.get_event_loop() if loop is None else loop
        self.output = open(self.fd, mode='wb', closefd=False)
        self.events = Event()

        def events_queue_handler(event):
            type, _ = event
            if type != TTY_CPR:
                self.events_queue.put_nowait(event)
            return True  # keep subscribed
        self.events_queue = asyncio.Queue()
        self.events.on(events_queue_handler)

        self.closed = self.loop.create_future()
        cont_run(self._closer(), name='TTY._closer')

    @coro
    def _closer(self):
        os.set_blocking(self.fd, False)

        attrs_old = termios.tcgetattr(self.fd)
        attrs_new = termios.tcgetattr(self.fd)
        attrs_new[tty.IFLAG] &= ~reduce(op.or_, (
            # disable flow control ctlr-{s,q}
            termios.IXON,
            termios.IXOFF,
            # carriage return
            termios.ICRNL,
            termios.INLCR,
            termios.IGNCR,
        ))
        attrs_new[tty.LFLAG] &= ~reduce(op.or_, (
            termios.ECHO,
            termios.ICANON,
            termios.IEXTEN,
            # termios.ISIG,
        ))

        try:
            # set tty attributes
            termios.tcsetattr(self.fd, termios.TCSADRAIN, attrs_new)

            # resize handler
            def resize_handler():
                buf = array.array('H', (0, 0, 0, 0))
                if fcntl.ioctl(self.fileno(), termios.TIOCGWINSZ, buf):
                    size = (0, 0)
                else:
                    size = (buf[0], buf[1])
                self.size = size
                self.events(TTYEvent(TTY_SIZE, size))
            resize_handler()
            self.loop.add_signal_handler(signal.SIGWINCH, resize_handler)

            # reader
            readable = Event()
            parser = TTYParser()
            self.loop.add_reader(self.fd, lambda: readable(None))
            readable.on(partial(self._try_read, parser))

            # wait closed event
            yield cont_from_future(self.closed)
        finally:
            self.output.flush()
            # remove resize handler
            self.loop.remove_signal_handler(signal.SIGWINCH)
            # restore tty attributes
            termios.tcsetattr(self.fd, termios.TCSADRAIN, attrs_old)
            # terminate queue
            self.events_queue.put_nowait(TTYEvent(TTY_CLOSE, None))
            # stop reader
            self.loop.remove_reader(self.fd)
            os.close(self.fd)

    def _try_read(self, parser, _):
        try:
            chunk = os.read(self.fd, 1024)
            if not chunk:
                return False  # unsubsribe
        except (BlockingIOError,):
            pass
        else:
            events = parser(chunk)
            for event in events:
                self.events(event)
        return True  # keep subscrbied

    def __enter__(self):
        return self

    def __exit__(self, et, eo, tb):
        self.close(eo)
        return False

    def __await__(self):
        return self.closed

    def __aiter__(self):
        return self

    async def __anext__(self):
        event = await self.events_queue.get()
        type, _ = event
        if type == TTY_CLOSE:
            raise StopAsyncIteration()
        return event

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

    def cursor_to(self, row=0, column=0):
        self.write(f'\x1b[{row};{column}H'.encode())

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
            self.write(f'\x1b[{index}G'.encode())
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

    async def cursor_cpr(self):
        def cpr_handler(event):
            type, attrs = event
            if type != TTY_CPR:
                return True
            else:
                cpr.set_result(attrs)
                return False
        cpr = self.loop.create_future()
        self.events.on(cpr_handler)

        self.write(b'\x1b[6n')
        self.flush()

        return await cpr

    def cursor_hide(self):
        self.write(b'\x1b[?25l')

    def cursor_show(self):
        self.write(b'\x1b[?12l\x1b[?25h')

    def erase_line(self) -> None:
        self.write(b'\x1b[K')

    def erase_down(self):
        self.write(b'\x1b[J')

    def format(self, text):
        """Write formatted text

        """


# ------------------------------------------------------------------------------
# Text
# ------------------------------------------------------------------------------
class Color(tuple):
    __slots__ = tuple()
    HEX_PATTERN = re.compile(
        '^#?'
        '([0-9a-fA-F]{2})'   # red
        '([0-9a-fA-F]{2})'   # green
        '([0-9a-fA-F]{2})'   # blue
        '([0-9a-fA-F]{2})?'  # optional alpha
        '$')

    def __new__(cls, color):
        if isinstance(color, str):
            match = cls.HEX_PATTERN.match(color)
            if match is None:
                raise ValueError(f'invalid color: {color}')
            r, g, b, a = match.groups()
            r = int(r, 16) / 255.0
            g = int(g, 16) / 255.0
            b = int(b, 16) / 255.0
            a = 1.0 if a is None else int(a, 16) / 255.0
            color = (r, g, b, a)
        elif isinstance(color, tuple):
            size = len(color)
            if size == 3:
                color = (*color, 1.0)
            elif size == 4:
                color = color
            else:
                raise ValueError(f'invalid color: {color}')
        else:
            raise ValueError(f'invalid color: {color}')
        return tuple.__new__(cls, color)

    red = property(lambda self: self[0])
    gren = property(lambda self: self[1])
    green = property(lambda self: self[2])
    alpha = property(lambda self: self[3])
    luma = property(lambda self: sum(
        c * p for c, p in zip(self, (0.2126, 0.7152, 0.0722))))

    def overlay(self, other):
        """Overlay other color over current color
        """
        if other is None:
            return self
        r0, g0, b0, a0 = self
        r1, g1, b1, a1 = other
        a01 = (1 - a1) * a0 + a1
        r01 = ((1 - a1) * a0 * r0 + a1 * r1) / a01
        g01 = ((1 - a1) * a0 * g0 + a1 * g1) / a01
        b01 = ((1 - a1) * a0 * b0 + a1 * b1) / a01
        return Color((r01, g01, b01, a01))

    def with_alpha(self, alpha):
        return Color((*self[:3], alpha))

    def __repr__(self):
        return 'Color(\x1b[48;2;{};{};{}m  \x1b[m)'.format(
            *(int(c * 255) for c in self[:3]))


FACE_NONE = 0
FACE_BOLD = 1 << 1
FACE_ITALIC = 1 << 2
FACE_UNDERLINE = 1 << 3
FACE_BLINK = 1 << 4
FACE_REVERSE = 1 << 5
FACE_MAP = (
    (FACE_BOLD, '01;'),
    (FACE_ITALIC, '03;'),
    (FACE_UNDERLINE, '04;'),
    (FACE_BLINK, '05;'),
    (FACE_REVERSE, '07;'),
)


class Face(tuple):
    __slots__ = tuple()

    def __new__(cls, fg=None, bg=None, attrs=FACE_NONE):
        return tuple.__new__(cls, (fg, bg, attrs))

    def overlay(self, other):
        fg0, bg0, attrs0 = self
        fg1, bg1, attrs1 = other
        bg01 = bg1 if bg0 is None else bg0.overlay(bg1)
        fg01 = fg1 if fg0 is None else fg0.overlay(fg1)
        if fg01 is not None:
            fg01 = fg01 if bg01 is None else bg01.overlay(fg01)
        return Face(fg01, bg01, attrs0 | attrs1)

    fg = property(lambda self: self[0])
    bg = property(lambda self: self[1])
    attrs = property(lambda self: self[2])

    def set(self):
        fg, bg, attrs = self
        seq = ['\x1b[']
        if attrs:
            for attr, code in FACE_MAP:
                if attrs & attr:
                    seq.append(code)
        if fg:
            seq.append('38;2;{};{};{};'.format(
                *(int(c * 255) for c in fg[:3])))
        if bg:
            seq.append('48;2;{};{};{};'.format(
                *(int(c * 255) for c in bg[:3])))
        seq.append('m')
        return ''.join(seq)

    def unset(self):
        return '\x1b[m'

    def __repr__(self):
        return f'Face({self.set()} X {self.unset()})'


TEXT_STRING = 1
TEXT_FACE = 2
TEXT_LIST = 3


class Text(tuple):
    """Formated text

    Text = TString String | TFace (Text, Face) | TList [Text]
    """
    __slots__ = tuple()

    def __new__(cls, value, type=TEXT_STRING):
        if type == TEXT_STRING:
            return tuple.__new__(cls, (type, len(value), value))
        elif type == TEXT_FACE:
            text, _ = value
            return tuple.__new__(cls, (type, len(text), value))
        elif type == TEXT_LIST:
            return tuple.__new__(
                cls, (type, sum(len(text) for text in value), value))
        assert False, 'unreachable'

    def __len__(self):
        type, size, value = self
        return size

    def __add__(self, other):
        if isinstance(other, str):
            other = Text(other)
        return Text((self, other), TEXT_LIST)

    def __getitem__(self, selector):
        if isinstance(selector, slice):
            assert slice.step is not None, 'slice step is not supported'
            _, result = self.split(slice.start)
            result, _ = result.split(slice.stop)
            return result
        elif isinstance(selector, int):
            return self[selector:selector + 1]
        else:
            raise ValueError('text indices must be integers')

    def mark(self, start, end, face=Face()):
        left, middle = self.split(start)
        middle, right = middle.split(end - start)
        return Text((left, Text((middle, face), TEXT_FACE), right), TEXT_LIST)

    def split(self, index):
        type, size, value = self
        index = index if index >= 0 else len(self) + index
        if type == TEXT_STRING:
            return Text(value[:index], type), Text(value[index:], type)
        elif type == TEXT_FACE:
            text, face = value
            left, right = text.split(index)
            return Text((left, face), type), Text((right, face), type)
        elif type == TEXT_LIST:
            lefts, rights = [], []
            for i, t in enumerate(value):
                lt = len(t)
                if lt < index:
                    index -= lt
                    lefts.append(t)
                elif lt == index:
                    lefts.append(t)
                    rights.extend(value[i + 1:])
                    break
                else:
                    left, right = t.split(index)
                    lefts.append(left)
                    rights.append(right)
                    rights.extend(value[i + 1:])
                    break
            return Text(lefts, TEXT_LIST), Text(rights, TEXT_LIST)

    def render(self, stream, face=Face()):
        type, size, value = self
        if type == TEXT_STRING:
            stream.write(value)
        elif type == TEXT_FACE:
            f_text, f_face = value
            f_face = face.overlay(f_face)
            stream.write(f_face.set())
            f_text.render(stream, face)
            stream.write('\x1b[m')
            stream.write(face.set())
        elif type == TEXT_LIST:
            for text in value:
                text.render(stream, face)
        return stream

    def __str__(self):
        stream = io.StringIO()
        stream.write('Text(\'')
        self.render(stream)
        stream.write('\')')
        return stream.getvalue()

    def __repr__(self):
        return str(self)

    def __bytes__(self):
        stream = io.StringIO()
        self.render(stream)
        return stream.getvalue().encode()

    def debug(self):
        type, _, value = self
        if type == TEXT_STRING:
            return value
        elif type == TEXT_FACE:
            text, face = value
            return (face, text.debug())
        elif type == TEXT_LIST:
            return tuple(t.debug() for t in value)
        assert False, 'unreachable'


# ------------------------------------------------------------------------------
# Selector
# ------------------------------------------------------------------------------
class Input:
    def __init__(self, prompt=None, buffer=None, cursor=None):
        self.prompt = prompt or ''
        self.buffer = [] if buffer is None else list(buffer)
        self.cursor = len(self.buffer) if cursor is None else cursor

    def __call__(self, event):
        type, attrs = event
        if type == TTY_KEY:
            name, mode = attrs
            if name == 'left':
                self.cursor = max(0, self.cursor - 1)
            elif name == 'right':
                self.cursor = min(len(self.buffer), self.cursor + 1)
            elif mode & KEY_MODE_CTRL:
                if name == 'a':
                    self.cursor = 0
                elif name == 'e':
                    self.cursor = len(self.buffer)
                elif name == 'h':  # delete
                    if self.cursor > 0:
                        self.cursor -= 1
                        del self.buffer[self.cursor]
                elif name == 'k':
                    del self.buffer[self.cursor:]
        elif type == TTY_CHAR:
            self.buffer.insert(self.cursor, attrs)
            self.cursor += 1

    def render(self, tty):
        tty.write(self.prompt.encode())
        tty.write(''.join(self.buffer).encode())
        tty.erase_line()
        tty.cursor_backward(len(self.buffer) - self.cursor)


async def selector(items, *, loop=None):
    face = Face(fg=Color('#ff8040'), attrs=FACE_BOLD)
    header = Text('Press <ctrl-d> to exit\n').mark(6, 14, face)
    ctrl_d = TTYEvent(TTY_KEY, ('d', KEY_MODE_CTRL))
    input = Input('Input: ')

    with TTY(loop=loop) as tty:
        # header
        tty.write(bytes(header))

        tty.write(b'\n\n')
        tty.cursor_up(2)
        line, column = await tty.cursor_cpr()
        async for event in tty:
            tty.cursor_to(line, column)
            tty.write(f'[{event}]'.encode())
            tty.erase_line()

            tty.cursor_to(line + 1, column)
            input(event)
            input.render(tty)

            tty.flush()
            if event == ctrl_d:
                tty.cursor_to(line + 2, column)
                return


# ------------------------------------------------------------------------------
# Entry Point
# ------------------------------------------------------------------------------
def main() -> None:
    # return

    if sys.platform in ('darwin',):
        # kqueue does not support devices
        import selectors
        asyncio.set_event_loop(
            asyncio.SelectorEventLoop(selectors.SelectSelector()))

    # TODO: remove debugging
    loop = asyncio.get_event_loop()
    loop.set_debug(True)
    import logging
    logging.getLogger('asyncio').setLevel(logging.INFO)

    try:
        loop.run_until_complete(selector({}))
    finally:
        loop.run_until_complete(loop.shutdown_asyncgens())
        loop.close()


if __name__ == '__main__':
    main()
