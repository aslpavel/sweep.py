#!/usr/bin/env python
"""Sweep is a command line fuzzy finer (fzf analog)

TODO:
  - use something instead of future in closer coro as it fails to complete
    if loop is not running
  - validate that loop is not `kqueue` based
  - use lighter queues?
  - disable signals
  - unittests
  - add types
"""
import array
import asyncio
import codecs
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
import time
import traceback
import tty
import warnings
from collections import namedtuple, deque
from concurrent.futures import ProcessPoolExecutor
from contextlib import ExitStack
from functools import partial, reduce

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

    - continuation type is `ContT r a = ((a -> r), (e -> r)) -> r`
    - fn must be a generator yielding continuation
    - coro(fn) will return continuation
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

    Executed on_{done|error} before actual continuation
    """
    def cont_finally(out_done, out_error):
        def with_callback(fn, arg):
            callback()
            return fn(arg)
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

    def __await__(self):
        future = asyncio.Future()
        self.on_once(future.set_result)
        return future


# ------------------------------------------------------------------------------
# Matchers
# ------------------------------------------------------------------------------
@apply
def _fuzzy_scorer():
    """Fuzzy matching for `fzy` utility

    source: https://github.com/jhawthorn/fzy/blob/master/src/match.c
    """
    SCORE_MIN = float('-inf')
    SCORE_MAX = float('inf')
    SCORE_GAP_LEADING = -0.005
    SCORE_GAP_TRAILING = -0.005
    SCORE_GAP_INNER = -0.01
    SCORE_MATCH_CONSECUTIVE = 1.0

    def char_range_with(c_start, c_stop, v, d):
        d = d.copy()
        d.update((chr(c), v) for c in range(ord(c_start), ord(c_stop) + 1))
        return d
    lower_with = partial(char_range_with, 'a', 'z')
    upper_with = partial(char_range_with, 'A', 'Z')
    digit_with = partial(char_range_with, '0', '9')

    SCORE_MATCH_SLASH = 0.9
    SCORE_MATCH_WORD = 0.8
    SCORE_MATCH_CAPITAL = 0.7
    SCORE_MATCH_DOT = 0.6
    BONUS_MAP = {
        '/': SCORE_MATCH_SLASH,
        '-': SCORE_MATCH_WORD,
        '_': SCORE_MATCH_WORD,
        ' ': SCORE_MATCH_WORD,
        '.': SCORE_MATCH_DOT,
    }
    BONUS_STATES = [
        {},
        BONUS_MAP,
        lower_with(SCORE_MATCH_CAPITAL, BONUS_MAP),
    ]
    BONUS_INDEX = digit_with(1, lower_with(1, upper_with(2, {})))

    def bonus(haystack):
        """Additional bonus based on previous char in haystack
        """
        c_prev = '/'
        bonus = []
        for c in haystack:
            bonus.append(BONUS_STATES[BONUS_INDEX.get(c, 0)].get(c_prev, 0))
            c_prev = c
        return bonus

    def subsequence(niddle, haystack):
        """Check if niddle is subsequence of haystack
        """
        niddle, haystack = niddle.lower(), haystack.lower()
        if not niddle:
            True
        offset = 0
        for char in niddle:
            offset = haystack.find(char, offset) + 1
            if offset <= 0:
                return False
        return True

    def score(niddle, haystack):
        """Calculate score, and positions of haystack
        """
        n, m = len(niddle), len(haystack)
        bonus_score = bonus(haystack)
        niddle, haystack = niddle.lower(), haystack.lower()

        if n == 0 or n == m:
            return SCORE_MAX, []
        D = [[0] * m for _ in range(n)]  # best score ending with `niddle[:i]`
        M = [[0] * m for _ in range(n)]  # best score for `niddle[:i]`
        for i in range(n):
            prev_score = SCORE_MIN
            gap_score = SCORE_GAP_TRAILING if i == n - 1 else SCORE_GAP_INNER

            for j in range(m):
                if niddle[i] == haystack[j]:
                    score = SCORE_MIN
                    if i == 0:
                        score = j * SCORE_GAP_LEADING + bonus_score[j]
                    elif j != 0:
                        score = max(
                            M[i - 1][j - 1] + bonus_score[j],
                            D[i - 1][j - 1] + SCORE_MATCH_CONSECUTIVE,
                        )
                    D[i][j] = score
                    M[i][j] = prev_score = max(score, prev_score + gap_score)
                else:
                    D[i][j] = SCORE_MIN
                    M[i][j] = prev_score = prev_score + gap_score

        match_required = False
        position = [0] * n
        i, j = n - 1, m - 1
        while i >= 0:
            while j >= 0:
                if ((match_required or D[i][j] == M[i][j]) and D[i][j] != SCORE_MIN):
                    match_required = (
                        i > 0 and
                        j > 0 and
                        M[i][j] == D[i - 1][j - 1] + SCORE_MATCH_CONSECUTIVE
                    )
                    position[i] = j
                    j -= 1
                    break
                else:
                    j -= 1
            i -= 1

        return M[n - 1][m - 1], position

    def fuzzy_scorer(niddle, haystack):
        if subsequence(niddle, haystack):
            return score(niddle, haystack)
        else:
            return SCORE_MIN, None
    return fuzzy_scorer


def fuzzy_scorer(niddle, haystack):
    return _fuzzy_scorer(niddle, haystack)


RankResult = namedtuple('RankResult', (
    'score',
    'index',
    'haystack',
    'positions',
))


def _rank_task(scorer, niddle, haystack, offset):
    result = []
    for index, item in enumerate(haystack):
        score, positions = scorer(niddle, item)
        if positions is None:
            continue
        result.append(RankResult(-score, index + offset, item, positions))
    return result


async def rank(scorer, niddle, haystack, *, executor=None, loop=None):
    """Score haystack against niddle in execturo and return sorted result
    """
    loop = loop or asyncio.get_event_loop()

    batch_size = 1024
    batches = await asyncio.gather(*(
        loop.run_in_executor(
            executor,
            _rank_task,
            scorer,
            niddle,
            haystack[offset:offset + batch_size],
            offset,
        ) for offset in range(0, len(haystack), batch_size)
    ), loop=loop)
    results = [item for batch in batches for item in batch]
    results.sort()

    return results


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


TTYSize = namedtuple('TTYSize', ('height', 'width'))


class TTY:
    __slots__ = (
        'fd', 'size', 'events', 'events_queue', 'loop', 'closed',
        'write_queue', 'write_event', 'write_buffer',
    )
    DEFAULT_FILE = '/dev/tty'

    def __init__(self, file: Union[int, str] = None, *, loop=None) -> None:
        if isinstance(file, int):
            self.fd = file
        else:
            self.fd = os.open(file or self.DEFAULT_FILE, os.O_RDWR)
        assert os.isatty(self.fd), f'file must be a tty: {file}'

        self.loop = asyncio.get_event_loop() if loop is None else loop
        self.size = TTYSize(0, 0)

        def events_queue_handler(event):
            type, _ = event
            if type != TTY_CPR:
                self.events_queue.put_nowait(event)
            return True  # keep subscribed
        self.events = Event()
        self.events_queue = asyncio.Queue()
        self.events.on(events_queue_handler)

        self.write_buffer = io.StringIO()
        self.write_event = Event()
        self.write_queue = deque()

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
            termios.ISIG,
        ))

        try:
            # set tty attributes
            termios.tcsetattr(self.fd, termios.TCSADRAIN, attrs_new)

            # resize handler
            def resize_handler():
                buf = array.array('H', (0, 0, 0, 0))
                if fcntl.ioctl(self.fileno(), termios.TIOCGWINSZ, buf):
                    size = TTYSize(0, 0)
                else:
                    size = TTYSize(buf[0], buf[1])
                self.size = size
                self.events(TTYEvent(TTY_SIZE, size))
            resize_handler()
            self.loop.add_signal_handler(signal.SIGWINCH, resize_handler)

            # reader
            readable = Event()
            parser = TTYParser()
            self.loop.add_reader(self.fd, lambda: readable(None))
            readable.on(partial(self._try_read, parser))

            # writer
            cont_run(self._writer(), name='TTY._writer')

            # wait closed event
            yield cont_from_future(self.closed)
        finally:
            # remove resize handler
            self.loop.remove_signal_handler(signal.SIGWINCH)
            # terminate queue
            self.events_queue.put_nowait(TTYEvent(TTY_CLOSE, None))
            # restore tty attributes
            termios.tcsetattr(self.fd, termios.TCSADRAIN, attrs_old)
            # unregister descriptor
            os.set_blocking(self.fd, True)
            self.write_event(None)
            self.loop.remove_reader(self.fd)
            self.loop.remove_writer(self.fd)
            os.close(self.fd)

    def _try_read(self, parser, _):
        try:
            chunk = os.read(self.fd, 1024)
            if not chunk:
                return False  # unsubsribe
        except BlockingIOError:
            pass
        else:
            events = parser(chunk)
            for event in events:
                self.events(event)
        return True  # keep subscrbied

    def write_sync(self, data: bytes) -> bool:
        blocked = False
        while data:
            try:
                data = data[os.write(self.fd, data):]
            except BlockingIOError:
                blocked = True
        return blocked

    def write(self, input: str) -> None:
        self.write_buffer.write(input)

    def flush(self) -> None:
        frame = self.write_buffer.getvalue()
        self.write_buffer.truncate(0)
        self.write_buffer.seek(0)
        self.write_queue.append(frame)
        self.write_event(None)

    @coro
    def _writer(self):
        wait_queue = cont(self.write_event.on_once)
        wait_writable = cont_finally(
            cont(partial(self.loop.add_writer, self.fd)),
            partial(self.loop.remove_writer, self.fd),
        )
        encode = codecs.getencoder('utf-8')
        while True:
            if not self.write_queue:
                yield wait_queue
                continue
            frame, _ = encode(self.write_queue.popleft())
            if self.write_sync(frame):
                # we were blocked during writing previous frame
                yield wait_writable
                if self.write_queue:
                    # removing all but last frame, assuming flush is called
                    # on whole frame barrier.
                    frame_last = self.write_queue.pop()
                    self.write_queue.clear()
                    self.write_queue.append(frame_last)

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

    def fileno(self) -> int:
        return self.fd

    def autowrap_set(self, enable):
        if enable:
            self.write('\033[?7h')
        else:
            self.write('\033[?7l')

    def cursor_to(self, row=0, column=0):
        self.write(f'\x1b[{row};{column}H')

    def cursor_up(self, count: int) -> None:
        if count == 0:
            pass
        elif count == 1:
            self.write('\x1b[A')
        elif count > 1:
            self.write(f'\x1b[{count}A')
        else:
            self.cursor_down(-count)

    def cursor_down(self, count: int) -> None:
        if count == 0:
            pass
        elif count == 1:
            self.write('\x1b[B')
        elif count > 1:
            self.write(f'\x1b[{count}B')
        else:
            self.cursor_up(-count)

    def cursor_to_column(self, index: int) -> None:
        if index == 0:
            self.write('\x1b[G')
        elif index > 1:
            self.write(f'\x1b[{index}G')
        else:
            raise ValueError(f'column index can not be negative: {index}')

    def cursor_forward(self, count: int) -> None:
        if count == 0:
            pass
        elif count == 1:
            self.write('\x1b[C')
        elif count > 1:
            self.write(f'\x1b[{count}C')
        else:
            self.cursor_backward(-count)

    def cursor_backward(self, count: int) -> None:
        if count == 0:
            pass
        elif count == 1:
            self.write('\x1b[D')
        elif count > 1:
            self.write(f'\x1b[{count}D')
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

        self.write_sync(b'\x1b[6n')
        return await cpr

    def cursor_hide(self):
        self.write('\x1b[?25l')

    def cursor_show(self):
        self.write('\x1b[?12l\x1b[?25h')

    def erase_line(self) -> None:
        self.write('\x1b[K')

    def erase_down(self):
        self.write('\x1b[J')


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
FACE_RENDER_CACHE = {}
FACE_OVERLAY_CACHE = {}


class Face(tuple):
    __slots__ = tuple()

    def __new__(cls, fg=None, bg=None, attrs=FACE_NONE):
        return tuple.__new__(cls, (fg, bg, attrs))

    def overlay(self, other):
        face = FACE_OVERLAY_CACHE.get((self, other))
        if face is None:
            fg0, bg0, attrs0 = self
            fg1, bg1, attrs1 = other
            bg01 = bg1 if bg0 is None else bg0.overlay(bg1)
            fg01 = fg1 if fg0 is None else fg0.overlay(fg1)
            if fg01 is not None:
                fg01 = fg01 if bg01 is None else bg01.overlay(fg01)
            face = Face(fg01, bg01, attrs0 | attrs1)
            FACE_OVERLAY_CACHE[(self, other)] = face
        return face

    def invert(self):
        fg, bg, attrs = self
        return Face(bg, fg, attrs)

    fg = property(lambda self: self[0])
    bg = property(lambda self: self[1])
    attrs = property(lambda self: self[2])

    def render(self, stream):
        seq = FACE_RENDER_CACHE.get(self)
        if seq is None:
            fg, bg, attrs = self
            buf = ['\x1b[m\x1b[']
            if attrs:
                for attr, code in FACE_MAP:
                    if attrs & attr:
                        buf.append(code)
            if fg:
                buf.append('38;2;{};{};{};'.format(
                    *(int(c * 255) for c in fg[:3])))
            if bg:
                buf.append('48;2;{};{};{};'.format(
                    *(int(c * 255) for c in bg[:3])))
            buf.append('m')
            seq = ''.join(buf)
            FACE_RENDER_CACHE[self] = seq
        stream.write(seq)

    def __repr__(self):
        stream = io.StringIO()
        self.render(stream)
        return f'Face({stream.getvalue()} X \x1b[m)'


class Text:
    """Formated text (string with associated faces)
    """
    __slots__ = ('_chunks', '_len',)

    def __init__(self, chunks):
        if isinstance(chunks, str):
            chunks = [(chunks, Face())]
        self._chunks = chunks
        self._len = None

    def __len__(self):
        if self._len is None:
            self._len = sum(len(c) for c, _ in self._chunks)
        return self._len

    def __bool__(self):
        return bool(self._chunks)

    def __add__(self, other):
        return Text(self._chunks + other._chunks)

    def mark(self, face, start=None, stop=None):
        start = 0 if start is None else (start if start >= 0 else len(self) + start)
        stop = len(self) if stop is None else (stop if stop >= 0 else len(self) + stop)
        left, mid = self.split(start)
        mid, right = mid.split(stop - start)
        chunks = []
        chunks.extend(left._chunks)
        for c_text, c_face in mid._chunks:
            chunks.append((c_text, c_face.overlay(face)))
        chunks.extend(right._chunks)
        return Text(chunks)

    def mark_mask(self, face, mask):
        if not mask:
            return self
        # collect ranges
        ranges = []
        start, *mask = sorted(mask)
        offset, stop = 0, start + 1
        for index in mask:
            if index == stop:
                stop += 1
            else:
                ranges.append((start - offset, stop - start))
                offset = stop
                start, stop = index, index + 1
        ranges.append((start - offset, stop - start))

        chunks, text = [], self
        for offset, size in ranges:
            left, mid = text.split(offset)
            mid, text = mid.split(size)
            chunks.extend(left._chunks)
            for c_text, c_face in mid._chunks:
                chunks.append((c_text, c_face.overlay(face)))
        chunks.extend(text._chunks)
        return Text(chunks)

    def split(self, index):
        index = index if index >= 0 else len(self) + index
        lefts, rights = [], []
        for chunk_index, (text, face) in enumerate(self._chunks):
            chunk_len = len(text)
            if chunk_len < index:
                index -= chunk_len
                lefts.append((text, face))
            elif chunk_len == index:
                lefts.append((text, face))
                rights.extend(self._chunks[chunk_index + 1:])
                break
            else:
                left, right = text[:index], text[index:]
                if left:
                    lefts.append((left, face))
                if right:
                    rights.append((right, face))
                rights.extend(self._chunks[chunk_index + 1:])
                break
        return Text(lefts), Text(rights)

    def __getitem__(self, selector):
        if isinstance(selector, slice):
            start, stop = selector.start, selector.stop
            assert selector.step != 1, 'slice step is not supported'
            start = 0 if start is None else (start if start >= 0 else len(self) + start)
            stop = len(self) if stop is None else (stop if stop >= 0 else len(self) + stop)
            _, result = self.split(start)
            result, _ = result.split(stop - start)
            return result
        elif isinstance(selector, int):
            return self[selector:selector + 1]
        else:
            raise ValueError('text indices must be integers')

    def render(self, stream, face=Face()):
        p_face = face
        for c_text, c_face in self._chunks:
            c_face = face.overlay(c_face)
            if c_face != p_face:
                c_face.render(stream)
                p_face = c_face
            stream.write(c_text)
        face.render(stream)

    def __str__(self):
        stream = io.StringIO()
        stream.write('Text(\'')
        self.render(stream)
        stream.write('\')')
        return stream.getvalue()

    def __repr__(self):
        return str(self)


# ------------------------------------------------------------------------------
# Selector
# -----------------------------------------------------------------------------
THEME_DEFAULT = {
    'prompt': Face(bg=Color('#458588')),
    'match': Face(bg=Color('#d65d0e')),
    'list-selected': Face(bg=Color('#3c3836')),
    'list-default': Face(bg=Color('#282828')),
    'list-scrollbar-on': Face(bg=Color('#458588').with_alpha(.8)),
    'list-scrollbar-off': Face(bg=Color('#458588').with_alpha(.4)),
}


def get_face(name, theme=None):
    """Get face with specified name from theme
    """
    if theme is None:
        theme = THEME_DEFAULT
    return theme.get(name) or THEME_DEFAULT[name]


class InputWidget:
    __slots__ = ('buffer', 'cursor', 'update', 'prefix', 'suffix')

    def __init__(self, buffer=None, cursor=None):
        self.buffer = [] if buffer is None else list(buffer)
        self.cursor = len(self.buffer) if cursor is None else cursor
        self.prefix = Text('')
        self.suffix = Text('')
        self.update = Event()

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
                        self.update(self.buffer)
                elif name == 'k':
                    del self.buffer[self.cursor:]
                    self.update(self.buffer)
        elif type == TTY_CHAR:
            self.buffer.insert(self.cursor, attrs)
            self.update(self.buffer)
            self.cursor += 1

    def set_prefix(self, prefix):
        self.prefix = prefix

    def set_suffix(self, suffix):
        self.suffix = suffix

    def render(self, tty):
        tty.erase_line()
        self.prefix.render(tty)
        tty.write(''.join(self.buffer))
        tty.cursor_to_column(tty.size.width - len(self.suffix) + 1)
        self.suffix.render(tty)
        tty.cursor_to_column(len(self.prefix) + self.cursor + 1)


class ListWidget:
    __slots__ = ('items', 'render_item', 'height', 'offset', 'cursor', 'theme',)

    def __init__(self, items, render_item, height, theme=None):
        self.items = items
        self.cursor = 0
        self.offset = 0
        self.height = height
        self.render_item = render_item
        self.theme = None

    def __call__(self, event):
        type, attrs = event
        if type == TTY_KEY:
            name, mode = attrs
            if name == 'up':
                self.move(-1)
            elif name == 'pageup':
                self.move(-self.height)
            elif name == 'down':
                self.move(1)
            elif name == 'pagedown':
                self.move(self.height)
            elif mode & KEY_MODE_CTRL:
                if name == 'p':
                    self.move(-1)
                elif name == 'n':
                    self.move(1)

    @property
    def selected(self):
        current = self.offset + self.cursor
        if current < len(self.items):
            return self.items[current]
        else:
            return None

    def move(self, count):
        if count < 0:
            count = -count
            self.cursor -= count
            if self.cursor < 0:
                self.offset += self.cursor
                self.cursor = 0
                if self.offset < 0:
                    self.offset = 0
        else:
            self.cursor += count
            if self.offset + self.cursor < len(self.items):
                if self.cursor >= self.height:
                    self.offset += self.cursor - self.height + 1
                    self.cursor = self.height - 1
            else:
                if self.cursor >= len(self.items):
                    self.offset, self.cursor = 0, len(self.items) - 1
                else:
                    self.cursor = self.height - 1
                    self.offset = len(self.items) - self.cursor - 1

    def reset(self, items):
        self.cursor = 0
        self.offset = 0
        self.items = items

    def render(self, tty):
        face_selected = get_face('list-selected', self.theme)
        face_default = get_face('list-default', self.theme)
        face_scrollbar_on = get_face('list-scrollbar-on', self.theme)
        face_scrollbar_off = get_face('list-scrollbar-off', self.theme)

        # scroll bar
        scrollbar = [False] * self.height
        if self.items:
            filled = max(1, min(self.height, self.height ** 2 // len(self.items)))
            empty = round((self.height - filled) * (self.offset + self.cursor) / len(self.items))
            for fill in range(empty, empty + filled):
                scrollbar[fill] = True

        # lines
        width = tty.size.width
        for line in range(self.height):
            # pointer
            if line == self.cursor:
                face = face_selected
                face.render(tty)
                tty.write(' \u25cf ')
            else:
                face = face_default
                face.render(tty)
                tty.write('   ')
            # text
            index = self.offset + line
            if index < len(self.items):
                self.render_item(tty, width - 4, face, self.items[index])
            tty.erase_line()  # will fill with current color
            # scroll bar
            tty.cursor_to_column(width)
            if scrollbar[line]:
                face.overlay(face_scrollbar_on).render(tty)
            else:
                face.overlay(face_scrollbar_off).render(tty)
            tty.write(' ')
            # next line
            tty.cursor_to_column(0)
            tty.cursor_down(1)
        tty.write('\x1b[m')


async def selector(
    items,
    *,
    prompt=None,
    tty=None,
    executor=None,
    loop=None,
    theme=None
):
    loop = loop or asyncio.get_event_loop()
    prompt = prompt or 'input'

    face_prompt = get_face('prompt', theme)
    face_match = get_face('match', theme)

    def render_item(tty, width, face, item):
        text = Text(item.haystack)
        text.mark_mask(face_match, item.positions)[:width].render(tty, face)

    prefix = reduce(op.add, (
        Text(f' {prompt} ').mark(face_prompt),
        Text('\ue0b0 ').mark(face_prompt.invert()),
    ))
    input = InputWidget()
    input.set_prefix(prefix)
    table = ListWidget([], render_item, 10, theme)

    async def table_update_coro(niddle):
        niddle = ''.join(niddle)
        start = time.time()
        result = await rank(
            fuzzy_scorer,
            niddle,
            items,
            loop=loop,
            executor=executor,
        )
        stop = time.time()
        input.set_suffix(
            Text(' \ue0b2').mark(face_prompt.invert()) +
            Text(
                f' {len(result)}/{len(items)} {stop - start:.2f}s '
            ).mark(face_prompt)
        )
        table.reset(result)
        render()

    def table_update(niddle):
        nonlocal table_update_task
        table_update_task.cancel()
        table_update_task = asyncio.ensure_future(
            table_update_coro(niddle))
        return True
    table_update_task = loop.create_future()
    input.update.on(table_update)

    def render():
        tty.cursor_to(line, column)
        tty.erase_down()
        # show table
        tty.cursor_to(line + 1, column)
        table.render(tty)
        # show input
        tty.cursor_to(line, column)
        input.render(tty)
        # flush output
        tty.flush()

    with ExitStack() as stack:
        tty = tty or stack.enter_context(TTY(loop=loop))
        executor = executor or stack.enter_context(
            ProcessPoolExecutor(max_workers=5))

        tty.autowrap_set(False)

        # reserve space (force scroll)
        tty.write('\n' * table.height)
        tty.cursor_up(table.height)
        tty.flush()

        line, column = await tty.cursor_cpr()
        table_update('')

        result = -1
        async for event in tty:
            type, attrs = event
            if type == TTY_KEY:
                name, mode = attrs
                if name in 'cd':
                    break
                if name == 'm':
                    selected = table.selected
                    result = -1 if selected is None else selected.index
                    break
            input(event)
            table(event)
            render()

        tty.cursor_to(line, column)
        tty.erase_down()
        tty.autowrap_set(True)
        tty.flush()
        table_update_task.cancel()

        return result


# ------------------------------------------------------------------------------
# Entry Point
# ------------------------------------------------------------------------------
def main() -> None:
    import argparse
    import logging

    parser = argparse.ArgumentParser()
    parser.add_argument(
        '-d', '--debug',
        action='store_true',
        help='enable debugging',
    )
    parser.add_argument(
        '-r', '--reversed',
        action='store_true',
        help='reverse order of items',
    )
    parser.add_argument(
        '-k', '--show-key',
        action='store_true',
        help='show last pressed key',
    )
    parser.add_argument(
        '-p', '--prompt',
        default='input',
        help='override prompt string',
    )
    options = parser.parse_args()

    if sys.platform in ('darwin',):
        # kqueue does not support devices
        import selectors
        asyncio.set_event_loop(
            asyncio.SelectorEventLoop(selectors.SelectSelector()))
    loop = asyncio.get_event_loop()
    if options.debug:
        loop.set_debug(True)
        logging.getLogger('asyncio').setLevel(logging.INFO)

    items = [line.rstrip('\n') for line in sys.stdin.readlines()]
    if options.reversed:
        items = items[::-1]
    try:
        with ExitStack() as stack:
            tty = stack.enter_context(TTY(loop=loop))
            executor = stack.enter_context(ProcessPoolExecutor(max_workers=5))

            if options.show_key:
                def show_key(event):
                    key = Text(str(event)).mark(face_key)
                    tty.cursor_to(0, 0)
                    key.render(tty)
                    tty.erase_line()
                    return True
                face_key = Face(bg=Color('#cc241d'), fg=Color('#ebdbb2'))
                tty.events.on(show_key)

            selected = loop.run_until_complete(selector(
                items,
                prompt=options.prompt,
                loop=loop,
                tty=tty,
                executor=executor,
            ))
        if selected >= 0:
            print(items[selected])
    finally:
        loop.run_until_complete(loop.shutdown_asyncgens())
        loop.close()


if __name__ == '__main__':
    main()
