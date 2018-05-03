#!/usr/bin/env python
"""Sweep is a command line fuzzy finer (fzf analog)

TODO:
  - use something instead of future in closer coro as it fails to complete
    if loop is not running
  - validate that loop is not `kqueue` based
  - use lighter queues?
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
    Iterable,
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
        return Pattern(
            table,
            {f: cb for fs in finals for f, cb in fs.items()},
            epsilons,
        )

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
            """Epsilon closure (reachable with epsilon move) of set of states
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
                    (d_finals
                     .setdefault(d_state, [])
                     .append(self.finals[n_state]))
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
            return SCORE_MAX, list(range(n))
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
        score, positions = scorer(niddle, str(item))
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

    return Pattern.choice(patterns)


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
                        sys.stderr.write('[ERROR] failed to process: {}\n'
                                         .format(bytes(unconsumed)))
                        self._parse(None)
            else:
                # all consumed (no break in for loop)
                break
        return keys


TTYSize = namedtuple('TTYSize', ('height', 'width'))


class TTY:
    __slots__ = (
        'fd', 'size', 'loop', 'closed', 'color_depth',
        'events', 'events_queue',
        'write_queue', 'write_event', 'write_buffer', 'write_count',
    )
    DEFAULT_FILE = '/dev/tty'

    def __init__(self, *, file=None, loop=None, color_depth=None):
        if isinstance(file, int):
            self.fd = file
        else:
            self.fd = os.open(file or self.DEFAULT_FILE, os.O_RDWR)
        assert os.isatty(self.fd), f'file must be a tty: {file}'

        self.loop = asyncio.get_event_loop() if loop is None else loop
        self.color_depth = color_depth
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
        self.write_count = 0

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
            self.write_count += 1
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
        """Current cursor possition
        """
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
COLOR_DEPTH_24 = 1
COLOR_DEPTH_8 = 2
COLOR_DEPTH_4 = 3


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

    def hex(self):
        r, g, b, a = self
        return '#{:02x}{:02x}{:02x}{}'.format(
            int(r * 255),
            int(g * 255),
            int(b * 255),
            f'{int(a * 255):02x}' if a != 1 else '',
        )

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
        fg = ';38;5;231' if self.luma < .5 else ';38;5;232'
        return f'Color(\x1b[00{fg}{self.sgr(False)}m{self.hex()}\x1b[m)'

    def sgr(self, is_fg, depth=None):
        """Return part of SGR sequence responsible for picking this color
        """
        depth = depth or COLOR_DEPTH_24
        r, g, b, _ = self

        if depth == COLOR_DEPTH_24:
            p = ';38' if is_fg else ';48'
            return f'{p};2;{int(r * 255)};{int(g * 255)};{int(b * 255)}'

        elif depth == COLOR_DEPTH_8:
            def l2(lr, lg, lb, rr, rg, rb):
                return (lr - rr) ** 2 + (lg - rg) ** 2 + (lb - rb) ** 2

            # quantized color
            def v2q(value):
                if value < .1882:  # 48 / 255
                    return 0
                elif value < .4471:  # 114 / 255
                    return 1
                else:
                    return int((value * 255.0 - 35.0) / 40.0)
            # value range for color cupe [0x00, 0x5f, 0x87, 0xaf, 0xd7, 0xff]
            q2v = (0.0, 0.3725, 0.5294, 0.6863, 0.8431, 1.0)
            qr, qg, qb = v2q(r), v2q(g), v2q(b)
            cr, cg, cb = q2v[qr], q2v[qg], q2v[qb]

            # grayscale color
            c = (r + g + b) / 3
            gi = 23 if c > .9333 else int((c * 255 - 3) / 10)
            gv = (8 + 10 * gi) / 255.0

            # determine if gray is closer then quantized color
            if l2(cr, cg, cb, r, g, b) > l2(gv, gv, gv, r, g, b):
                i = 232 + gi
            else:
                i = 16 + 36 * qr + 6 * qg + qb
            p = ';38' if is_fg else ';48'
            return f'{p};5;{i}'

        elif depth == COLOR_DEPTH_4:
            def l2(lr, lg, lb, rr, rg, rb):
                return (lr - rr) ** 2 + (lg - rg) ** 2 + (lb - rb) ** 2

            best_fg, best_bg, min_d = None, None, 4
            for fg, bg, cr, cg, cb in (
                (';30', ';40', 0, 0, 0),
                (';31', ';41', .5, 0, 0),
                (';32', ';42', 0, .5, 0),
                (';33', ';43', .5, .5, 0),
                (';34', ';44', 0, 0, .5),
                (';35', ';45', .5, 0, .5),
                (';36', ';46', 0, .5, .5),
                (';37', ';47', 0.75, 0.75, 0.75),
                (';90', ';100', 0.5, 0.5, 0.5),
                (';91', ';101', 1, 0, 0),
                (';92', ';102', 0, 1, 0),
                (';93', ';103', 1, 1, 0),
                (';94', ';104', 0, 0, 1),
                (';95', ';105', 1, 0, 1),
                (';96', ';106', 0, 1, 1),
                (';97', ';107', 1, 1, 1),
            ):
                d = l2(r, g, b, cr, cg, cb)
                if d < min_d:
                    best_fg, best_bg, min_d = fg, bg, d
            return best_fg if is_fg else best_bg


FACE_NONE = 0
FACE_BOLD = 1 << 1
FACE_ITALIC = 1 << 2
FACE_UNDERLINE = 1 << 3
FACE_BLINK = 1 << 4
FACE_REVERSE = 1 << 5
FACE_MAP = (
    (FACE_BOLD, ';01'),
    (FACE_ITALIC, ';03'),
    (FACE_UNDERLINE, ';04'),
    (FACE_BLINK, ';05'),
    (FACE_REVERSE, ';07'),
)
FACE_RENDER_CACHE = {}
FACE_OVERLAY_CACHE = {}


class Face(tuple):
    __slots__ = tuple()

    def __new__(cls, fg=None, bg=None, attrs=FACE_NONE):
        return tuple.__new__(cls, (fg, bg, attrs))

    fg = property(lambda self: self[0])
    bg = property(lambda self: self[1])
    attrs = property(lambda self: self[2])

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

    def with_fg_contrast(self, fg0, fg1):
        _, bg, attrs = self
        fg_light, fg_dark = (fg0, fg1) if fg0.luma > fg1.luma else (fg1, fg0)
        fg = bg.overlay(fg_light if bg.luma < .5 else fg_dark)
        return Face(fg, bg, attrs)

    def render(self, stream):
        seq = FACE_RENDER_CACHE.get(self)
        if seq is None:
            fg, bg, attrs = self
            buf = ['\x1b[00']  # first reset previous SGR settings
            if attrs:
                for attr, code in FACE_MAP:
                    if attrs & attr:
                        buf.append(code)
            depth = getattr(stream, 'color_depth', None)
            if fg is not None:
                buf.append(fg.sgr(True, depth))
            if bg is not None:
                buf.append(bg.sgr(False, depth))
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
        start = 0 if start is None else (
            start if start >= 0 else len(self) + start)
        stop = len(self) if stop is None else (
            stop if stop >= 0 else len(self) + stop)
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

    def join(self, texts):
        texts = list(texts)
        chunks = []
        index_last = len(texts) - 1
        for index, text in enumerate(texts):
            chunks.extend(text._chunks)
            if index != index_last:
                chunks.extend(self._chunks)
        return Text(chunks)

    def __getitem__(self, selector):
        if isinstance(selector, slice):
            start, stop = selector.start, selector.stop
            assert selector.step != 1, 'slice step is not supported'
            start = 0 if start is None else (
                start if start >= 0 else len(self) + start)
            stop = len(self) if stop is None else (
                stop if stop >= 0 else len(self) + stop)
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
# Widgets
# ------------------------------------------------------------------------------
def Theme(base, match, fg, bg):
    base = Color(base)
    match = Color(match)
    fg = Color(fg)
    bg = Color(bg)
    theme_dict = {
        'base_bg': Face(bg=base).with_fg_contrast(fg, bg),
        'base_fg': Face(fg=base, bg=bg),
        'match': Face(bg=match).with_fg_contrast(fg, bg),
        'input_default': Face(fg=fg, bg=bg),
        'list_dot': Face(fg=base),
        'list_selected': Face(
            fg=bg.overlay(fg.with_alpha(.9)),
            bg=bg.overlay(fg.with_alpha(.055)),
        ),
        'list_default': Face(fg=bg.overlay(fg.with_alpha(.9)), bg=bg),
        'list_scrollbar_on': Face(bg=base.with_alpha(.8)),
        'list_scrollbar_off': Face(bg=base.with_alpha(.4)),
        'candidate_active': Face(fg=bg.overlay(fg.with_alpha(.9))),
        'candidate_inactive': Face(fg=bg.overlay(fg.with_alpha(.4))),
    }
    return type('Theme', tuple(), theme_dict)()


THEME_LIGHT_ATTRS = dict(
    base='#076678', match='#af3a03', fg='#3c3836', bg='#fbf1c7')
THEME_DARK_ATTRS = dict(
    base='#458588', match='#fe8019', fg='#ebdbb2', bg='#282828')
THEME_DEFAULT = Theme(**THEME_DARK_ATTRS)


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

    def render(self, tty, theme=None):
        theme = theme or THEME_DEFAULT
        face = theme.input_default
        face.render(tty)
        tty.erase_line()
        self.prefix.render(tty, face)
        face.render(tty)
        tty.write(''.join(self.buffer))
        tty.cursor_to_column(tty.size.width - len(self.suffix) + 1)
        self.suffix.render(tty, face)
        tty.cursor_to_column(len(self.prefix) + self.cursor + 1)


class ListWidget:
    __slots__ = ('items', 'height', 'offset', 'cursor', 'item_to_text',)

    def __init__(self, items, height, item_to_text):
        self.items = items
        self.cursor = 0
        self.offset = 0
        self.height = height
        self.item_to_text = item_to_text

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

    def render(self, tty, theme=None):
        theme = theme or THEME_DEFAULT
        face_selected = theme.list_selected
        face_default = theme.list_default
        face_scrollbar_on = theme.list_scrollbar_on
        face_scrollbar_off = theme.list_scrollbar_off
        face_dot = theme.list_dot

        # scroll bar
        scrollbar = [False] * self.height
        if self.items:
            items_len = len(self.items)
            filled = max(1, min(self.height, self.height ** 2 // items_len))
            empty = round((self.height - filled) * (self.offset + self.cursor)
                          / items_len)
            for fill in range(empty, empty + filled):
                scrollbar[fill] = True

        # lines
        width = tty.size.width
        for line in range(self.height):
            # pointer
            if line == self.cursor:
                face = face_selected
                face.render(tty)
                Text(' \u25cf ').mark(face_dot).render(tty, face)
            else:
                face = face_default
                face.render(tty)
                tty.write('   ')
            # text
            index = self.offset + line
            if index < len(self.items):
                (self
                 .item_to_text(self.items[index])[:width - 4]
                 .render(tty, face))
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


# ------------------------------------------------------------------------------
# Select
# ------------------------------------------------------------------------------
class Candidate(tuple):
    def __new__(cls, fields, positions=None):
        return tuple.__new__(cls, (fields, positions))

    @classmethod
    def from_str(cls, string, delimiter=None, predicate=None):
        if delimiter is None or predicate is None:
            return cls(((string, True),))

        offset, fields = 0, []
        for match in re.finditer(delimiter, string):
            if match.start() == 0:
                continue
            end = match.end()
            fields.append(string[offset:end])
            offset = end
        if offset < len(string):
            fields.append(string[offset:])

        return cls(tuple((field, predicate(index))
                         for index, field in enumerate(fields)))

    def to_str(self):
        fields, _ = self
        return ''.join(field for field, _ in fields)

    def to_text(self, theme=None):
        fields, positions = self
        theme = theme or THEME_DEFAULT

        face_active = theme.candidate_active
        face_inactive = theme.candidate_inactive

        text = Text('').join(
            Text(field).mark(face_active if active else face_inactive)
            for field, active in fields
        )
        return text.mark_mask(theme.match, positions)

    def with_positions(self, positions):
        fields, _ = self

        positions_rev = list(reversed(positions)) if positions else []
        positions = []
        offset, size = 0, 0
        for field, active in fields:
            if active:
                size += len(field)
                while positions_rev and positions_rev[-1] < size + offset:
                    positions.append(positions_rev.pop() + offset)
            else:
                offset += len(field)
        return Candidate(fields, positions)

    def __str__(self):
        """Used in ranker to produce candidate string
        """
        fields, _ = self
        return ''.join(field for field, active in fields if active)

    def __repr__(self):
        stream = io.StringIO()
        self.to_text().render(stream)
        return f'Candidate(\'{stream.getvalue()}\')'

    def __reduce__(self):
        return Candidate, tuple(self)


async def select(
    candidates,
    *,
    height=None,
    prompt=None,
    tty=None,
    executor=None,
    loop=None,
    theme=None,
):
    """Show text UI to select candidate

    Candidates can be either strings or `Candidate` objects.
    """
    prompt = prompt or 'input'
    height = height or 10
    theme = theme or THEME_DEFAULT
    loop = loop or asyncio.get_event_loop()

    face_base_fg = theme.base_fg
    face_base_bg = theme.base_bg
    face_match = theme.match

    def item_to_text(item):
        if isinstance(item.haystack, Candidate):
            return item.haystack.with_positions(item.positions).to_text(theme)
        else:
            return Text(item.haystack).mark_mask(face_match, item.positions)

    prefix = reduce(op.add, (
        Text(f' {prompt} ').mark(face_base_bg),
        Text('\ue0b0 ').mark(face_base_fg),
    ))
    input = InputWidget()
    input.set_prefix(prefix)
    table = ListWidget([], height, item_to_text)

    async def table_update_coro(niddle):
        niddle = ''.join(niddle)
        start = time.time()
        result = await rank(
            fuzzy_scorer,
            niddle,
            candidates,
            loop=loop,
            executor=executor,
        )
        stop = time.time()
        input.set_suffix(
            Text(' \ue0b2').mark(face_base_fg) +
            Text(
                f' {len(result)}/{len(candidates)} {stop - start:.2f}s '
            ).mark(face_base_bg)
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
        tty.write('\x1b[00m')
        tty.erase_down()
        # show table
        tty.cursor_to(line + 1, column)
        table.render(tty, theme)
        # show input
        tty.cursor_to(line, column)
        input.render(tty, theme)
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
        tty.write('\x1b[00m')
        tty.erase_down()
        tty.autowrap_set(True)
        tty.flush()
        table_update_task.cancel()

        return result


# ------------------------------------------------------------------------------
# Entry Point
# ------------------------------------------------------------------------------
def main_options():
    import argparse
    import textwrap

    def parse_nth(argument):
        def predicate(low, high):
            if low is not None and high is not None:
                return lambda index: low <= index <= high
            elif low is not None:
                return lambda index: index >= low
            elif high is not None:
                return lambda index: index <= high
            else:
                return lambda _: True

        def predicate_field(index):
            return index in fields

        fields = set()
        predicates = [predicate_field]
        for field in argument.split(','):
            field = field.split('..')
            if len(field) == 1:
                fields.add(int(field[0]) - 1)
            elif len(field) == 2:
                low, high = field
                predicates.append(predicate(
                    int(low) - 1 if low else None,
                    int(high) - 1 if high else None,
                ))
            else:
                raise argparse.ArgumentTypeError(
                    f'invalid predicate: {"..".join(fields)}')

        return lambda index: any(predicate(index) for predicate in predicates)

    def parse_color_depth(argument):
        depths = {
            '24': COLOR_DEPTH_24,
            '8': COLOR_DEPTH_8,
            '4': COLOR_DEPTH_4,
        }
        depth = depths.get(argument)
        if depth is None:
            raise argparse.ArgumentTypeError(
                f'invalid depth: {argument} (allowed [{",".join(depths)}])')
        return depth

    def parse_theme(argument):
        attrs = dict(THEME_DARK_ATTRS)
        for attr in argument.lower().split(','):
            if attr == 'light':
                attrs.update(THEME_LIGHT_ATTRS)
            elif attr == 'dark':
                attrs.update(THEME_DARK_ATTRS)
            else:
                key, value = attr.split('=')
                attrs[key] = value.strip('"\'')
        return Theme(**attrs)

    parser = argparse.ArgumentParser(description=textwrap.dedent("""\
    Sweep is a command line fuzzy finer (fzf analog)
    """))
    parser.add_argument(
        '-p', '--prompt',
        default='input',
        help='override prompt string',
    )
    parser.add_argument(
        '-r', '--reversed',
        action='store_true',
        help='reverse order of items',
    )
    parser.add_argument(
        '-n', '--nth',
        type=parse_nth,
        help='comma-separated list of for limiting search scope',
    )
    parser.add_argument(
        '-d', '--delimiter',
        type=re.compile,
        default=re.compile('[ \t]+'),
        help='field delimiter regular expression',
    )
    parser.add_argument(
        '--theme',
        type=parse_theme,
        default=THEME_DEFAULT,
        help='specify theme as a list of comma sperated attributes',
    )
    parser.add_argument(
        '--color-depth',
        type=parse_color_depth,
        default=COLOR_DEPTH_24,
        help='color depth',
    )
    parser.add_argument(
        '--debug',
        action='store_true',
        help='enable debugging',
    )
    return parser.parse_args()


def main() -> None:
    options = main_options()

    # `kqueue` does not support tty, fallback to `select`
    if sys.platform in ('darwin',):
        import selectors
        asyncio.set_event_loop(
            asyncio.SelectorEventLoop(selectors.SelectSelector()))

    loop = asyncio.get_event_loop()
    if options.debug:
        import logging
        loop.set_debug(True)
        logging.getLogger('asyncio').setLevel(logging.INFO)

    candidates = [Candidate.from_str(
        line.rstrip(),
        delimiter=options.delimiter,
        predicate=options.nth,
    ) for line in sys.stdin.readlines()]
    if options.reversed:
        candidates = candidates[::-1]

    try:
        with ExitStack() as stack:
            executor = stack.enter_context(ProcessPoolExecutor(max_workers=5))
            tty = stack.enter_context(TTY(
                loop=loop,
                color_depth=options.color_depth,
            ))

            if options.debug:
                def debug_label(event):
                    label = ' '.join((
                        '',
                        f'event: {event}',
                        f'write_count: {tty.write_count}',
                        '',
                    ))
                    tty.cursor_to(0, 0)
                    Text(label).mark(face_key).render(tty)
                    tty.erase_line()
                    return True
                face_key = Face(bg=Color('#cc241d'), fg=Color('#ebdbb2'))
                tty.events.on(debug_label)

            selected = loop.run_until_complete(select(
                candidates,
                prompt=options.prompt,
                loop=loop,
                tty=tty,
                executor=executor,
                theme=options.theme,
            ))
        if selected >= 0:
            print(candidates[selected].to_str())
    finally:
        loop.run_until_complete(loop.shutdown_asyncgens())
        loop.close()


if __name__ == '__main__':
    main()
