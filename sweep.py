#!/usr/bin/env python3
"""Sweep is a command line fuzzy finer (fzf analog)
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

from typing import Iterable


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
            sys.stderr.write(f"\x1b[31;01m{repr(error)}\x1b[m\n")
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
        assert all(
            -1 <= s < len(table) for ss in table for s in ss.values()
        ), f"invalid transition state found: {table}"
        assert all(
            -1 <= s <= len(table) for s in finals
        ), f"invalid final state found: {finals}"

        self.table = table
        self.finals = finals
        self.epsilons = epsilons or {}

    def check(self, string):
        if not string:
            return
        if isinstance(string, str):
            string = string.encode()
        matcher = self()
        matcher(None)
        for i, c in enumerate(string):
            alive, results, unconsumed = matcher(c)
            if not alive:
                break
        unconsumed.extend(string[i + 1 :])
        return alive, results, unconsumed

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
            elif fs is not None:
                results.append(buffer)
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
        assert len(patterns) > 0, "pattern set must be non empyt"
        table, starts, finals, epsilons = cls._merge(patterns, table=[{}])
        epsilons[0] = set(starts)
        return Pattern(
            table, {f: cb for fs in finals for f, cb in fs.items()}, epsilons
        )

    def __or__(self, other):
        return self.choice((self, other))

    @classmethod
    def sequence(cls, patterns):
        assert len(patterns) > 0, "patterns set must be non empyt"
        table, starts, finals, epsilons = cls._merge(patterns)

        for s, fs in zip(starts[1:], finals):
            for f, cb in fs.items():
                assert not cb, "only last pattern can have callback"
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
            finals.append({final + offset: cb for final, cb in pattern.finals.items()})

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
                    (d_finals.setdefault(d_state, []).append(self.finals[n_state]))
            # transitions
            n_trans = [self.table[n_state] for n_state in d_state]
            d_tran = {}
            for i in {i for n_tran in n_trans for i in n_tran}:
                d_state_new = epsilon_closure(
                    {n_tran[i] for n_tran in n_trans if i in n_tran}
                )
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
            {i: d_ss_sn[ss] for i, ss in d_table[d_sn_ss[sn]].items()} for sn in d_sn_ss
        ]
        d_finals_norm = {
            d_ss_sn[ss]: tuple(it.chain.from_iterable(cb))
            for ss, cb in d_finals.items()
        }

        return Pattern(d_table_norm, d_finals_norm)

    def show(self, render=True, size=384):
        from graphviz import Digraph

        dot = Digraph(format="png")
        dot.graph_attr["rankdir"] = "LR"

        for state in range(len(self.table)):
            attrs = {"shape": "circle"}
            if state in self.finals:
                attrs["shape"] = "doublecircle"
            dot.node(str(state), **attrs)

        edges = {}
        for state, row in enumerate(self.table):
            for input, state_new in row.items():
                edges.setdefault((state, state_new), []).append(chr(input))
        for (src, dst), inputs in edges.items():
            dot.edge(str(src), str(dst), label="".join(inputs))

        for epsilon_out, epsilon_ins in self.epsilons.items():
            for epsilon_in in epsilon_ins:
                dot.edge(str(epsilon_out), str(epsilon_in), color="red")

        if sys.platform == "darwin" and os.environ["TERM"] and render:
            import base64

            iterm_format = "\x1b]1337;File=inline=1;width={width}px:{data}\a\n"
            with open(dot.render(), "rb") as file:
                sys.stdout.write(
                    iterm_format.format(
                        width=size, data=base64.b64encode(file.read()).decode()
                    )
                )
        else:
            return dot


def p_byte(b):
    assert 0 <= b <= 255, f"byte expected: {b}"
    return Pattern([{b: 1}, {}], {1: tuple()})


def p_byte_pred(pred):
    return Pattern([{b: 1 for b in range(256) if pred(b)}, {}], {1: tuple()})


@apply
def p_utf8():
    printable_set = set(
        ord(c)
        for c in (string.ascii_letters + string.digits + string.punctuation + " ")
    )
    printable = p_byte_pred(lambda b: b in printable_set)
    utf8_two = p_byte_pred(lambda b: b >> 5 == 0b110)
    utf8_three = p_byte_pred(lambda b: b >> 4 == 0b1110)
    utf8_four = p_byte_pred(lambda b: b >> 3 == 0b11110)
    utf8_tail = p_byte_pred(lambda b: b >> 6 == 0b10)
    return Pattern.choice(
        (
            printable,
            utf8_two + utf8_tail,
            utf8_three + utf8_tail + utf8_tail,
            utf8_four + utf8_tail + utf8_tail + utf8_tail,
        )
    )


@apply
def p_digit():
    return p_byte_pred(lambda b: ord("0") <= b <= ord("9"))


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
                        f"coro_next called with incorrect ticket: "
                        f"{ticket} != {gen_ticket} "
                        f"[{fn}(*{args}, **{kwargs})]",
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
                    return cont(
                        partial(coro_next, ticket + 1, False),
                        partial(coro_next, ticket + 1, True),
                    )

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
                        raise asyncio.CancelledError()
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
    message.write(f"failed with {et.__name__}: {eo}\n")
    traceback.print_tb(tb, file=message)
    sys.stderr.write(message.getvalue())


def cont_run(cont, on_done=None, on_error=None, name=None):
    if on_error is None:
        source = traceback.format_stack()[-2]
        on_error = partial(cont_print_exception, name, source)
    return cont(const(None) if on_done is None else on_done, on_error)


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

        return cont(partial(with_callback, out_done), partial(with_callback, out_error))

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
    __slots__ = ("handlers",)

    def __init__(self):
        self.handlers = []

    def __call__(self, event):
        handlers, self.handlers = self.handlers, []
        for handler in handlers:
            if handler(event):
                self.handlers.append(handler)

    def on(self, handler):
        self.handlers.append(handler)
        return self

    def on_once(self, handler):
        def handler_once(event):
            handler(event)
            return False

        self.handlers.append(handler_once)
        return self

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
    SCORE_MIN = float("-inf")
    SCORE_MAX = float("inf")
    SCORE_GAP_LEADING = -0.005
    SCORE_GAP_TRAILING = -0.005
    SCORE_GAP_INNER = -0.01
    SCORE_MATCH_CONSECUTIVE = 1.0

    def char_range_with(c_start, c_stop, v, d):
        d = d.copy()
        d.update((chr(c), v) for c in range(ord(c_start), ord(c_stop) + 1))
        return d

    lower_with = partial(char_range_with, "a", "z")
    upper_with = partial(char_range_with, "A", "Z")
    digit_with = partial(char_range_with, "0", "9")

    SCORE_MATCH_SLASH = 0.9
    SCORE_MATCH_WORD = 0.8
    SCORE_MATCH_CAPITAL = 0.7
    SCORE_MATCH_DOT = 0.6
    BONUS_MAP = {
        "/": SCORE_MATCH_SLASH,
        "-": SCORE_MATCH_WORD,
        "_": SCORE_MATCH_WORD,
        " ": SCORE_MATCH_WORD,
        ".": SCORE_MATCH_DOT,
    }
    BONUS_STATES = [{}, BONUS_MAP, lower_with(SCORE_MATCH_CAPITAL, BONUS_MAP)]
    BONUS_INDEX = digit_with(1, lower_with(1, upper_with(2, {})))

    def bonus(haystack):
        """Additional bonus based on previous char in haystack
        """
        c_prev = "/"
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
                if (match_required or D[i][j] == M[i][j]) and D[i][j] != SCORE_MIN:
                    match_required = (
                        i > 0
                        and j > 0
                        and M[i][j] == D[i - 1][j - 1] + SCORE_MATCH_CONSECUTIVE
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


def substr_scorer(niddle, haystack):
    positions, offset = [], 0
    niddle, haystack = niddle.lower(), haystack.lower()
    for niddle in niddle.split(" "):
        if not niddle:
            continue
        offset = haystack.find(niddle, offset)
        if offset < 0:
            return float("-inf"), None
        niddle_len = len(niddle)
        positions.extend(range(offset, offset + niddle_len))
        offset += niddle_len
    if not positions:
        return 0, positions
    match_len = positions[-1] + 1 - positions[0]
    return -match_len + 2 / (positions[0] + 1) + 1 / (positions[-1] + 1), positions


SCORER_DEFAULT = "fuzzy"
SCORERS = {"fuzzy": fuzzy_scorer, "substr": substr_scorer}

RankResult = namedtuple("RankResult", ("score", "index", "haystack", "positions"))


def _rank_task(scorer, niddle, haystack, offset):
    result = []
    for index, item in enumerate(haystack):
        score, positions = scorer(niddle, str(item))
        if positions is None:
            continue
        result.append(RankResult(-score, index + offset, item, positions))
    return result


async def rank(scorer, niddle, haystack, *, keep_order=None, executor=None, loop=None):
    """Score haystack against niddle in execturo and return sorted result
    """
    loop = loop or asyncio.get_event_loop()

    batch_size = 1024
    batches = await asyncio.gather(
        *(
            loop.run_in_executor(
                executor,
                _rank_task,
                scorer,
                niddle,
                haystack[offset : offset + batch_size],
                offset,
            )
            for offset in range(0, len(haystack), batch_size)
        ),
        loop=loop,
    )
    results = [item for batch in batches for item in batch]
    if not keep_order:
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
TTY_MOUSE = 5

KEY_MODE_SHIFT = 0b001
KEY_MODE_ALT = 0b010
KEY_MODE_CTRL = 0b100
KEY_MODE_PRESS = 0b1000
KEY_MODE_BITS = 4

KEY_MOUSE_LEFT = 1
KEY_MOUSE_RIGHT = 2
KEY_MOUSE_MIDDLE = 3
KEY_MOUSE_WHEEL_UP = 4
KEY_MOUSE_WHEEL_DOWN = 5


class TTYEvent(tuple):
    def __new__(cls, type, attrs):
        return tuple.__new__(cls, (type, attrs))

    def __repr__(self):
        type, attrs = self
        if type == TTY_KEY:
            key_name, mode = attrs
            names = []
            for mask, mode_name in (
                (KEY_MODE_ALT, "alt"),
                (KEY_MODE_CTRL, "ctrl"),
                (KEY_MODE_SHIFT, "shift"),
            ):
                if mode & mask:
                    names.append(mode_name)
            names.append(key_name)
            return f'Key({"-".join(names)})'
        elif type == TTY_CHAR:
            return f"Char({attrs})"
        elif type == TTY_CPR:
            line, column = attrs
            return f"Postion(line={line}, column={column})"
        elif type == TTY_CLOSE:
            return "Close()"
        elif type == TTY_SIZE:
            rows, columns = attrs
            return f"Size(rows={rows}, columns={columns})"
        elif type == TTY_MOUSE:
            button, mode, (line, column) = attrs
            names = []
            names.append("\u2207" if mode & KEY_MODE_PRESS else "\u2206")
            for mask, mode_name in (
                (KEY_MODE_ALT, "alt"),
                (KEY_MODE_CTRL, "ctrl"),
                (KEY_MODE_SHIFT, "shift"),
            ):
                if mode & mask:
                    names.append(mode_name)
            names.append(
                {0: "\u2205", 1: "left", 2: "right", 3: "middle", 4: "up", 5: "down"}[
                    button
                ]
            )
            return "Mouse({} at line={} column={})".format(
                "-".join(names), line, column
            )


@apply
def p_tty():
    r"""Pattern matching tty input

    NOTE:
      \n - ctrl-j
      \t - ctrl-i
    """

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
    add("\x1bOP", key("f1"))
    add("\x1bOQ", key("f2"))
    add("\x1bOR", key("f3"))
    add("\x1bOS", key("f4"))
    add("\x1b[15~", key("f5"))
    for i in range(6, 11):
        add(f"\x1b[{i + 11}~", key(f"f{i}"))
    add("\x1b[23~", key("f11"))
    add("\x1b[24~", key("f12"))

    # special
    add("\x1b", key("esc"))
    add("\x1b[5~", key("pageup"))
    add("\x1b[6~", key("pagedown"))
    add("\x1b[H", key("home"))
    add("\x1b[F", key("end"))

    # arrows
    add("\x1b[A", key("up"))
    add("\x1b[B", key("down"))
    add("\x1b[C", key("right"))
    add("\x1b[D", key("left"))
    add("\x1b[1;9A", key("up", KEY_MODE_ALT))
    add("\x1b[1;9B", key("donw", KEY_MODE_ALT))
    add("\x1b[1;9C", key("right", KEY_MODE_ALT))
    add("\x1b[1;9D", key("left", KEY_MODE_ALT))

    # alt-letter
    for b in range(ord("a"), ord("z") + 1):
        add(p_byte(27) + p_byte(b), key(chr(b), KEY_MODE_ALT))
    for b in range(ord("0"), ord("9") + 1):
        add(p_byte(27) + p_byte(b), key(chr(b), KEY_MODE_ALT))
    for b in map(ord, "`~!@#$%^&*()-_=+[{]}\\|;:'\",<.>/?"):
        add(p_byte(27) + p_byte(b), key(chr(b), KEY_MODE_ALT))

    # ctrl-letter
    for b in range(1, 27):
        add(p_byte(b), key(chr(b + 96), KEY_MODE_CTRL))
    add("\x7f", key("h", KEY_MODE_CTRL))  # backspace
    add("\x1f", key("/", KEY_MODE_CTRL))
    add("\x1c", key("\\", KEY_MODE_CTRL))
    add("\x1e", key("^", KEY_MODE_CTRL))
    add("\x1d", key("]", KEY_MODE_CTRL))

    # CPR (current position report)
    def extract_cpr(buf):
        line, column = (int(v) for v in buf[2:-1].decode().split(";"))
        return TTYEvent(TTY_CPR, (line, column))

    add(
        Pattern.sequence(
            (p_string("\x1b["), p_number, p_string(";"), p_number, p_string("R"))
        ),
        extract_cpr,
    )

    # Mouse
    def extract_mouse_sgr(buf):
        event, line, column = tuple(int(v) for v in buf[3:-1].decode().split(";"))
        mode = (event >> 2) & 0b111
        if buf[-1] == 77:  # 'M'
            mode |= KEY_MODE_PRESS
        button = (event & 0b11) + 1
        if event & 64:
            button += 3
        return TTYEvent(TTY_MOUSE, (button, mode, (line, column)))

    add(
        Pattern.sequence(
            (
                p_string("\x1b[<"),
                p_number,
                p_string(";"),
                p_number,
                p_string(";"),
                p_number,
                p_byte_pred(lambda b: b in (77, 109)),  # (m|M)
            )
        ),
        extract_mouse_sgr,
    )

    def extract_mouse_x10(buf):
        event, line, column = tuple(b - 32 for b in buf[-3:])
        mode = (event >> 2) & 0b111
        if event & 0b11 != 0b11:
            mode |= KEY_MODE_PRESS
            button = (event & 0b11) + 1
            if event & 64:
                button += 3
        else:
            button = 0
        return TTYEvent(TTY_MOUSE, (button, mode, (line, column)))

    add(
        Pattern.sequence(
            (
                p_string("\x1b[M"),
                p_byte_pred(lambda b: b >= 32),
                p_byte_pred(lambda b: b >= 32),
                p_byte_pred(lambda b: b >= 32),
            )
        ),
        extract_mouse_x10,
    )

    # chars
    add(p_utf8, lambda buf: TTYEvent(TTY_CHAR, buf.decode()))

    return Pattern.choice(patterns)


class TTYParser:
    __slots__ = ("_parse",)

    def __init__(self) -> None:
        self._parse = p_tty()
        self._parse(None)

    def __call__(self, chunk: bytes) -> Iterable[TTYEvent]:
        keys = []
        while True:
            for index, byte in enumerate(chunk):
                alive, results, unconsumed = self._parse(byte)
                if alive:
                    continue
                if results:
                    keys.append(results[-1])
                    # reschedule unconsumed for parsing
                    unconsumed.extend(chunk[index + 1 :])
                    chunk = unconsumed
                    self._parse(None)
                    break
                else:
                    sys.stderr.write(
                        "[ERROR] failed to process: {}\n".format(bytes(unconsumed))
                    )
                    self._parse(None)
            else:
                # all consumed (no break in for loop)
                break
        return keys


TTYSize = namedtuple("TTYSize", ("height", "width"))


class TTY:
    """Asynchronous tty device

    Ansi escape sequences:
      - http://invisible-island.net/xterm/ctlseqs/ctlseqs.html
    """

    __slots__ = (
        "fd",
        "size",
        "loop",
        "color_depth",
        "events",
        "events_queue",
        "write_queue",
        "write_event",
        "write_buffer",
        "write_count",
        "closed",
        "closed_event",
    )
    DEFAULT_FILE = "/dev/tty"
    EPILOGUE = (
        # enable autowrap
        b"\x1b[?7h"
        # disable mouse
        b"\x1b[?1003l"
        b"\x1b[?1006l"
        b"\x1b[?1000l"
        # visible cursor
        b"\x1b[?25h"
        # reset color settings
        b"\x1b[00m"
    )

    def __init__(self, *, file=None, loop=None, color_depth=None):
        if isinstance(file, int):
            self.fd = file
        else:
            self.fd = os.open(file or self.DEFAULT_FILE, os.O_RDWR)
        assert os.isatty(self.fd), f"file must be a tty: {file}"

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

        self.closed = False
        self.closed_event = Event()
        cont_run(self._closer(), name="TTY._closer")

    @coro
    def _closer(self):
        os.set_blocking(self.fd, False)

        attrs_old = termios.tcgetattr(self.fd)
        attrs_new = termios.tcgetattr(self.fd)
        attrs_new[tty.IFLAG] &= ~reduce(
            op.or_,
            (
                # disable flow control ctlr-{s,q}
                termios.IXON,
                termios.IXOFF,
                # carriage return
                termios.ICRNL,
                termios.INLCR,
                termios.IGNCR,
            ),
        )
        attrs_new[tty.LFLAG] &= ~reduce(
            op.or_, (termios.ECHO, termios.ICANON, termios.IEXTEN, termios.ISIG)
        )

        try:
            # set tty attributes
            termios.tcsetattr(self.fd, termios.TCSADRAIN, attrs_new)

            # resize handler
            def resize_handler():
                buf = array.array("H", (0, 0, 0, 0))
                if fcntl.ioctl(self.fileno(), termios.TIOCGWINSZ, buf):
                    size = TTYSize(0, 0)
                else:
                    size = TTYSize(buf[0], buf[1])
                self.size = size
                self.events(TTYEvent(TTY_SIZE, size))

            resize_handler()
            self.loop.add_signal_handler(signal.SIGWINCH, resize_handler)

            # reader
            parser = TTYParser()
            self.loop.add_reader(self.fd, partial(self._try_read, parser))

            # writer
            cont_run(self._writer(), name="TTY._writer")

            # wait closed event
            yield cont(self.closed_event.on)
        finally:
            # remove resize handler
            self.loop.remove_signal_handler(signal.SIGWINCH)
            # terminate queue
            self.events_queue.put_nowait(TTYEvent(TTY_CLOSE, None))
            # restore tty attributes
            termios.tcsetattr(self.fd, termios.TCSADRAIN, attrs_old)
            # write epilogue
            self.write_sync(self.EPILOGUE)
            # unregister descriptor
            os.set_blocking(self.fd, True)
            self.write_event(None)
            self.loop.remove_reader(self.fd)
            self.loop.remove_writer(self.fd)
            os.close(self.fd)

    def _try_read(self, parser):
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
                data = data[os.write(self.fd, data) :]
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
        encode = codecs.getencoder("utf-8")
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
        self.close()
        return False

    def __aiter__(self):
        return self

    async def __anext__(self):
        event = await self.events_queue.get()
        type, _ = event
        if type == TTY_CLOSE:
            raise StopAsyncIteration()
        return event

    def close(self) -> None:
        if not self.closed:
            self.closed = True
            self.closed_event(None)

    def fileno(self) -> int:
        return self.fd

    def autowrap_set(self, enable):
        if enable:
            self.write("\x1b[?7h")
        else:
            self.write("\x1b[?7l")

    def alternative_screen_set(self, enable):
        if enable:
            self.write("\x1b[?1049h")
        else:
            self.write("\x1b[?1049l")

    def mouse_set(self, enable, motion=False):
        if enable:
            self.write("\x1b[?1000h")  # SET_VT200_MOUSE
            self.write("\x1b[?1006h")  # SET_SGR_EXT_MODE_MOUSE
            motion and self.write("\x1b[?1003h")  # SET_ANY_EVENT_MOUSE
        else:
            self.write("\x1b[?1003l")
            self.write("\x1b[?1006l")
            self.write("\x1b[?1000l")

    def cursor_visibility_set(self, visible):
        if visible:
            self.write("\x1b[?25h")
        else:
            self.write("\x1b[?25l")

    def cursor_to(self, row=0, column=0):
        self.write(f"\x1b[{row};{column}H")

    def cursor_up(self, count: int) -> None:
        if count == 0:
            pass
        elif count == 1:
            self.write("\x1b[A")
        elif count > 1:
            self.write(f"\x1b[{count}A")
        else:
            self.cursor_down(-count)

    def cursor_down(self, count: int) -> None:
        if count == 0:
            pass
        elif count == 1:
            self.write("\x1b[B")
        elif count > 1:
            self.write(f"\x1b[{count}B")
        else:
            self.cursor_up(-count)

    def cursor_to_column(self, index: int) -> None:
        if index == 0:
            self.write("\x1b[G")
        elif index > 1:
            self.write(f"\x1b[{index}G")
        else:
            raise ValueError(f"column index can not be negative: {index}")

    def cursor_forward(self, count: int) -> None:
        if count == 0:
            pass
        elif count == 1:
            self.write("\x1b[C")
        elif count > 1:
            self.write(f"\x1b[{count}C")
        else:
            self.cursor_backward(-count)

    def cursor_backward(self, count: int) -> None:
        if count == 0:
            pass
        elif count == 1:
            self.write("\x1b[D")
        elif count > 1:
            self.write(f"\x1b[{count}D")
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

        self.write_sync(b"\x1b[6n")
        return await cpr

    def erase_line(self) -> None:
        self.write("\x1b[K")

    def erase_down(self):
        self.write("\x1b[J")


# ------------------------------------------------------------------------------
# Text
# ------------------------------------------------------------------------------
COLOR_DEPTH_24 = 1
COLOR_DEPTH_8 = 2
COLOR_DEPTH_4 = 3
if os.environ.get("COLORTERM") in ("truecolor", "24bit"):
    COLOR_DEPTH_DEFAULT = COLOR_DEPTH_24
else:
    COLOR_DEPTH_DEFAULT = COLOR_DEPTH_8


class Color(tuple):
    __slots__ = tuple()
    HEX_PATTERN = re.compile(
        "^#?"
        "([0-9a-fA-F]{2})"  # red
        "([0-9a-fA-F]{2})"  # green
        "([0-9a-fA-F]{2})"  # blue
        "([0-9a-fA-F]{2})?"  # optional alpha
        "$"
    )

    def __new__(cls, color):
        if isinstance(color, str):
            match = cls.HEX_PATTERN.match(color)
            if match is None:
                raise ValueError(f"invalid color: {color}")
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
                raise ValueError(f"invalid color: {color}")
        else:
            raise ValueError(f"invalid color: {color}")
        return tuple.__new__(cls, color)

    red = property(lambda self: self[0])
    gren = property(lambda self: self[1])
    green = property(lambda self: self[2])
    alpha = property(lambda self: self[3])
    luma = property(
        lambda self: sum(c * p for c, p in zip(self, (0.2126, 0.7152, 0.0722)))
    )

    def hex(self):
        r, g, b, a = self
        return "#{:02x}{:02x}{:02x}{}".format(
            round(r * 255),
            round(g * 255),
            round(b * 255),
            f"{int(a * 255):02x}" if a != 1 else "",
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
        fg = ";38;5;231" if self.luma < 0.5 else ";38;5;232"
        return f"Color(\x1b[00{fg}{self.sgr(False)}m{self.hex()}\x1b[m)"

    def sgr(self, is_fg, depth=None):
        """Return part of SGR sequence responsible for picking this color
        """
        depth = depth or COLOR_DEPTH_DEFAULT
        r, g, b, _ = self

        if depth == COLOR_DEPTH_24:
            p = ";38" if is_fg else ";48"
            return f"{p};2;{int(r * 255)};{int(g * 255)};{int(b * 255)}"

        elif depth == COLOR_DEPTH_8:

            def l2(lr, lg, lb, rr, rg, rb):
                return (lr - rr) ** 2 + (lg - rg) ** 2 + (lb - rb) ** 2

            # quantized color
            def v2q(value):
                if value < 0.1882:  # 48 / 255
                    return 0
                elif value < 0.4471:  # 114 / 255
                    return 1
                else:
                    return int((value * 255.0 - 35.0) / 40.0)

            # value range for color cupe [0x00, 0x5f, 0x87, 0xaf, 0xd7, 0xff]
            q2v = (0.0, 0.3725, 0.5294, 0.6863, 0.8431, 1.0)
            qr, qg, qb = v2q(r), v2q(g), v2q(b)
            cr, cg, cb = q2v[qr], q2v[qg], q2v[qb]

            # grayscale color
            c = (r + g + b) / 3
            gi = 23 if c > 0.9333 else int((c * 255 - 3) / 10)
            gv = (8 + 10 * gi) / 255.0

            # determine if gray is closer then quantized color
            if l2(cr, cg, cb, r, g, b) > l2(gv, gv, gv, r, g, b):
                i = 232 + gi
            else:
                i = 16 + 36 * qr + 6 * qg + qb
            p = ";38" if is_fg else ";48"
            return f"{p};5;{i}"

        elif depth == COLOR_DEPTH_4:

            def l2(lr, lg, lb, rr, rg, rb):
                return (lr - rr) ** 2 + (lg - rg) ** 2 + (lb - rb) ** 2

            best_fg, best_bg, min_d = None, None, 4
            for fg, bg, cr, cg, cb in (
                (";30", ";40", 0, 0, 0),
                (";31", ";41", 0.5, 0, 0),
                (";32", ";42", 0, 0.5, 0),
                (";33", ";43", 0.5, 0.5, 0),
                (";34", ";44", 0, 0, 0.5),
                (";35", ";45", 0.5, 0, 0.5),
                (";36", ";46", 0, 0.5, 0.5),
                (";37", ";47", 0.75, 0.75, 0.75),
                (";90", ";100", 0.5, 0.5, 0.5),
                (";91", ";101", 1, 0, 0),
                (";92", ";102", 0, 1, 0),
                (";93", ";103", 1, 1, 0),
                (";94", ";104", 0, 0, 1),
                (";95", ";105", 1, 0, 1),
                (";96", ";106", 0, 1, 1),
                (";97", ";107", 1, 1, 1),
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
FACE_MASK = (1 << 6) - 1
FACE_MAP = (
    (FACE_BOLD, ";01"),
    (FACE_ITALIC, ";03"),
    (FACE_UNDERLINE, ";04"),
    (FACE_BLINK, ";05"),
    (FACE_REVERSE, ";07"),
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
        fg = bg.overlay(fg_light if bg.luma < 0.5 else fg_dark)
        return Face(fg, bg, attrs)

    def render(self, stream):
        seq = FACE_RENDER_CACHE.get(self)
        if seq is None:
            fg, bg, attrs = self
            buf = ["\x1b[00"]  # first reset previous SGR settings
            if attrs:
                for attr, code in FACE_MAP:
                    if attrs & attr:
                        buf.append(code)
            depth = getattr(stream, "color_depth", None)
            if fg is not None:
                buf.append(fg.sgr(True, depth))
            if bg is not None:
                buf.append(bg.sgr(False, depth))
            buf.append("m")
            seq = "".join(buf)
            FACE_RENDER_CACHE[self] = seq
        stream.write(seq)

    def __str__(self):
        stream = io.StringIO()
        self.render(stream)
        return stream.getvalue()

    def __repr__(self):
        return f"Face({str(self)} X \x1b[m)"

    def with_sgr(self, params):
        if not params:
            return self
        ansi_colors = (
            (0, 0, 0),
            (0.5, 0, 0),
            (0, 0.5, 0),
            (0.5, 0.5, 0),
            (0, 0, 0.5),
            (0.5, 0, 0.5),
            (0, 0.5, 0.5),
            (0.75, 0.75, 0.75),
            (0.5, 0.5, 0.5),
            (1, 0, 0),
            (0, 1, 0),
            (1, 1, 0),
            (0, 0, 1),
            (1, 0, 1),
            (0, 1, 1),
            (1, 1, 1),
        )
        fg, bg, attrs = self
        params = list(reversed(params))
        while params:
            param = params.pop()
            if param == 1:
                attrs |= FACE_BOLD
            elif param == 3:
                attrs |= FACE_ITALIC
            elif param == 4:
                attrs |= FACE_UNDERLINE
            elif param == 5:
                attrs |= FACE_BLINK
            elif param == 7:
                attrs |= FACE_REVERSE
            elif 30 <= param <= 37:
                fg = Color(ansi_colors[param - 30])
            elif 40 <= param <= 47:
                bg = Color(ansi_colors[param - 40])
            elif 90 <= param <= 97:
                fg = Color(ansi_colors[param - 82])
            elif 100 <= param <= 107:
                bg = Color(ansi_colors[param - 92])
            elif param == 38 or param == 48:
                if len(params) < 2:
                    break
                depth = params.pop()
                if depth == 5:  # 256 colors
                    n = params.pop()
                    if n < 16:
                        color = Color(ansi_colors[n])
                    elif n <= 231:
                        n -= 16
                        qr, n = divmod(n, 36)
                        qg, qb = divmod(n, 6)
                        q2v = (0.0, 0.3725, 0.5294, 0.6863, 0.8431, 1.0)
                        color = Color((q2v[qr], q2v[qg], q2v[qb]))
                    elif n <= 255:
                        v = (8 + 10 * (n - 232)) / 255.0
                        color = Color((v, v, v))
                elif depth == 2:  # true color
                    if len(params) < 3:
                        break
                    color = Color(
                        (
                            params.pop() / 255.0,
                            params.pop() / 255.0,
                            params.pop() / 255.0,
                        )
                    )
                if param == 38:
                    fg = color
                else:
                    bg = color
        return Face(fg, bg, attrs)


@apply
def p_ansi_text():
    def extract_sgr(buf):
        return (False, tuple(map(int, buf[2:-1].decode().split(";"))))

    sgr = Pattern.sequence(
        (p_string("\x1b["), p_number, (p_string(";") + p_number).many(), p_string("m"))
    ).map(extract_sgr)
    utf8 = p_utf8.map(lambda buf: (True, buf.decode()))
    sgr_reset = p_string("\x1b[m").map(lambda _: (False, tuple()))
    return (utf8 | sgr | sgr_reset).optimize()


class Text:
    """Formated text (string with associated faces)
    """

    __slots__ = ("_chunks", "_len")

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
                rights.extend(self._chunks[chunk_index + 1 :])
                break
            else:
                left, right = text[:index], text[index:]
                if left:
                    lefts.append((left, face))
                if right:
                    rights.append((right, face))
                rights.extend(self._chunks[chunk_index + 1 :])
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

    def chunk(self, size):
        text, chunks = self, []
        while text:
            chunk, text = text.split(size)
            chunks.append(chunk)
        chunks = chunks or [self]
        return chunks

    def __getitem__(self, selector):
        if isinstance(selector, slice):
            start, stop = selector.start, selector.stop
            assert selector.step != 1, "slice step is not supported"
            start = 0 if start is None else (start if start >= 0 else len(self) + start)
            stop = (
                len(self) if stop is None else (stop if stop >= 0 else len(self) + stop)
            )
            _, result = self.split(start)
            result, _ = result.split(stop - start)
            return result
        elif isinstance(selector, int):
            return self[selector : selector + 1]
        else:
            raise ValueError("text indices must be integers")

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
        self.render(stream)
        return stream.getvalue()

    def __repr__(self):
        return f"Text('{str(self)}')"

    @classmethod
    def from_ansi(cls, input):
        if isinstance(input, str):
            input = input.encode()
        parse = p_ansi_text()
        parse(None)

        chunks = []
        chunk, face = io.StringIO(), Face()
        while True:
            for index, byte in enumerate(input):
                alive, results, unconsumed = parse(byte)
                if alive:
                    continue
                if results:
                    is_char, value = results[-1]
                    if is_char:
                        chunk.write(value)
                    else:
                        if chunk.tell() != 0:
                            chunks.append((chunk.getvalue(), face))
                            chunk.seek(0)
                            chunk.truncate()
                        face = face.with_sgr(value)
                    # reschedule unconsumed for parsing
                    unconsumed.extend(input[index + 1 :])
                    input = unconsumed
                    parse(None)
                    break
                else:
                    sys.stderr.write(
                        "[ERROR] failed to process: {}\n".format(bytes(unconsumed))
                    )
                    parse(None)
            else:
                # all consumed (no break in for loop)
                chunks.append((chunk.getvalue(), face))
                break
        return Text(chunks)


# ------------------------------------------------------------------------------
# Widgets
# ------------------------------------------------------------------------------
def Theme(base, match, fg, bg):
    base = Color(base)
    match = base.with_alpha(0.35) if match is None else Color(match)
    fg = Color(fg)
    bg = Color(bg)
    theme_dict = {
        "base_bg": Face(bg=base).with_fg_contrast(fg, bg),
        "base_fg": Face(fg=base, bg=bg),
        "base_bg_1": Face(bg=bg.overlay(match)).with_fg_contrast(fg, bg),
        "base_fg_1": Face,
        "match": Face(bg=bg.overlay(match)).with_fg_contrast(fg, bg),
        "input_default": Face(fg=fg, bg=bg),
        "list_dot": Face(fg=base),
        "list_selected": Face(
            fg=bg.overlay(fg.with_alpha(0.9)), bg=bg.overlay(fg.with_alpha(0.055))
        ),
        "list_default": Face(fg=bg.overlay(fg.with_alpha(0.9)), bg=bg),
        "list_scrollbar_on": Face(bg=base.with_alpha(0.8)),
        "list_scrollbar_off": Face(bg=base.with_alpha(0.4)),
        "candidate_active": Face(fg=bg.overlay(fg.with_alpha(0.9))),
        "candidate_inactive": Face(fg=bg.overlay(fg.with_alpha(0.4))),
    }
    return type("Theme", tuple(), theme_dict)()


THEME_LIGHT_ATTRS = dict(base="#8f3f71", match=None, fg="#3c3836", bg="#fbf1c7")
THEME_DARK_ATTRS = dict(base="#d3869b", match=None, fg="#ebdbb2", bg="#282828")
THEME_DEFAULT = Theme(**THEME_DARK_ATTRS)


class InputWidget:
    __slots__ = ("buffer", "cursor", "update", "prefix", "suffix", "tty", "theme")

    def __init__(self, tty, theme=None, buffer=None, cursor=None):
        self.prefix = Text("")
        self.suffix = Text("")
        self.update = Event()
        self.tty = tty
        self.theme = theme or THEME_DEFAULT
        self.set(buffer, cursor)

    def set(self, buffer=None, cursor=None):
        self.buffer = [] if buffer is None else list(buffer)
        self.cursor = len(self.buffer) if cursor is None else cursor
        self.notify()

    def notify(self):
        self.update("".join(self.buffer))

    @property
    def input(self):
        return "".join(self.buffer)

    def __call__(self, event):
        type, attrs = event
        if type == TTY_KEY:
            name, mode = attrs
            if name == "left":
                self.cursor = max(0, self.cursor - 1)
                return True
            elif name == "right":
                self.cursor = min(len(self.buffer), self.cursor + 1)
                return True
            elif mode & KEY_MODE_CTRL:
                if name == "a":
                    self.cursor = 0
                    return True
                elif name == "e":
                    self.cursor = len(self.buffer)
                    return True
                elif name == "h":  # delete
                    if self.cursor > 0:
                        self.cursor -= 1
                        del self.buffer[self.cursor]
                        self.notify()
                        return True
                elif name == "k":
                    del self.buffer[self.cursor :]
                    self.notify()
                    return True
        elif type == TTY_CHAR:
            self.buffer.insert(self.cursor, attrs)
            self.notify()
            self.cursor += 1
            return True
        return False

    def set_prefix(self, prefix):
        self.prefix = prefix

    def set_suffix(self, suffix):
        self.suffix = suffix

    def render(self):
        tty = self.tty
        face = self.theme.input_default
        face.render(tty)
        tty.erase_line()
        self.prefix.render(tty, face)
        face.render(tty)
        tty.write("".join(self.buffer))
        tty.cursor_to_column(tty.size.width - len(self.suffix) + 1)
        self.suffix.render(tty, face)
        tty.cursor_to_column(len(self.prefix) + self.cursor + 1)


class ListWidget:
    __slots__ = (
        "items",
        "height",
        "offset",
        "cursor",
        "item_to_text",
        "layout",
        "layout_height",
        "tty",
        "theme",
    )

    def __init__(self, tty, items=None, height=None, item_to_text=None, theme=None):
        self.items = items or []  # list of all items
        self.cursor = 0  # selected item in visible items
        self.offset = 0  # offset of first rendered item
        self.height = height or 10  # height of the widget
        self.item_to_text = item_to_text or (
            lambda i: i
        )  # how to convert item to a text
        self.layout = []  # [[default_face, left_margin, text, scorllbar]]
        self.layout_height = 0  # number of items show in layout
        self.tty = tty
        self.theme = theme or THEME_DEFAULT
        self.update_layout()

    def __call__(self, event: TTYEvent) -> bool:
        type, attrs = event
        if type == TTY_KEY:
            name, mode = attrs
            if name == "up":
                self.move(-1)
                return True
            elif name == "pageup":
                self.move(-self.height)
                return True
            elif name == "down":
                self.move(1)
                return True
            elif name == "pagedown":
                self.move(self.height)
                return True
            elif name == "home":
                self.move(-(1 << 32))
                return True
            elif name == "end":
                self.move(1 << 32)
                return True
            elif mode & KEY_MODE_CTRL:
                if name == "p":
                    self.move(-1)
                    return True
                elif name == "n":
                    self.move(1)
                    return True
        elif type == TTY_MOUSE:
            button, mode, _ = attrs
            if mode & KEY_MODE_PRESS:
                if button == KEY_MOUSE_WHEEL_UP:
                    self.move(-1)
                    return True
                elif button == KEY_MOUSE_WHEEL_DOWN:
                    self.move(1)
                    return True
        elif type == TTY_SIZE:
            self.update_layout()
            return True
        return False

    @property
    def selected(self):
        """Current selected item"""
        current = self.offset + self.cursor
        if 0 <= current < len(self.items):
            return self.items[current]
        else:
            return None

    def move(self, count: int) -> None:
        self.cursor += count
        if self.cursor < 0:
            self.offset += self.cursor
            self.cursor = 0
            if self.offset < 0:
                self.offset = 0
        elif self.offset + self.cursor < len(self.items):
            if self.cursor >= self.layout_height:
                self.offset += self.cursor - self.layout_height + 1
                self.cursor = self.layout_height - 1
        else:
            if self.cursor >= len(self.items):
                self.offset, self.cursor = len(self.items) - 1, 0
            else:
                self.cursor = self.layout_height - 1
                self.offset = len(self.items) - self.cursor - 1
        self.update_layout()

    def reset(self, items):
        self.cursor = 0
        self.offset = 0
        self.items = items
        self.update_layout()

    def update_layout(self):
        width = self.tty.size.width
        theme = self.theme
        layout = []  # [[default_face, left_margin, text, scorllbar]]

        line_index = 0  # current line of layout
        index = 0  # index of item starting with `self.offset`
        while line_index < self.height:
            if 0 <= self.offset + index < len(self.items):
                face = (
                    theme.list_selected if self.cursor == index else theme.list_default
                )
                text = self.item_to_text(self.items[self.offset + index])
                for chunk_index, chunk in enumerate(text.chunk(width - 4)):
                    if self.cursor == index and chunk_index == 0:
                        left_margin = Text(" \u25cf ").mark(theme.list_dot)
                    else:
                        left_margin = Text("   ")
                    layout.append([face, left_margin, chunk])
                    line_index += 1
                index += 1
            else:
                layout.append([theme.list_default, Text("   "), Text("")])
                line_index += 1

        # only keep `self.height` lines in layout
        if self.cursor + 1 == index and index != 0:
            layout = layout[-self.height :]
        else:
            layout = layout[: self.height]

        # fill scroll bar
        if self.items:
            sb_filled = max(1, min(self.height, self.height * index // len(self.items)))
            sb_empty = round(
                (self.height - sb_filled)
                * (self.offset + self.cursor)
                / len(self.items)
            )
        else:
            sb_filled = self.height
            sb_empty = 0
        sb_text = Text(" ")
        for line_index, line in enumerate(layout):
            if sb_empty <= line_index < sb_empty + sb_filled:
                line.append(sb_text.mark(line[0].overlay(theme.list_scrollbar_on)))
            else:
                line.append(sb_text.mark(line[0].overlay(theme.list_scrollbar_off)))

        self.layout = layout
        self.layout_height = index

    def render(self):
        tty = self.tty
        width = self.tty.size.width
        for face, left, text, right in self.layout:
            face.render(tty)
            left.render(tty, face)
            text.render(tty, face)
            tty.erase_line()  # will fill with current color
            tty.cursor_to_column(width)
            right.render(tty)
            tty.cursor_to_column(0)
            tty.cursor_down(1)
        tty.write("\x1b[m")


# ------------------------------------------------------------------------------
# Select
# ------------------------------------------------------------------------------
class Candidate(tuple):
    def __new__(cls, fields, positions=None):
        return tuple.__new__(cls, (fields, positions))

    @classmethod
    def from_str(cls, string, delimiter=None, predicate=None):
        """Create `Candidate` from string

        - delimiter - field separator
        - predicate - inidicate whether field is serachable basend on its index
        """
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

        return cls(
            tuple((field, predicate(index)) for index, field in enumerate(fields))
        )

    @classmethod
    def line_decoder(cls, delimiter=None, predicate=None):
        """Create line decoder object.

        Line decoder splits incoming chunks into lines and converts them
        to `Candidate` with `Candidate::from_str`. Decoder is a function
        which consumes chunks of bytes, and returns list of candidates,
        if chunks is None, it means all chunks have been received.
        """

        def line_decoder():
            buffer = b""
            candidates = []
            while True:
                chunk = yield candidates
                if chunk is None:
                    line = buffer.strip().decode(errors="backslashreplace")
                    return [Candidate.from_str(line)] if line else []
                buffer += chunk
                lines = buffer.split(b"\n")
                buffer = lines[-1]
                lines = (
                    line.strip().decode(errors="backslashreplace")
                    for line in lines[:-1]
                )
                candidates = list(map(Candidate.from_str, filter(None, lines)))

        def line_decode(chunk):
            try:
                return line_decoder_gen.send(chunk)
            except StopIteration as ret:
                return ret.args[0] if ret.args else []

        line_decoder_gen = line_decoder()
        line_decoder_gen.send(None)
        return line_decode

    def to_str(self):
        fields, _ = self
        return "".join(field for field, _ in fields)

    def to_text(self, theme=None):
        fields, positions = self
        theme = theme or THEME_DEFAULT

        face_active = theme.candidate_active
        face_inactive = theme.candidate_inactive

        text = Text("").join(
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
        return "".join(field for field, active in fields if active)

    def __repr__(self):
        stream = io.StringIO()
        self.to_text().render(stream)
        return f"Candidate('{stream.getvalue()}')"

    def __reduce__(self):
        return Candidate, tuple(self)


class CandidatesAsync:
    """Candidates that are asynchronously loaded from provided file
    """

    __slots__ = ("candidates", "loop", "decoder", "fd", "update", "reversed")

    def __init__(self, file, decoder, reversed=False, loop=None):
        self.loop = loop or asyncio.get_event_loop()
        self.decoder = decoder
        self.reversed = reversed
        self.fd = file if isinstance(file, int) else file.fileno()

        self.candidates = []
        self.update = Event()
        os.set_blocking(self.fd, False)
        self.loop.add_reader(self.fd, self._try_read)

    def _try_read(self):
        try:
            chunk = os.read(self.fd, 4096)
            if not chunk:
                self.close()
                return
        except BlockingIOError:
            pass
        else:
            self.extend(self.decoder(chunk))
            self.notify()

    def notify(self):
        self.update(self.candidates)

    def __len__(self):
        return len(self.candidates)

    def __getitem__(self, selector):
        return self.candidates[selector]

    def extend(self, candidates):
        if self.reversed:
            self.candidates, candidates = candidates[::-1], self.candidates
        self.candidates.extend(candidates)

    def close(self):
        if self.fd is not None:
            fd, self.fd = self.fd, None
            self.loop.remove_reader(fd)
            os.set_blocking(fd, True)
            self.extend(self.decoder(None))
            self.notify()

    def __enter__(self):
        return self

    def __exit__(self, et, eo, tb):
        self.close()


def rate_limit_callback(max_frequency, loop=None):
    """Rate limiting decorator
    """

    def rate_limit_callback(callback):
        def call_at_callback():
            nonlocal last_call, scheduled
            scheduled = False
            last_call = event_loop.time()
            callback()

        def rate_limited_callback():
            nonlocal last_call, scheduled
            if scheduled:
                return
            now = event_loop.time()
            if now - last_call >= delay:
                last_call = now
                callback()
            else:
                scheduled = True
                event_loop.call_at(last_call + delay, call_at_callback)

        scheduled = False
        last_call = 0
        event_loop = loop or asyncio.get_event_loop()
        return rate_limited_callback

    delay = 1.0 / max_frequency
    return rate_limit_callback


class SingletonTask:
    def __init__(self, loop=None):
        self.loop = loop or asyncio.get_event_loop()
        self.task = None

    def __call__(self, task):
        """"Schedule new task and cancel current one if any
        """
        if self.task is not None:
            self.task.cancel()
        self.task = asyncio.ensure_future(task, loop=self.loop)

    def __enter__(self):
        return self

    def __exit__(self, et, eo, tb):
        if self.task is not None:
            self.task.cancel()


class ScorerToggler:
    __slots__ = ("scorers", "index")

    def __init__(self, scorer=None):
        scorers, index = [], None
        for i, (n, s) in enumerate(SCORERS.items()):
            if s is scorer:
                index = i
            scorers.append((n, s))
        if index is None:
            scorers.append(("custom", scorer))
            index = len(scorers) - 1
        self.index = index
        self.scorers = scorers

    @property
    def scorer(self):
        return self.scorers[self.index][1]

    @property
    def name(self):
        return self.scorers[self.index][0]

    def next(self):
        self.index = (self.index + 1) % len(self.scorers)


async def select(
    candidates,
    *,
    scorer=None,
    keep_order=None,
    height=None,
    prompt=None,
    tty=None,
    executor=None,
    loop=None,
    theme=None,
):
    """Show text UI to select candidate

    Candidates can be `List[str | Candidate] | CandidatesAsync`
    """
    prompt = prompt or "input"
    height = height or 10
    theme = theme or THEME_DEFAULT
    loop = loop or asyncio.get_event_loop()
    scorer = ScorerToggler(scorer or SCORERS[SCORER_DEFAULT])

    face_base_fg = theme.base_fg
    face_base_bg = theme.base_bg
    face_match = theme.match

    def item_to_text(item):
        if isinstance(item.haystack, Candidate):
            return item.haystack.with_positions(item.positions).to_text(theme)
        else:
            return Text(item.haystack).mark_mask(face_match, item.positions)

    def suffix(count, time):
        return reduce(
            op.add,
            (
                Text(" \ue0b2").mark(face_base_fg),
                Text(f" {count}/{len(candidates)} {time:.2f}s").mark(face_base_bg),
                Text(
                    " [{}{}]".format(
                        "\ue0a2" if keep_order else "", scorer.name[0].upper()
                    )
                ).mark(face_base_bg),
            ),
        )

    async def table_update_coro():
        niddle = input.input
        # rank
        start = time.time()
        result = await rank(
            scorer.scorer,
            niddle,
            candidates,
            loop=loop,
            executor=executor,
            keep_order=keep_order,
        )
        stop = time.time()
        # set suffix
        input.set_suffix(suffix(len(result), stop - start))
        table.reset(result)
        render()

    @rate_limit_callback(5.0, loop=loop)
    def table_update():
        table_update_task(table_update_coro())

    @rate_limit_callback(30.0, loop=loop)
    def render():
        # clean screen down
        tty.cursor_to(line, column)
        tty.write("\x1b[00m")
        tty.erase_down()
        # show table
        tty.cursor_to(line + 1, column)
        table.render()
        # show input
        tty.cursor_to(line, column)
        input.render()
        # flush frame
        tty.flush()

    with ExitStack() as stack:
        tty = tty or stack.enter_context(TTY(loop=loop))
        executor = executor or stack.enter_context(ProcessPoolExecutor(max_workers=5))

        prefix = reduce(
            op.add,
            (
                Text(f" {prompt} ").mark(face_base_bg.overlay(Face(attrs=FACE_BOLD))),
                Text("\ue0b0 ").mark(face_base_fg),
            ),
        )
        input = InputWidget(tty, theme=theme)
        input.set_prefix(prefix)
        input.set_suffix(suffix(0, 0))
        table = ListWidget(tty, height=height, item_to_text=item_to_text, theme=theme)

        table_update_task = stack.enter_context(SingletonTask())
        input.update.on(lambda _: (table_update(),))
        candidates_update = getattr(candidates, "update", None)
        if candidates_update is not None:
            candidates_update.on(lambda _: (table_update(),))

        tty.autowrap_set(False)
        tty.mouse_set(True)

        # reserve space (force scroll)
        tty.write("\n" * table.height)
        tty.cursor_up(table.height)
        tty.flush()

        line, column = await tty.cursor_cpr()
        input.update("")  # force table update

        result = -1
        async for event in tty:
            type, attrs = event
            if type == TTY_KEY:
                name, mode = attrs
                if mode == KEY_MODE_CTRL:
                    if name in "cg":
                        break
                    elif name in "mj":
                        selected = table.selected
                        result = -1 if selected is None else selected.index
                        break
                    elif name == "i":  # \t completion
                        selected = table.selected
                        if selected is not None:
                            input.set(str(selected.haystack))
                            render()
                    elif name == "r":
                        keep_order = not keep_order
                        input.notify()
                    elif name == "s":
                        scorer.next()
                        input.notify()
            if any((type == TTY_SIZE, input(event), table(event))):
                render()

        tty.cursor_to(line, column)
        tty.write("\x1b[00m")
        tty.erase_down()
        tty.flush()

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
        for field in argument.split(","):
            field = field.split("..")
            if len(field) == 1:
                fields.add(int(field[0]) - 1)
            elif len(field) == 2:
                low, high = field
                predicates.append(
                    predicate(
                        int(low) - 1 if low else None, int(high) - 1 if high else None
                    )
                )
            else:
                raise argparse.ArgumentTypeError(
                    f'invalid predicate: {"..".join(fields)}'
                )

        return lambda index: any(predicate(index) for predicate in predicates)

    def parse_color_depth(argument):
        depths = {"24": COLOR_DEPTH_24, "8": COLOR_DEPTH_8, "4": COLOR_DEPTH_4}
        depth = depths.get(argument)
        if depth is None:
            raise argparse.ArgumentTypeError(
                f'invalid depth: {argument} (allowed [{",".join(depths)}])'
            )
        return depth

    def parse_scorer(argument):
        scorer = SCORERS.get(argument)
        if scorer is None:
            raise argparse.ArgumentTypeError(
                f'invalid scorer: {argument} (allowed [{",".join(SCORERS.keys())}])'
            )
        return scorer

    def parse_theme(argument):
        attrs = dict(THEME_DARK_ATTRS)
        for attr in argument.lower().split(","):
            if attr == "light":
                attrs.update(THEME_LIGHT_ATTRS)
            elif attr == "dark":
                attrs.update(THEME_DARK_ATTRS)
            else:
                key, value = attr.split("=")
                value = value.strip("\"'")
                if not value or value == "none":
                    attrs[key] = None
                else:
                    attrs[key] = value
        return Theme(**attrs)

    def parse_height(argument):
        try:
            height = int(argument)
            if height <= 0:
                raise ValueError()
            return height
        except ValueError:
            raise argparse.ArgumentTypeError(
                f"hieght must a postivie integer: {argument}"
            )

    parser = argparse.ArgumentParser(
        description=textwrap.dedent(
            """\
    Sweep is a command line fuzzy finer (fzf analog)
    """
        )
    )
    parser.add_argument(
        "-p", "--prompt", default="input", help="override prompt string"
    )
    parser.add_argument(
        "-r", "--reversed", action="store_true", help="reverse initial order of items"
    )
    parser.add_argument(
        "-n",
        "--nth",
        type=parse_nth,
        help="comma-separated list of fields for limiting search scope",
    )
    parser.add_argument(
        "-d",
        "--delimiter",
        type=re.compile,
        default=re.compile("[ \t]+"),
        help="field delimiter regular expression",
    )
    parser.add_argument(
        "--theme",
        type=parse_theme,
        default=THEME_DEFAULT,
        help="specify theme as a list of comma sperated attributes",
    )
    parser.add_argument(
        "--color-depth",
        type=parse_color_depth,
        default=COLOR_DEPTH_DEFAULT,
        help="color depth",
    )
    parser.add_argument("--debug", action="store_true", help="enable debugging")
    parser.add_argument(
        "--keep-order", action="store_true", help="keep order (don't use ranking score)"
    )
    parser.add_argument(
        "--scorer",
        type=parse_scorer,
        default=SCORERS.get(SCORER_DEFAULT),
        help="default scorer to rank candidates",
    )
    parser.add_argument("--tty-device", help="tty device file (useful for debugging)")
    parser.add_argument("--height", type=parse_height, help="height of the list show")
    parser.add_argument(
        "--sync", action="store_true", help="block on reading full input"
    )
    return parser.parse_args()


def main() -> None:
    options = main_options()

    # `kqueue` does not support tty, fallback to `select`
    if sys.platform in ("darwin",):
        import selectors

        asyncio.set_event_loop(asyncio.SelectorEventLoop(selectors.SelectSelector()))

    loop = asyncio.get_event_loop()
    if options.debug:
        # enable asyncio debugging
        import logging

        loop.set_debug(True)
        logging.getLogger("asyncio").setLevel(logging.INFO)

        # debug lable callback
        def debug_label(event):
            label = " ".join(
                ("", f"event: {event}", f"write_count: {tty.write_count}", "")
            )
            tty.cursor_to(0, 0)
            Text(label).mark(face_debug_label).render(tty)
            tty.erase_line()
            tty.flush()
            return True

        face_debug_label = Face(bg=Color("#cc241d"), fg=Color("#ebdbb2"))
    else:
        debug_label = lambda _: False

    decoder = Candidate.line_decoder(delimiter=options.delimiter, predicate=options.nth)
    if options.sync or sys.stdin.isatty():
        candidates = []
        while True:
            chunk = os.read(sys.stdin.fileno(), 4096)
            if not chunk:
                candidates.extend(decoder(None))
                break
            candidates.extend(decoder(chunk))
        if options.reversed:
            candidates = candidates[::-1]
    else:
        candidates = CandidatesAsync(
            sys.stdin, decoder, reversed=options.reversed, loop=loop
        )

    with ExitStack() as stack:

        @stack.callback
        def _():
            loop.run_until_complete(loop.shutdown_asyncgens())
            loop.close()

        executor = stack.enter_context(ProcessPoolExecutor(max_workers=5))
        tty = stack.enter_context(
            TTY(file=options.tty_device, loop=loop, color_depth=options.color_depth)
        )
        tty.events.on(debug_label)

        selected = loop.run_until_complete(
            select(
                candidates,
                prompt=options.prompt,
                loop=loop,
                tty=tty,
                executor=executor,
                theme=options.theme,
                keep_order=options.keep_order,
                scorer=options.scorer,
                height=options.height,
            )
        )
    if selected >= 0:
        print(candidates[selected].to_str())


if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        sys.stderr.write("interrupted by user\n")
