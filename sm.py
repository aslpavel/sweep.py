#!/usr/bin/env python
"""
Parser a = Byte -> a | Fail | Parser a  # Function must be a map

map :: (a -> b) -> Parser a -> Parser b
<*> :: Parser (a -> b) -> Parser a -> Parser b
<|> :: Parser a -> Parser a -> Parser a

seq :: Parser a -> Parser b -> Parser (a, b)
seq a b = (,) <$> a <*> b

a0 : a -> (b -> (a, b))
a1 : Parser a
a2 : Parser b

~> a0 <$>           : Parser a -> Parser (b -> (a, b))
~> a0 <$> a1        : Parser (b -> (a, b))
~> a0 <$> a1 <*> a2 : Parser (a, b)

TODO:
  - [parser] add associated name
  - [parser] `__repr__` using names and cobinators
"""


def apply(fn, *args, **kwargs):
    return fn(*args, **kwargs)


@apply
class Fail:
    def __repr__(self):
        return '<Fail>'


@apply
class Feed:
    def __repr__(self):
        return '<Feed>'


@apply
class Final:
    def __repr__(self):
        return '<Final>'


class Parser:
    """Parser which represented as state machine

    table    : List[Map[Input, State]]  - state transition table
    finals   : Set[State]               - dictionary of final states
    folds    : Map[State, Result? -> Input -> Result]
    epsilons : Map[State, Set[State]]   - epsilon moves
    """
    STATE_START = 0
    STATE_FAIL = -1

    def __init__(self, table, finals, folds=None, epsilons=None):
        assert all(-1 <= s < len(table) for ss in table for s in ss.values()),\
            f'invalid transition state found: {table}'
        assert all(-1 <= s <= len(table) for s in finals),\
            f'invalid final state found: {finals}'

        self.table = table
        self.finals = finals
        self.folds = folds or {}
        self.epsilons = epsilons or {}

    def compile(self, callback):
        def parse(input):
            nonlocal state, value

            if input is None:
                state = STATE_START
            elif state != STATE_FAIL:
                state = table[state].get(input, STATE_FAIL)

            if state == STATE_FAIL:
                return (Fail, value)

            fold = folds.get(state)
            if fold:
                value = fold(value, input)
            else:
                value = input

            return (Final, value) if state in finals else (Feed, value)

        state, value = self.STATE_FAIL, None

        parser = self
        if self.epsilons:
            parser = self.optimize()
        STATE_START, STATE_FAIL = self.STATE_START, self.STATE_FAIL
        table, finals, folds = parser.table, parser.finals, parser.folds

        return parse

    @classmethod
    def unit(cls, value):
        return Parser(
            [{}],
            {0},
            {0: lambda _: value},
        )

    def map(self, fn):
        def fold_closure(fold):
            return lambda v, i: fn(fold(v, i))

        parser, *_ = self._merge((self,))
        for final in parser.finals:
            fold = parser.folds.get(final)
            if fold is None:
                parser.folds[final] = lambda _, i: fn(i)
            else:
                parser.folds[final] = fold_closure(fold)
        return parser

    @classmethod
    def _merge(cls, parsers, table=None):
        """(Merge|Copy) multiple parsers into single one
        """
        table = table or []
        finals = set()
        epsilons = {}
        folds = {}

        offsets = []
        states_index = [None] * len(table)

        def index_closure(i, m):
            return lambda *_: print(f'{i}: {m}')

        for index, parser in enumerate(parsers):
            offset = len(table)
            offsets.append(offset)
            for tran in parser.table:
                table.append({i: s + offset for i, s in tran.items()})
                states_index.append(index)
            for final in parser.finals:
                finals.add(final + offset)
            for s_in, s_outs in parser.epsilons.items():
                epsilons[s_in + offset] = {s_out + offset for s_out in s_outs}
            for state, fold in parser.folds.items():
                folds[state + offset] = fold

            # FIXME:
            for state in range(len(parser.table)):
                if state == 0:
                    folds[state + offset] = index_closure(index, "start")
                if state in parser.finals:
                    folds[state + offset] = index_closure(index, "stop")

        return (
            Parser(table, finals, folds, epsilons),
            offsets,
            states_index,
        )

    @classmethod
    def choice(cls, parsers):
        assert len(parsers) > 0, 'parsers set must be non empyt'
        parser, offsets, _ = cls._merge(parsers, table=[{}])
        parser.epsilons[0] = set(offsets)
        return parser

    def __or__(self, other):
        return self.choice((self, other))

    @classmethod
    def sequence(cls, parsers):
        assert len(parsers) > 0, 'parsers set must be non empyt'
        parser, offsets, states_index = cls._merge(parsers)
        for final in list(parser.finals):
            index = states_index[final]
            if index + 1 == len(parsers):
                continue
            parser.finals.discard(final)
            parser.epsilons.setdefault(final, set()).add(offsets[index + 1])
        return parser

    def __add__(self, other):
        return self.sequence((self, other))

    def __lshift__(self, other):
        # TODO: correctly discard right-folds
        return (self + other).map(lambda p: p[0])

    def __rshift__(self, other):
        # TODO: correctly discard left-folds
        return (self + other).map(lambda p: p[1])

    def some(self):
        parser, *_ = self._merge((self,))
        for final in parser.finals:
            parser.epsilons.setdefault(final, set()).add(0)
        return parser

    def many(self):
        pass

    def __invert__(self):
        # swap final and not final states?
        raise NotImplementedError()

    def optimize(self):
        """Convert NFA to DFA (eleminate epsilons) using powerset construnction
        """
        # NOTE:
        #  - `n_` contains NFA states (indices in table)
        #  - `d_` constains DFA state (subset of all indices in table)
        # TOOD:
        #  - maybe cache epsilon-closure results, using bit-sets as identificator
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
        d_finals = set()

        # FIXME:
        def fold_closure(folds):
            return lambda value, input: [fold(value, input) for fold in folds]
        d_folds = {}

        d_queue = [d_start]
        d_found = set()
        while d_queue:
            d_state = d_queue.pop()
            # finals
            for n_state in d_state:
                if n_state in self.finals:
                    d_finals.add(d_state)
            # FIXME: folds
            folds = []
            for n_state in d_state:
                fold = self.folds.get(n_state)
                if fold is not None:
                    folds.append(fold)
            if folds:
                d_folds[d_state] = fold_closure(folds)
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
        d_finals_norm = {d_ss_sn[ss] for ss in d_finals}

        # FIXME
        d_folds_norm = {d_ss_sn[ss]: fold for ss, fold in d_folds.items()}

        return Parser(
            d_table_norm,
            d_finals_norm,
            d_folds_norm,
        )

    # DEBUG
    def debug(self, input):
        input = input if isinstance(input, bytes) else input.encode()
        parse = self.compile()

        print(parse(None))
        for i in input:
            print(parse(i))

    def show(self, render=True, size=384):
        import os
        import sys
        from graphviz import Digraph

        dot = Digraph(format='png')
        dot.graph_attr['rankdir'] = 'LR'

        for state in range(len(self.table)):
            attrs = {'shape': 'circle'}
            if state in self.finals:
                attrs['shape'] = 'doublecircle'
            if state in self.folds:
                attrs['color'] = 'blue'
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


def byte(b):
    assert 0 <= b <= 255, f'byte expected: {b}'
    return Parser([{b: 1}, {}], {1})


def match_pred(pred):
    return Parser([{b: 1 for b in range(256) if pred(b)}, {}], {1})


@apply
def utf8():
    # tail byte
    def utf8_tail(shift):
        shift = shift * 6
        return (match_pred(lambda b: b >> 6 == 0b10)
                .map(lambda b: (b & 0b111111) << shift))
    # first byte
    utf8_one = (match_pred(lambda b: b >> 7)
                .map(lambda b: b & 0b1111111))
    utf8_two = (match_pred(lambda b: b >> 5 == 0b110)
                .map(lambda b: (b & 0b11111) << 6))
    utf8_three = (match_pred(lambda b: b >> 4 == 0b1110)
                  .map(lambda b: (b & 0b1111) << 18))
    utf8_four = (match_pred(lambda b: b >> 3 == 0b11110)
                 .map(lambda b: (b & 0b111) << 24))
    return (
        utf8_one |
        utf8_two + utf8_tail(0) |
        utf8_three + utf8_tail(1) + utf8_tail(0) |
        utf8_four + utf8_tail(2) + utf8_tail(1) + utf8_tail(0)
    ).map(lambda args: chr(sum(args)))


@apply
def digit():
    return match_pred(lambda b: ord('0') <= b <= ord('9')).map(lambda b: b - 48)


@apply
def number():
    return digit.some()


def match(bs):
    table = []
    for i, b in enumerate(bs):
        table.append({b: i + 1})
    table.append({})
    return Parser(table, {len(table) - 1})


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


@debug
def main():
    print("parser: (match(b'abc') | match(b'abd')) + match(b'f')")
    p = (match(b'abc') | match(b'abd')) + match(b'f')
    p.show()
    print("optimized:")
    po = p.optimize()
    po.show()

    digit.map(lambda v: v + 1).debug('1')


if __name__ == '__main__':
    # main()
    pass
