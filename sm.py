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

    table - state transition table: List[Map[Input, State]]
    finals - dictionary of final states: Set[State]
    folds - is a mapping: Map[Tuple[State, State], Result? -> Input -> Result]
    epsilons - epsilon moves: Map[State, Set[State]]
    """
    STATE_START = 0
    STATE_FAIL = -1

    def __init__(self, table, finals, folds=None, *, epsilons=None):
        assert all(-1 <= s < len(table) for ss in table for s in ss.values()),\
            f'invalid transition state found: {table}'
        assert all(-1 <= s <= len(table) for s in finals),\
            f'invalid final state found: {finals}'

        self.table = table
        self.finals = finals
        self.folds = folds or {}
        self.epsilons = epsilons or {}

    def compile(self, greedy=False):
        def parse(input):
            nonlocal state, value

            state_new = table[state].get(input)  # consider using dense arrays?
            if state_new is None:
                state, value = self.STATE_FAIL, None
                return Fail

            # FIXME: handle folds
            """
            fold = folds.get((state, state_new))
            if fold:
                value = fold(value, input)
            else:
                value = input
            """

            state = state_new
            return Final if state in finals else Feed
        state, value = self.STATE_START, None

        parser = self
        if self.epsilons:
            parser = self.optimize()
        table, finals, folds = parser.table, parser.finals, parser.folds

        return parse

    def map(self, fn):
        return self  # FIXME: handle folds

    @classmethod
    def _merge(cls, parsers, table=None, finals=None, epsilons=None):
        """Merge multiple parsers into single one
        """
        table = table or []
        finals = finals or set()
        epsilons = epsilons or {}
        offsets = []
        states_index = []

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

        return offsets, states_index, table, finals, epsilons

    @classmethod
    def choice(cls, parsers):
        assert len(parsers) > 0, 'parsers set must be non empyt'
        offsets, _, table, finals, epsilons = cls._merge(parsers, table=[{}])
        epsilons[0] = set(offsets)
        return Parser(
            table,
            finals,
            folds=None,  # FIXME: handle folds
            epsilons=epsilons,
        )

    def __or__(self, other):
        return self.choice((self, other))

    @classmethod
    def sequence(cls, parsers):
        assert len(parsers) > 0, 'parsers set must be non empyt'
        offsets, states_index, table, finals, epsilons = cls._merge(parsers)
        for final in list(finals):
            index = states_index[final]
            if index + 1 == len(parsers):
                continue
            finals.discard(final)
            epsilons.setdefault(final, set()).add(offsets[index + 1])
        return Parser(
            table,
            finals,
            folds=None,  # FIXME: handle folds
            epsilons=epsilons,
        )

    def __add__(self, other):
        return self.sequence((self, other))

    def __lshift__(self, other):
        # TODO: correctly discard right-folds
        return (self + other).map(lambda p: p[0])

    def __rshift__(self, other):
        # TODO: correctly discard left-folds
        return (self + other).map(lambda p: p[1])

    def many(self):
        _, _, table, finals, epsilons = self._merge((self,))
        for final in finals:
            epsilons.setdefault(final, set()).add(0)
        return Parser(table, finals, folds=None, epsilons=epsilons)

    def __invert__(self):
        raise NotImplementedError()

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
        d_finals = set()

        d_queue = [d_start]
        d_found = set()
        while d_queue:
            d_state = d_queue.pop()

            for n_state in d_state:
                if n_state in self.finals:
                    d_finals.add(d_state)

            n_trans = [self.table[n_state] for n_state in d_state]
            d_tran = {}
            for b in {b for n_tran in n_trans for b in n_tran}:
                d_state_new = epsilon_closure(
                    {n_tran[b] for n_tran in n_trans if b in n_tran})
                if d_state_new not in d_found:
                    d_found.add(d_state_new)
                    d_queue.append(d_state_new)
                d_tran[b] = d_state_new
            d_table[d_state] = d_tran

        # normalize (use indicies instead of sets to identify states)
        d_ss_sn = {d_start: 0}  # state-set -> state-norm
        for d_state in d_table.keys():
            d_ss_sn.setdefault(d_state, len(d_ss_sn))
        d_sn_ss = {v: k for k, v in d_ss_sn.items()}  # state-norm -> state-set
        d_table_norm = [
            {b: d_ss_sn[ss] for b, ss in d_table[d_sn_ss[sn]].items()}
            for sn in d_sn_ss
        ]
        d_finals_norm = {d_ss_sn[ss] for ss in d_finals}

        return Parser(
            d_table_norm,
            d_finals_norm,
            folds=None,  # FIXME: handle folds
        )

    # DEBUG
    def show(self, render=True, size=384):
        import os
        import sys
        from graphviz import Digraph

        dot = Digraph(format='png')
        dot.graph_attr['rankdir'] = 'LR'

        for state in range(len(self.table)):
            if state in self.finals:
                dot.node(str(state), shape='doublecircle')
            else:
                dot.node(str(state), shape='circle')

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
    return match_pred(lambda b: ord('0') <= b <= ord('9'))


@apply
def number():
    return digit + digit.many()


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
    print("parser: match(b'abc') | match(b'abd')")
    p = match(b'abc') | match(b'abd')
    p.show()
    print("optimized:")
    po = p.optimize()
    po.show()


if __name__ == '__main__':
    main()
