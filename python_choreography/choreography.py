from dataclasses import dataclass
from collections import defaultdict
from functools import wraps

views = defaultdict(list)

@dataclass(frozen=True)
class Party:
    name: str

    def __rmatmul__(self, f):
        def wrapped(*args, **kwargs):
            return locally(self, f, *args, **kwargs)
        return wrapped

@dataclass(frozen=True)
class LocatedVal:
    party: str
    val: any

    def __rshift__(self, party_to):
        return send(party_to, self)

    def __str__(self):
        return f'{self.val}@{self.party.name}'

    __repr__ = __str__

def get_val(lv, party):
    if isinstance(lv, LocatedVal):
        assert lv.party == party
        return lv.val
    elif isinstance(lv, (tuple, list)):
        return [get_val(x, party) for x in lv]
    elif isinstance(lv, (int, float)):
        return lv
    else:
        raise Exception(f'Unsupported value for local computation: {lv} : {type(lv)}')

def constant(party, v):
    assert not isinstance(v, LocatedVal)
    return LocatedVal(party, v)

def locally(party, f, *args, **kwargs):
    new_args = [get_val(lv, party) for lv in args]
    new_kwargs = {x: get_val(lv, party) for x, lv in kwargs}
    output = f(*new_args, **new_kwargs)
    return LocatedVal(party, output)

def send(party_to, lv):
    party_from = lv.party
    val = get_val(lv, party_from)
    views[party_to].append(val)
    return LocatedVal(party_to, val)

def unlist(ls):
    assert isinstance(ls, LocatedVal)
    assert isinstance(ls.val, list)
    p = ls.party

    return [LocatedVal(p, x) for x in ls.val]

def untup(ls):
    assert isinstance(ls, LocatedVal)
    assert isinstance(ls.val, tuple)
    p = ls.party

    return tuple([LocatedVal(p, x) for x in ls.val])
