"""agent_work_U/dm.py -- the DESCENT MACHINE (leftmost-outermost evaluation along the leftmost Boehm-tree path).

Terms are hash-consed ints: 0 = S, negative ints = opaque atoms, positive = application nodes (L[i], R[i]).
A state is the term S e1 ... en, kept as a Python list with the FRONT AT THE END (stack top = last element).

DM rules (leftmost-outermost reduction restricted to the leftmost path):
  |L| >= 3 : [a, b, c | R]  ->  ch(a) ++ [c, b.c | R]          (head step; a must be S-headed)
  |L| == 2 : [c, d]         ->  ch(c)                          (hnf S c d: evaluation descends into c, d is frozen)
  |L| == 1 : [c]            ->  ch(c)                          (hnf S c)
  |L| == 0 :  the leftmost path ends at the leaf S              ('end')
If the element to be opened is atom-headed the run is STUCK (the real datum would now be executed): we return the
stuck state as (atom, args) meaning the term  atom . args[0] . args[1] ...  (args in application order).
"""
import sys
sys.setrecursionlimit(1000000)

L = [None]; R = [None]; TAB = {}
NAMES = {}

def app(l, r):
    k = (l, r)
    i = TAB.get(k)
    if i is None:
        i = len(L); L.append(l); R.append(r); TAB[k] = i
    return i

def apps(*xs):
    t = xs[0]
    for x in xs[1:]:
        t = app(t, x)
    return t

def mark():
    return len(L)

def truncate(m):
    for i in range(m, len(L)):
        TAB.pop((L[i], R[i]), None)
        _sz.pop(i, None)
    del L[m:]; del R[m:]

_atoms = {}
def atom(name):
    if name in _atoms: return _atoms[name]
    i = -(len(_atoms) + 1); _atoms[name] = i; NAMES[i] = name
    return i

def spine(i):
    a = []
    while i > 0:
        a.append(R[i]); i = L[i]
    a.reverse()
    return a, i

def head(i):
    while i > 0: i = L[i]
    return i

def build(h, args):
    t = h
    for a in args: t = app(t, a)
    return t

_sz = {}
def size(i):
    if i <= 0: return 1
    s = _sz.get(i)
    if s is not None: return s
    st = [i]
    while st:
        j = st[-1]
        if j <= 0 or j in _sz: st.pop(); continue
        l, r = L[j], R[j]
        pend = [x for x in (l, r) if x > 0 and x not in _sz]
        if pend: st.extend(pend); continue
        _sz[j] = (1 if l <= 0 else _sz[l]) + (1 if r <= 0 else _sz[r]); st.pop()
    return _sz[i]

def show(i, names=None, maxlen=400):
    out = []
    def rec(i):
        if sum(len(x) for x in out) > maxlen: return
        if i == 0: out.append("S"); return
        if i < 0: out.append((names or NAMES).get(i, "a%d" % -i)); return
        args, h = spine(i)
        rec(h)
        for a in args:
            if a == 0 or a < 0: rec(a)
            else:
                out.append("("); rec(a); out.append(")")
    rec(i)
    s = "".join(out)
    return s if len(s) <= maxlen else s[:maxlen] + "..."

def parse(s, env=None):
    """S-terms; uppercase S is the combinator; any other letter is an atom (or env[name] if given)."""
    s = s.replace(" ", ""); pos = [0]
    def at():
        c = s[pos[0]]
        if c == "(":
            pos[0] += 1; t = term(); assert s[pos[0]] == ")"; pos[0] += 1; return t
        pos[0] += 1
        if c == "S": return 0
        if env and c in env: return env[c]
        return atom(c)
    def term():
        t = at()
        while pos[0] < len(s) and s[pos[0]] != ")":
            t = app(t, at())
        return t
    t = term(); assert pos[0] == len(s), s
    return t

def to_list(t):
    """term (S-headed) -> DM list (front at end)."""
    args, h = spine(t)
    assert h == 0, "not S-headed"
    return list(reversed(args))

def dm_run(st, budget, trace=None, rounds=None):
    """Run the DM on list st (front at end; modified in place).
    Returns ('stuck', atom, args, steps) | ('end', None, None, steps) | ('budget', None, None, steps).
    trace: optional list receiving ('h', opcode) for head steps and ('d', k) for descents (k = list length before).
    rounds: optional list receiving the term opened at each descent (the successive leftmost-path states)."""
    for t in range(budget):
        n = len(st)
        if n >= 3:
            a = st[-1]
            args, h = spine(a)
            if h != 0:
                # the S-redex S a b c fires: a c (b c) R...; a = atom . args, so the new state is
                # atom . args . c . (b c) . R  (head atom: the datum would now be executed)
                b = st[-2]; c = st[-3]
                rest = list(reversed(st[:-3]))
                return ("stuck", h, args + [c, app(b, c)] + rest, t + 1)
            st.pop(); b = st.pop(); c = st.pop()
            st.append(app(b, c)); st.append(c)
            st.extend(reversed(args))
            if trace is not None: trace.append(('h', len(args)))
        elif n >= 1:
            c = st[-1]
            if rounds is not None: rounds.append(c)
            args, h = spine(c)
            if h != 0:
                return ("stuck", h, args, t)
            st.clear(); st.extend(reversed(args))
            if trace is not None: trace.append(('d', n))
        else:
            return ("end", None, None, t)
    return ("budget", None, None, budget)

def dm_term(t, budget, trace=None, rounds=None):
    """run the DM on the state term t (any term; if atom-headed it is immediately stuck)."""
    args, h = spine(t)
    if h != 0:
        return ("stuck", h, args, 0)
    st = list(reversed(args))
    return dm_run(st, budget, trace, rounds)

def stuck_term(res):
    """rebuild the stuck state as a term atom.args..."""
    _, h, args, _ = res
    return build(h, args)

# ---------------------------------------------------------------- enumeration of closed terms
_trees = {1: [0]}
def trees(n):
    if n in _trees: return _trees[n]
    out = []
    for k in range(1, n):
        for l in trees(k):
            for r in trees(n - k):
                out.append(app(l, r))
    _trees[n] = out
    return out

if __name__ == "__main__":
    X, Y, Z = atom("X"), atom("Y"), atom("Z")
    for s in ["SSXY", "S(SS)XY", "SSSSZ", "S(SX)Y", "S(S(SS))XY", "SS(SS)XY"]:
        t = parse(s)
        r = dm_term(t, 100)
        print(s, "=>", r[0], show(stuck_term(r)) if r[0] == "stuck" else "", "steps", r[3])
