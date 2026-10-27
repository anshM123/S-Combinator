"""agent_work/hm.py -- small symbolic head machine for S-terms (construction agent).

Terms are hash-consed ints: 0 = S, negative ints = opaque atoms (variables), positive = application nodes.
A *list* L (front first) represents the term S L[0] L[1] ...; the head step is
    [a, b, c] ++ R  =>  args(a) ++ [c, b.c] ++ R          (opcode = |args(a)|)
If the front element has an atom head the run is STUCK (it would have to inspect an unknown term).
If |L| < 3 the term is a head normal form.

Internally lists are Python lists with the FRONT AT THE END (stack top = last element) for speed.
"""
import sys
sys.setrecursionlimit(1000000)

L = [None]; R = [None]; TAB = {}
NAMES = {}            # atom id -> name

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
    """current table size; pass to truncate() to forget every node created afterwards (memory control)."""
    return len(L)

def truncate(m):
    for i in range(m, len(L)):
        TAB.pop((L[i], R[i]), None)
        _size.pop(i, None)
    del L[m:]; del R[m:]

_atom_by_name = {}
def atom(name):
    if name in _atom_by_name:
        return _atom_by_name[name]
    i = -(len(_atom_by_name) + 1)
    _atom_by_name[name] = i; NAMES[i] = name
    return i

def spine(i):
    a = []
    while i > 0:
        a.append(R[i]); i = L[i]
    a.reverse()
    return a, i                     # head is 0 (S) or an atom (<0)

def head(i):
    while i > 0:
        i = L[i]
    return i

def build(h, args):
    t = h
    for a in args:
        t = app(t, a)
    return t

_size = {}
def size(i):
    if i <= 0: return 1
    s = _size.get(i)
    if s is None:
        # iterative to avoid deep recursion on left spines
        stack = [i]
        while stack:
            j = stack[-1]
            if j <= 0 or j in _size:
                stack.pop(); continue
            l, r = L[j], R[j]
            pend = [x for x in (l, r) if x > 0 and x not in _size]
            if pend:
                stack.extend(pend); continue
            _size[j] = (1 if l <= 0 else _size[l]) + (1 if r <= 0 else _size[r])
            stack.pop()
        s = _size[i]
    return s

def show(i, names=None):
    if i == 0: return "S"
    if i < 0:
        n = (names or NAMES).get(i, f"a{-i}")
        return n
    args, h = spine(i)
    s = show(h, names)
    for a in args:
        if a == 0 or (a < 0 and len(show(a, names)) == 1):
            s += show(a, names)
        else:
            s += "(" + show(a, names) + ")"
    return s

def parse(s):
    """S-terms; any other single character (letter) is an atom; parentheses group; juxtaposition = application."""
    pos = [0]
    s = s.replace(" ", "")
    def at():
        c = s[pos[0]]
        if c == "(":
            pos[0] += 1; t = term(); assert s[pos[0]] == ")"; pos[0] += 1; return t
        pos[0] += 1
        if c == "S": return 0
        return atom(c)
    def term():
        t = at()
        while pos[0] < len(s) and s[pos[0]] != ")":
            t = app(t, at())
        return t
    t = term()
    assert pos[0] == len(s), s
    return t

def tolist(t):
    """term -> stack (front at end).  t must be S-headed."""
    args, h = spine(t)
    assert h == 0
    return list(reversed(args))

def fromlist(st):
    return build(0, list(reversed(st)))

def step(st):
    """one head step in place; returns opcode, or -1 if hnf, or ('stuck', atom) as -2."""
    if len(st) < 3: return -1
    a = st[-1]
    args, h = spine(a)
    if h != 0: return -2
    st.pop(); b = st.pop(); c = st.pop()
    st.append(app(b, c)); st.append(c)
    st.extend(reversed(args))
    return len(args)

def run(st, budget, trace=None):
    """run until hnf / stuck / budget.  returns (status, steps).  st modified in place.
    trace: optional list to receive opcodes."""
    for t in range(budget):
        if len(st) < 3: return ("hnf", t)
        a = st[-1]
        args, h = spine(a)
        if h != 0: return ("stuck", t)
        st.pop(); b = st.pop(); c = st.pop()
        st.append(app(b, c)); st.append(c)
        st.extend(reversed(args))
        if trace is not None: trace.append(len(args))
    if len(st) < 3: return ("hnf", budget)
    return ("budget", budget)

def show_list(st, names=None, maxn=12):
    items = [show(x, names) for x in reversed(st[-maxn:])] if len(st) > maxn else [show(x, names) for x in reversed(st)]
    tail = "" if len(st) <= maxn else f" ...(+{len(st)-maxn})"
    return "[" + ", ".join(items) + "]" + tail

def behaviour(T, nvars=6, budget=10000):
    """head-reduce T x1 ... xn (T closed S-term) until the front is atom-headed / hnf / budget.
    Returns (status, steps, resulting term as int)."""
    xs = [atom("x%d" % (i + 1)) for i in range(nvars)]
    args, h = spine(T)
    st = list(reversed(args + xs))
    status, n = run(st, budget)
    return status, n, fromlist_term(st)

def fromlist_term(st):
    """the term represented by stack st: S applied to the list -- but if the front is atom-headed show it as that
    application.  We return the term  front . rest  (front applied to the remaining list), which for an S-headed
    representation is just S L0 L1 ...; for a stuck list we return  (L0) L1 L2 ... where L0 is atom-headed? No:
    the list [L0, L1, ...] means S L0 L1 ..., i.e. L0 L2 (L1 L2) ... only after a step.  For a stuck list the term
    is still S L0 L1 L2 ...; we return that."""
    return build(0, list(reversed(st)))

# ---------------------------------------------------------------- enumeration
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

def has_redex(t):
    stack = [t]
    while stack:
        i = stack.pop()
        if i <= 0: continue
        args, h = spine(i)
        if h == 0 and len(args) >= 3: return True
        stack.extend(args)
    return False

if __name__ == "__main__":
    t = parse("SSS(SS)S(SS(SS))")
    st = tolist(t)
    tr = []
    print(run(st, 400, tr), tr[:40])
