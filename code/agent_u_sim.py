"""Concrete hash-consed head machine for S-terms (agent U tools).

Terms are integers: 0 = S, other ids are applications (L[id], R[id]); app() is hash-consed, so huge shared terms
(duplication by S) cost O(1) per step.  The head machine works on a list K (top first) stored reversed (top = end):
  [a, b, c] ++ R  ->  ch(a) ++ [c, b.c] ++ R.
Utilities: parse/show (with a naming dictionary for recognised subterms such as nests), spine, size (leaves).
"""
import sys
sys.setrecursionlimit(1000000)

L = [-1]; R = [-1]; _memo = {}
S = 0

def app(f, a):
    k = (f, a)
    r = _memo.get(k)
    if r is None:
        r = len(L); L.append(f); R.append(a); _memo[k] = r
    return r

def apps(*xs):
    t = xs[0]
    for x in xs[1:]:
        t = app(t, x)
    return t

def build(head, args):
    t = head
    for a in args:
        t = app(t, a)
    return t

def spine(t):
    args = []
    while t != 0:
        args.append(R[t]); t = L[t]
    args.reverse()
    return args

_size = {0: 1}
def size(t):
    st = [t]
    while st:
        u = st[-1]
        if u in _size: st.pop(); continue
        l, r = L[u], R[u]
        if l in _size and r in _size:
            _size[u] = _size[l] + _size[r]; st.pop()
        else:
            if l not in _size: st.append(l)
            if r not in _size: st.append(r)
    return _size[t]

def parse(s):
    """S-terms written with S and parentheses, application left-assoc; names in NAMES may be used as atoms
    when written in square brackets, e.g. [N3]."""
    pos = [0]
    def atom():
        c = s[pos[0]]
        if c == "(":
            pos[0] += 1; t = term(); pos[0] += 1; return t
        if c == "[":
            j = s.index("]", pos[0]); name = s[pos[0] + 1:j]; pos[0] = j + 1; return NAMES[name]
        pos[0] += 1
        assert c == "S", c
        return 0
    def term():
        t = atom()
        while pos[0] < len(s) and s[pos[0]] != ")":
            if s[pos[0]] == " ": pos[0] += 1; continue
            t = app(t, atom())
        return t
    return term()

NAMES = {}

def show(t, names=None, maxlen=400):
    names = names or {}
    out = []
    def go(u, top):
        if len(out) > maxlen: return
        if u in names: out.append(names[u]); return
        if u == 0: out.append("S"); return
        args = spine(u)
        if not top: out.append("(")
        out.append("S")
        for a in args:
            if a == 0: out.append("S")
            elif a in names: out.append(names[a] if len(names[a]) == 1 else " " + names[a] + " ")
            else: go(a, False)
        if not top: out.append(")")
    go(t, True)
    s = "".join(out)
    return s if len(s) <= maxlen else s[:maxlen] + "..."

def run(K, steps, trace=None):
    """K: list top first. Returns (final list top first, steps done, status)."""
    st = list(reversed(K))
    for n in range(steps):
        if len(st) < 3:
            return list(reversed(st)), n, "hnf"
        a = st.pop(); b = st.pop(); c = st.pop()
        st.append(app(b, c)); st.append(c)
        st.extend(reversed(spine(a)))
        if trace is not None: trace(n + 1, st)
    return list(reversed(st)), steps, "running"

if __name__ == "__main__":
    t = parse("SSS(S(SSS))S")
    K = spine(t)
    def tr(n, st):
        if n <= 60:
            print(n, [show(x, maxlen=60) for x in reversed(st[-8:])], len(st))
    run(K, 60, tr)
