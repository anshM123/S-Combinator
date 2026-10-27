"""Hash-consed head machine (main agent). Terms are ints; 0 = S; atoms are negative ints (opaque).
app(l, r) interns the pair. Used for fast structural identity of front elements."""
import sys
sys.setrecursionlimit(1000000)
L = [None]; R = [None]; TAB = {}
def app(l, r):
    k = (l, r)
    i = TAB.get(k)
    if i is None:
        i = len(L); L.append(l); R.append(r); TAB[k] = i
    return i
def from_tuple(t, memo=None):
    if memo is None: memo = {}
    if t == "S": return 0
    if isinstance(t, str): raise ValueError(t)
    k = id(t)
    if k in memo: return memo[k][1]
    v = app(from_tuple(t[0], memo), from_tuple(t[1], memo)); memo[k] = (t, v); return v
def spine(i):
    a = []
    while i > 0: a.append(R[i]); i = L[i]
    a.reverse(); return a, i          # head is 0 (S) or an atom (< 0)
def size(i, memo={}):
    if i <= 0: return 1
    if i in memo: return memo[i]
    s = size(L[i]) + size(R[i]); memo[i] = s; return s
def show(i):
    if i == 0: return "S"
    if i < 0: return f"a{-i}"
    l, r = L[i], R[i]
    return show(l) + (("(" + show(r) + ")") if r > 0 else show(r))
def call_time(P, cap):
    """generic run of [P, x, y, r1..r6] with atoms; returns T if x·y reaches the front with the tape untouched"""
    X, Y = -1, -2
    stk = [-8, -7, -6, -5, -4, -3, Y, X, P]; floor = 6; XY = app(X, Y)
    for t in range(cap):
        a = stk[-1]
        if a == XY: return t
        args, h = spine(a)
        if h != 0 or len(stk) < 3: return None
        stk.pop(); bb = stk.pop(); cc = stk.pop()
        if len(stk) < floor: return None
        stk.append(app(bb, cc)); stk.append(cc); stk.extend(reversed(args))
    return None
