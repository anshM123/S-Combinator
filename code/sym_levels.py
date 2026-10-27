"""Exact symbolic analysis of the binary counter SSS(SS)S(SS(SS)) (main agent).

Level tokens ('P', d) denote P_{j+d} for a symbolic level j >= 0 (case split when opened):
  P_0 = S·L0,   P_{m+1} = S·U_m,   U_m = S S P_m R_m,   R_m = S·(S S W P_m),   W = SS,  L0 = S S b c.
Opaque arguments are strings other than 'S' (a branch that opens one is reported as 'needs <var>').
Starting from a configuration (list), the engine runs head steps; opening a token ('P', d) with level j+d branches on
j+d = 0 (only possible when the constraint allows) or >= 1, recording the constraint. Used to derive the call rules.
"""
import sys
sys.setrecursionlimit(1000000)
from symb import parse, show as _show

b = parse("S(SS(SS))"); c = parse("S(S(SS)S)(SS(SS))"); W = ("S", "S")
L0 = ((("S", "S"), b), c)

def tok(d): return ("P", d)
def is_tok(t): return isinstance(t, tuple) and len(t) == 2 and t[0] == "P" and isinstance(t[1], int)

def U(d):  return ((("S", "S"), tok(d)), R(d))       # S S P R
def R(d):  return ("S", ((("S", "S"), W), tok(d)))    # S (S S W P)

def spine(t):
    args = []
    while isinstance(t, tuple) and not is_tok(t):
        args.append(t[1]); t = t[0]
    args.reverse(); return t, args

def children(head, args, j_min):
    """children of the front element; returns list of (children, new_j_min, label) branches or None if stuck"""
    if head == "S": return [(args, j_min, "")]
    if is_tok(head):
        d = head[1]
        out = []
        # level = j + d ; branch level == 0 (needs j == -d, only if -d >= j_min) and level >= 1
        if j_min <= -d:     # level 0 possible (j = -d)
            out.append(([L0] + args, j_min, f"j={-d}" if -d >= 0 else "x"))
        need = max(j_min, 1 - d)
        out.append(([U(d - 1)] + args, need, f"j>={need}"))
        return out
    return None   # opaque variable at the head

def show(t):
    if is_tok(t): return f"P[j{t[1]:+d}]" if t[1] else "P[j]"
    if t == "S": return "S"
    if isinstance(t, str): return t
    for name, v in (("b", b), ("c", c), ("W", W), ("L0", L0)):
        if t == v: return name
    h, args = spine(t)
    return show(h) + "".join(("(" + show(a) + ")") if isinstance(a, tuple) else show(a) for a in args)

def step(K, j_min):
    """all branches of one head step: list of (newK, j_min, label)"""
    if len(K) < 3: return []
    h, args = spine(K[0])
    br = children(h, args, j_min)
    if br is None: return None
    return [(ch + [K[2], (K[1], K[2])] + K[3:], jm, lab) for (ch, jm, lab) in br]
