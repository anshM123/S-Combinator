"""Joint (L36, M35) classes for dm.py terms, using the main agent's model files (read-only)."""
import sys, re
import numpy as np
sys.setrecursionlimit(1000000)
from dm import L, R, app
def load(path):
    classes, hn, rows = [], [], []
    in_tab = False
    for line in open(path):
        if line.startswith("class "):
            m = re.match(r"class (\d+) HN=(\d) count (\d+) ctxHN (\d+) rep (\S+)", line)
            classes.append(m.group(5)); hn.append(int(m.group(2)))
        elif line.startswith("# product table"):
            in_tab = True
        elif line.startswith("#"):
            in_tab = False
        elif in_tab and line.strip():
            rows.append([int(v) for v in line.split()])
    return classes, np.array(hn), np.array(rows, dtype=np.int64)
BASE = "C:/Users/anshm/Downloads/money problems/data/"
Lr, LF, LT = load(BASE + "model36_leftpath.txt")
Mr, MF, MT = load(BASE + "model35_hn.txt")
sL, sM = Lr.index("S"), Mr.index("S")
LTl = LT.tolist(); MTl = MT.tolist(); LFl = LF.tolist(); MFl = MF.tolist()
_C = {}
def cls(i):
    """joint class of a CLOSED term id (no atoms)"""
    if i == 0: return (sL, sM)
    r = _C.get(i)
    if r is not None: return r
    st = [i]
    while st:
        j = st[-1]
        if j == 0 or j in _C: st.pop(); continue
        l, rr = L[j], R[j]
        pend = [k for k in (l, rr) if k != 0 and k not in _C]
        if pend: st.extend(pend); continue
        a = (sL, sM) if l == 0 else _C[l]; b = (sL, sM) if rr == 0 else _C[rr]
        _C[j] = (LTl[a[0]][b[0]], MTl[a[1]][b[1]]); st.pop()
    return _C[i]
def clear_cache(m):
    for k in [k for k in _C if k >= m]: del _C[k]
COMPONENT = {(14, 28), (14, 26)}
