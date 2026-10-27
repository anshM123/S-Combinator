"""Leftmost-innermost single-step evolution of an S-term (tree terms as nested tuples for clarity)."""
import sys
sys.setrecursionlimit(100000)
def parse(s):
    s = s.replace(" ", ""); pos = [0]
    def at():
        c = s[pos[0]]
        if c == "(":
            pos[0] += 1; t = term(); pos[0] += 1; return t
        pos[0] += 1; return "S"
    def term():
        t = at()
        while pos[0] < len(s) and s[pos[0]] != ")": t = (t, at())
        return t
    return term()
def show(t):
    if t == "S": return "S"
    f, a = t
    return show(f) + (show(a) if a == "S" else "(" + show(a) + ")")
def is_redex(t):
    return isinstance(t, tuple) and isinstance(t[0], tuple) and isinstance(t[0][0], tuple) and t[0][0][0] == "S"
def li_step(t, depth=0):
    """returns (new_term, depth_of_contracted_redex) or None if normal form"""
    if t == "S": return None
    f, a = t
    r = li_step(f, depth + 1)
    if r is not None: return ((r[0], a), r[1])
    r = li_step(a, depth + 1)
    if r is not None: return ((f, r[0]), r[1])
    if is_redex(t):
        x = t[0][0][1]; y = t[0][1]; z = t[1]
        return (((x, z), (y, z)), depth)
    return None
def size(t):
    st = [t]; n = 0
    while st:
        u = st.pop()
        if u == "S": n += 1
        else: st.append(u[0]); st.append(u[1])
    return n
if __name__ == "__main__":
    t = parse(sys.argv[1]); N = int(sys.argv[2])
    depths = []
    for i in range(N):
        r = li_step(t)
        if r is None: print("normal form at", i); break
        t, d = r; depths.append(d)
        if size(t) > 200000: print("size cap at", i); break
    import collections
    c = collections.Counter(depths)
    print("steps", len(depths), "depth histogram (first 12):", sorted(c.items())[:12], "max", max(depths) if depths else None)
    print("last 40 depths:", depths[-40:])
    print("size", size(t))
