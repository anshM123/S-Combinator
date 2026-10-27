"""Clock steering in a parallel-robust counter (main agent). Base counter K0 = S(SS)S(S(S(SSS)))S (runs identically under
both orders, R45). Variants: (a) K0 applied to a clock W (W appended as a last head argument); (b) W substituted for one
S leaf of K0 (each leaf position). For each variant: first step at which the leftmost-outermost run and the parallel head
machine differ (front or list length), within STEPS steps, and the radix law of both opcode words."""
import sys
sys.setrecursionlimit(1000000)
from symb import parse, show
import hc
from parallel_eval import step_fn
from rand_radix import radix
P = step_fn(); STEPS = int(sys.argv[1])
def runs(t):
    start = len(hc.L)
    args, h = hc.spine(hc.from_tuple(t)); lo = list(args); par = list(args); first = None; lo_ops = []; par_ops = []
    for n in range(STEPS):
        if len(lo) < 3 or len(par) < 3: break
        a, b, c = lo[0], lo[1], lo[2]; ch, _ = hc.spine(a); lo_ops.append(len(ch)); lo = ch + [c, hc.app(b, c)] + lo[3:]
        a, b, c = par[0], par[1], par[2]; ch2, _ = hc.spine(a); par_ops.append(len(ch2))
        par = ch2 + [c, hc.app(b, c)] + [P(e) for e in par[3:]]
        if first is None and (len(lo) != len(par) or lo[0] != par[0]): first = n
        if len(hc.L) - start > 4_000_000: break
    return first, n, radix(lo_ops), radix(par_ops)
K0 = parse("S(SS)S(S(S(SSS)))S")
def leaves(t, path=()):
    if t == "S": yield path
    else:
        yield from leaves(t[0], path + (0,)); yield from leaves(t[1], path + (1,))
def subst(t, path, w):
    if not path: return w
    return (subst(t[0], path[1:], w), t[1]) if path[0] == 0 else (t[0], subst(t[1], path[1:], w))
if len(sys.argv) > 2:      # single variant mode: ws, path ('a' = appended)
    ws, path = sys.argv[2], sys.argv[3]; W = parse(ws)
    t = (K0, W) if path == "a" else subst(K0, tuple(int(ch) for ch in path), W)
    f, n, rl, rp = runs(t)
    print(f"W={ws} {'appended' if path == 'a' else 'at leaf ' + path}: first difference at step {f} (of {n} steps); "
          f"radix LO {rl[0] if rl else None}, parallel {rp[0] if rp else None}", flush=True)
    raise SystemExit
import subprocess
for ws in ("SSS(SS)S(SS(SS))", "S(SSS)S(SSS)"):
    for path in ["a"] + ["".join(map(str, p)) for p in leaves(K0)]:
        out = subprocess.run([sys.executable, "-u", __file__, str(STEPS), ws, path], capture_output=True, text=True, timeout=900).stdout
        print(out.strip(), flush=True)
