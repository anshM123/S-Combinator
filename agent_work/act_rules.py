"""Generic activation rules: for closed S-term T, run [T, u, v | r] (u, v, r opaque) until a u- or v-headed element
is at the front.  Print the resulting list (with r at the bottom)."""
import sys, collections
import hm
u = hm.atom("u"); v = hm.atom("v"); r = hm.atom("r")
def act(T, budget=3000):
    st = [r, v, u, T]
    status, n = hm.run(st, budget)
    return status, n, st
if __name__ == "__main__":
    N = int(sys.argv[1])
    out = collections.defaultdict(list)
    for n in range(1, N + 1):
        for T in hm.trees(n):
            status, k, st = act(T)
            if status != "stuck":
                out[status].append(hm.show(T)); continue
            # describe: the list
            out["stuck"].append((hm.show(T), k, hm.show_list(st)))
    print("budget/hnf:", {k: len(v_) for k, v_ in out.items() if k != "stuck"})
    for t, k, s in out["stuck"][:int(sys.argv[2]) if len(sys.argv) > 2 else 60]:
        print(f"{t:20s} {k:4d}  {s}")
