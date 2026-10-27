"""Agent U, obstruction test: the 'no fuel' invariant (Theorem U) on random head runs with opaque data.

(F1) no list element containing a variable lies directly above a closed list element;
(F2) no S-headed subterm (of any element) has a variable-containing spine argument directly followed by a closed one.
Claim (proved in the report): if a head run never opens a variable-headed element and F1, F2 hold initially, they hold
forever.  Consequences: (a) every compound b.c formed when a variable-containing element is opened has BOTH b and c
variable-containing; (b) a clean write c0.t (c0 closed, t data) only arises when a CLOSED element is opened with c0, t
below it; (c) no 'head-style' value S..u c0.. (data u followed by closed c0) and no append t.c0 ever forms.
This script checks F1, F2 after every step and also (a), (b) directly, on random initial lists satisfying F1, F2.
Usage: python agent_u_fuel.py RUNS STEPS SEED [code|data|block]
(block: random check of Lemma U3, the two-above blocking lemma)
"""
import sys, random
sys.setrecursionlimit(100000)
from symb import trees, spine

VARS = ("x", "y")

def hasvar(t, memo):
    """memoised by id; the memo also holds a reference to t, so ids are never recycled while memo lives"""
    k = id(t)
    if k in memo: return memo[k][1]
    if isinstance(t, str): r = t in VARS
    else: r = hasvar(t[0], memo) or hasvar(t[1], memo)
    memo[k] = (t, r)
    return r

def f2_ok(t, memo, seen):
    """every S-headed subterm: no var-containing spine arg directly followed by a closed one"""
    stack = [t]
    while stack:
        u = stack.pop()
        if isinstance(u, str) or id(u) in seen: continue
        seen.add(id(u))
        h, args = spine(u)
        if h == "S":
            for i in range(len(args) - 1):
                if hasvar(args[i], memo) and not hasvar(args[i + 1], memo):
                    return False
        stack.extend(args)
    return True

def inv_ok(K, memo):
    for i in range(len(K) - 1):
        if hasvar(K[i], memo) and not hasvar(K[i + 1], memo): return False
    seen = set()
    return all(f2_ok(e, memo, seen) for e in K)

def rand_closed(maxn):
    n = random.randint(1, maxn)
    return random.choice(trees(n))

def rand_data():
    """a data element satisfying F2: variable, or S-headed with closed args before variable-containing ones"""
    r = random.random()
    if r < 0.5: return random.choice(VARS)
    if r < 0.75:   # S c1 .. cj v  (closed then data)
        args = [rand_closed(3) for _ in range(random.randint(0, 2))] + [random.choice(VARS)]
        t = "S"
        for a in args: t = (t, a)
        return t
    v = random.choice(VARS)        # variable-headed data element  v c1 ... (never opened; F2 not about it)
    t = v
    for _ in range(random.randint(1, 2)): t = (t, rand_closed(3))
    return t

def rand_list(mode):
    if mode == "code":     # closed code on top of data
        return [rand_closed(6) for _ in range(random.randint(1, 4))] + [rand_data() for _ in range(random.randint(1, 3))]
    K = []                 # data-heavy: S-headed data elements (closed args before data args) on top
    for _ in range(random.randint(3, 5)):
        args = [rand_closed(4) for _ in range(random.randint(0, 3))] + [rand_data() for _ in range(random.randint(1, 2))]
        t = "S"
        for a in args: t = (t, a)
        K.append(t)
    return K + [rand_data() for _ in range(random.randint(0, 2))]

def one_run(steps, mode):
    while True:
        K = rand_list(mode); memo = {}
        if inv_ok(K, memo): break
    stats = {"steps": 0, "data_opens": 0, "clean_writes": 0, "viol": 0, "viol_a": 0, "viol_b": 0}
    for _ in range(steps):
        if len(K) < 3: break
        a, b, c = K[0], K[1], K[2]
        h, aa = spine(a)
        if h != "S": break                      # would open a variable-headed element: stop
        if hasvar(a, memo):
            stats["data_opens"] += 1
            if not (hasvar(b, memo) and hasvar(c, memo)): stats["viol_a"] += 1
        if not hasvar(b, memo) and hasvar(c, memo):
            stats["clean_writes"] += 1
            if hasvar(a, memo): stats["viol_b"] += 1
        K = list(aa) + [c, (b, c)] + K[3:]
        stats["steps"] += 1
        if not inv_ok(K, memo):
            stats["viol"] += 1; break
    return stats

def hasv(t, v, memo):
    k = (id(t), v)
    if k in memo: return memo[k][1]
    r = (t == v) if isinstance(t, str) else (hasv(t[0], v, memo) or hasv(t[1], v, memo))
    memo[k] = (t, r)
    return r

def block_run(steps):
    """Lemma U3: once >= 2 elements containing y but not x lie above the topmost x-containing element,
    no x-containing element reaches position 1 before some y-containing element is opened."""
    K = [rand_closed(6) for _ in range(random.randint(0, 3))]
    data = []
    for _ in range(random.randint(2, 4)):
        v = random.choice(VARS)
        t = "S"
        for a in [rand_closed(3) for _ in range(random.randint(0, 2))] + [v]: t = (t, a)
        data.append(t if random.random() < 0.6 else v)
    K += data
    memo = {}
    armed = False; st = {"armed": 0, "viol": 0, "released_by_y_open": 0}
    for _ in range(steps):
        if len(K) < 3: break
        a = K[0]; h, aa = spine(a)
        if h != "S": break
        if hasv(a, "y", memo):
            if armed: st["released_by_y_open"] += 1
            armed = False
        elif armed and hasv(a, "x", memo):
            st["viol"] += 1; break
        K = list(aa) + [K[2], (K[1], K[2])] + K[3:]
        fx = next((i for i, e in enumerate(K) if hasv(e, "x", memo)), None)
        if fx is not None and not armed:
            cnt = sum(1 for e in K[:fx] if hasv(e, "y", memo) and not hasv(e, "x", memo))
            if cnt >= 2: armed = True; st["armed"] += 1
    return st

if __name__ == "__main__" and len(sys.argv) > 4 and sys.argv[4] == "block":
    random.seed(int(sys.argv[3])); tot = {}
    for _ in range(int(sys.argv[1])):
        for k, v in block_run(int(sys.argv[2])).items(): tot[k] = tot.get(k, 0) + v
    print(tot); sys.exit()

if __name__ == "__main__":
    RUNS, STEPS, SEED = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    MODE = sys.argv[4] if len(sys.argv) > 4 else "code"
    random.seed(SEED)
    tot = {}
    for _ in range(RUNS):
        s = one_run(STEPS, MODE)
        for k, v in s.items(): tot[k] = tot.get(k, 0) + v
    print(tot)
