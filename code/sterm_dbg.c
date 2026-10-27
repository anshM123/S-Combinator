/* sterm.c -- research toolkit for pure S-combinator terms.
 *
 * Terms are hash-consed binary application trees over the single leaf S (node 0).
 * Rule: S x y z -> x z (y z).
 *
 * Modes (argv[1]):
 *   hnf   <term> [maxsteps]            head-reduce to head normal form (root spine <= 2 args)
 *   nf    <term> [maxsteps]            normal form via repeated head normalization (sharing)
 *   bt    <term> <depth> [maxsteps]    Boehm-tree approximation (CL head normal forms)
 *   lo    <term> <steps> <outfile>     leftmost-outermost step sequence, writes leaf counts
 *   trace <term> <steps>               show the head-reduction stack (top first) per step
 *   enum  <n> <lo> <hi> <hsteps> <nsteps> <outfile>
 *                                      classify all terms with n leaves, index range [lo,hi)
 *
 * Built with Lean's bundled clang (no libc headers available, so libc is declared by hand).
 */
#include <stdint.h>
#include <stddef.h>

typedef struct _iobuf FILE;
int printf(const char *, ...);
int fprintf(FILE *, const char *, ...);
int fputs(const char *, FILE *);
int fflush(FILE *);
void *malloc(size_t);
void *calloc(size_t, size_t);
void *realloc(void *, size_t);
void free(void *);
FILE *fopen(const char *, const char *);
int fclose(FILE *);
long long strtoll(const char *, char **, int);
size_t strlen(const char *);
int strcmp(const char *, const char *);
void *memset(void *, int, size_t);
void *memcpy(void *, const void *, size_t);
void exit(int);
char *fgets(char *, int, FILE *);
int strncmp(const char *, const char *, size_t);

typedef uint32_t T;
#define NIL 0xFFFFFFFFu

/* ---------------- node store ---------------- */
static T *NL, *NR;
static uint64_t *NSZ;   /* leaf count (number of S), saturating */
static uint32_t *NSP;   /* spine length = number of arguments of the head S, saturating */
static uint8_t *NNF;    /* 1 iff normal form */
static T nnodes, cap;
static T *HT;
static uint32_t *HG, gen = 1;
static uint64_t hmask;
static int overflow;

static void die(const char *m) { printf("fatal: %s\n", m); fflush(0); exit(2); }

static void store_init(T c) {
    cap = c;
    NL = malloc(sizeof(T) * (size_t)c); NR = malloc(sizeof(T) * (size_t)c);
    NSZ = malloc(8 * (size_t)c); NSP = malloc(4 * (size_t)c); NNF = malloc((size_t)c);
    uint64_t hs = 1; while (hs < 2ull * c) hs <<= 1;
    hmask = hs - 1;
    HT = malloc(sizeof(T) * (size_t)hs); HG = calloc((size_t)hs, 4);
    if (!NL || !NR || !NSZ || !NSP || !NNF || !HT || !HG) die("alloc");
    NL[0] = NR[0] = NIL; NSZ[0] = 1; NSP[0] = 0; NNF[0] = 1; nnodes = 1;
}
static void store_reset(void) { nnodes = 1; gen++; overflow = 0; if (gen == 0) { memset(HG, 0, 4 * (hmask + 1)); gen = 1; } }

static inline uint64_t hsh(T l, T r) {
    uint64_t x = ((uint64_t)l << 32) | r;
    x ^= x >> 33; x *= 0xff51afd7ed558ccdull; x ^= x >> 33; x *= 0xc4ceb9fe1a85ec53ull; x ^= x >> 33;
    return x;
}
static T app(T l, T r) {
    if (overflow) return 0;
    uint64_t s = hsh(l, r) & hmask;
    while (HG[s] == gen) {
        T id = HT[s];
        if (NL[id] == l && NR[id] == r) return id;
        s = (s + 1) & hmask;
    }
    if (nnodes >= cap) { overflow = 1; return 0; }
    T id = nnodes++;
    NL[id] = l; NR[id] = r;
    uint64_t z = NSZ[l] + NSZ[r]; if (z < NSZ[l]) z = ~0ull; NSZ[id] = z;
    uint32_t sp = NSP[l] + 1; if (sp == 0) sp = 0xFFFFFFFFu; NSP[id] = sp;
    NNF[id] = NNF[l] && NNF[r] && sp <= 2;
    HG[s] = gen; HT[s] = id;
    return id;
}

/* ---------------- parse / print ---------------- */
static const char *pp;
static T parse_term(void);
static T parse_atom(void) {
    while (*pp == ' ') pp++;
    if (*pp == 'S' || *pp == 's') { pp++; return 0; }
    if (*pp == '(') { pp++; T t = parse_term(); while (*pp == ' ') pp++; if (*pp != ')') die("expected )"); pp++; return t; }
    die("bad term syntax");
    return 0;
}
static T parse_term(void) {
    T t = parse_atom();
    for (;;) {
        while (*pp == ' ') pp++;
        if (*pp == 'S' || *pp == 's' || *pp == '(') t = app(t, parse_atom()); else break;
    }
    return t;
}
static T parse(const char *s) { pp = s; T t = parse_term(); if (*pp) die("trailing junk"); return t; }

static char *pbuf; static size_t plen, pcap, plimit = 4000;
static void pc(char c) { if (plen + 2 >= pcap) { pcap = pcap ? pcap * 2 : 1024; pbuf = realloc(pbuf, pcap); } pbuf[plen++] = c; pbuf[plen] = 0; }
static void pr_rec(T t) {
    if (plen > plimit) return;
    /* t = S a1 ... ak ; print S then args, compound args parenthesized */
    T args[64]; T *a = args; size_t k = 0, acap = 64; T x = t;
    while (x != 0) { if (k == acap) { T *na = malloc(sizeof(T) * acap * 2); memcpy(na, a, sizeof(T) * k); if (a != args) free(a); a = na; acap *= 2; } a[k++] = NR[x]; x = NL[x]; }
    pc('S');
    for (size_t i = k; i-- > 0;) {
        if (plen > plimit) break;
        if (a[i] == 0) pc('S'); else { pc('('); pr_rec(a[i]); pc(')'); }
    }
    if (a != args) free(a);
}
static const char *show(T t) { plen = 0; pc(0); plen = 0; pbuf[0] = 0; pr_rec(t); if (plen > plimit) { pc('.'); pc('.'); pc('.'); } return pbuf; }

/* ---------------- head reduction ---------------- */
static T *ST; static size_t stn, stcap;
static inline void push(T x) { if (stn == stcap) { stcap = stcap ? stcap * 2 : 1 << 16; ST = realloc(ST, sizeof(T) * stcap); if (!ST) die("stack alloc"); } ST[stn++] = x; }
static inline void push_args(T a) { while (a != 0) { push(NR[a]); a = NL[a]; } }

static uint64_t hsteps_total;
/* returns 1 hnf reached (*res set), 0 step budget exhausted, -1 node overflow, -2 stack limit */
static int hnf(T t, uint64_t maxsteps, size_t maxstack, uint64_t *steps_out, T *res) {
    stn = 0; push_args(t);
    uint64_t steps = 0;
    while (stn >= 3) {
        if (steps >= maxsteps) { *steps_out = steps; return 0; }
        T a = ST[stn - 1], b = ST[stn - 2], c = ST[stn - 3]; stn -= 3;
        T bc = app(b, c); if (overflow) { *steps_out = steps; return -1; }
        push(bc); push(c); push_args(a);
        steps++;
        if (stn > maxstack) { *steps_out = steps; return -2; }
    }
    hsteps_total += steps;
    T r = 0; for (size_t i = stn; i-- > 0;) r = app(r, ST[i]);
    *steps_out = steps; *res = r;
    return overflow ? -1 : 1;
}

/* ---------------- normal form with memo (sharing) ---------------- */
static T *MEMO; static uint32_t *MEMOG;
static uint64_t nf_budget;    /* total head steps allowed */
static int nf_fail;
static size_t nf_maxstack = 1u << 26;
static T nf_rec(T t, int depth) {
    if (nf_fail) return 0;
    if (NNF[t]) return t;
    if (MEMOG[t] == gen) return MEMO[t];
    if (depth > 200000) { nf_fail = 3; return 0; }
    uint64_t st; T h;
    int r = hnf(t, nf_budget, nf_maxstack, &st, &h);
    if (r != 1) { nf_fail = r == 0 ? 1 : 2; return 0; }
    nf_budget -= st;
    T res;
    if (h == 0) res = 0;
    else if (NL[h] == 0) { T a = nf_rec(NR[h], depth + 1); res = app(0, a); }
    else { T a = nf_rec(NR[NL[h]], depth + 1); T b = nf_rec(NR[h], depth + 1); res = app(app(0, a), b); }
    if (overflow) { nf_fail = 2; return 0; }
    if (t < cap) { MEMO[t] = res; MEMOG[t] = gen; }
    return res;
}
static void memo_init(void) { MEMO = malloc(sizeof(T) * (size_t)cap); MEMOG = calloc((size_t)cap, 4); if (!MEMO || !MEMOG) die("memo alloc"); }

/* ---------------- Boehm tree approximation ---------------- */
static uint64_t bt_steps;
static void ps(const char *s) { while (*s) pc(*s++); }
static void bt_rec(T t, int d) {
    if (d == 0) { ps("."); return; }
    uint64_t st; T h;
    int r = hnf(t, bt_steps, 1u << 26, &st, &h);
    if (r != 1) { ps("?"); return; }
    if (h == 0) { ps("S"); return; }
    if (NL[h] == 0) { ps("S("); bt_rec(NR[h], d - 1); ps(")"); return; }
    T a = NR[NL[h]], b = NR[h];
    ps("S("); bt_rec(a, d - 1); ps(")("); bt_rec(b, d - 1); ps(")");
}

/* Boehm-tree depth with memo: depth of the non-bottom part, capped at D.
 * A node whose head reduction exceeds the step budget counts as bottom (btd_fail set if the
 * failure was a node/stack overflow rather than the step budget). */
static int btd_fail;
static int btd_rec(T t, int r, uint64_t hs) {
    if (r == 0) return 0;
    uint64_t st; T h;
    int rc = hnf(t, hs, 1u << 22, &st, &h);
    if (rc != 1) { if (rc < 0) btd_fail = 1; return 0; }
    if (h == 0) return 1;
    if (NL[h] == 0) return 1 + btd_rec(NR[h], r - 1, hs);
    T a = NR[NL[h]], b = NR[h];
    int da = btd_rec(a, r - 1, hs);
    int db = (da < r - 1) ? btd_rec(b, r - 1, hs) : 0;
    return 1 + (da > db ? da : db);
}
static int btdepth(T t, int D, uint64_t hs) { btd_fail = 0; return btd_rec(t, D, hs); }

/* memoized hnf (store never reset in this mode); NIL = no hnf within budget */
static T *HM; static uint32_t *HMG;
static T hnf_memo(T t, uint64_t hs) {
    if (HMG[t] == gen) return HM[t];
    uint64_t st; T h; int rc = hnf(t, hs, 1u << 22, &st, &h);
    T res = rc == 1 ? h : NIL;
    if (t < cap) { HM[t] = res; HMG[t] = gen; }
    return res;
}
/* BT signature to depth k: hash of the depth-k truncation */
#define SIGN (1u << 22)
static uint64_t SGK[SIGN], SGV[SIGN];
static uint64_t mix64(uint64_t x) { x ^= x >> 31; x *= 0x7fb5d329728ea185ull; x ^= x >> 27; x *= 0x81dadef4bc2dd44dull; x ^= x >> 33; return x; }
static uint64_t btsig(T t, int k, uint64_t hs) {
    if (k == 0) return 0x1234567ull;
    uint64_t key = ((uint64_t)t << 6) | (uint64_t)k, s = mix64(key) & (SIGN - 1);
    while (SGK[s]) { if (SGK[s] == key + 1) return SGV[s]; s = (s + 1) & (SIGN - 1); }
    T h = hnf_memo(t, hs);
    uint64_t v;
    if (h == NIL) v = 0xB0770Bull;
    else if (h == 0) v = 0x51ull;
    else if (NL[h] == 0) v = mix64(0x52ull ^ btsig(NR[h], k - 1, hs));
    else v = mix64(0x53ull ^ mix64(btsig(NR[NL[h]], k - 1, hs)) * 3 ^ btsig(NR[h], k - 1, hs));
    s = mix64(key) & (SIGN - 1);
    while (SGK[s]) s = (s + 1) & (SIGN - 1);
    SGK[s] = key + 1; SGV[s] = v;
    return v;
}

/* ---------------- leftmost-outermost single step ---------------- */
static T *ABUF; static size_t abcap;
static T lo_step(T t) {
    if (NNF[t]) return t;
    if (NSP[t] >= 3) {
        size_t k = 0; T x = t;
        while (x != 0) { if (k == abcap) { abcap = abcap ? abcap * 2 : 1024; ABUF = realloc(ABUF, sizeof(T) * abcap); } ABUF[k++] = NR[x]; x = NL[x]; }
        /* ABUF[k-1]=a1, ABUF[k-2]=a2, ABUF[k-3]=a3 */
        T a1 = ABUF[k - 1], a2 = ABUF[k - 2], a3 = ABUF[k - 3];
        T r = app(app(a1, a3), app(a2, a3));
        for (size_t i = k - 3; i-- > 0;) r = app(r, ABUF[i]);
        return r;
    }
    if (NSP[t] == 1) return app(0, lo_step(NR[t]));
    /* spine 2: t = (S a) b */
    T a = NR[NL[t]], b = NR[t];
    if (!NNF[a]) return app(app(0, lo_step(a)), b);
    return app(NL[t], lo_step(b));
}

/* copying GC: keep only nodes reachable from root; returns new root id */
static T gc_root(T root) {
    /* iterative post-order copy into fresh arrays */
    T *nl = malloc(sizeof(T) * (size_t)cap), *nr = malloc(sizeof(T) * (size_t)cap);
    T *map = malloc(sizeof(T) * (size_t)cap);
    if (!nl || !nr || !map) die("gc alloc");
    for (T i = 0; i < nnodes; i++) map[i] = NIL;
    T *stk = malloc(sizeof(T) * (size_t)nnodes + 16); size_t sp = 0;
    T cnt = 1; map[0] = 0; nl[0] = nr[0] = NIL;
    stk[sp++] = root;
    while (sp) {
        T x = stk[sp - 1];
        if (map[x] != NIL) { sp--; continue; }
        T l = NL[x], r = NR[x];
        if (map[l] == NIL) { stk[sp++] = l; continue; }
        if (map[r] == NIL) { stk[sp++] = r; continue; }
        nl[cnt] = map[l]; nr[cnt] = map[r]; map[x] = cnt++; sp--;
    }
    T nroot = map[root];
    free(stk); free(map);
    store_reset();
    /* rebuild in order (children always have smaller new ids) */
    T *remap = malloc(sizeof(T) * (size_t)cnt); remap[0] = 0;
    for (T i = 1; i < cnt; i++) remap[i] = app(remap[nl[i]], remap[nr[i]]);
    T out = remap[nroot];
    free(remap); free(nl); free(nr);
    return out;
}

/* ---------------- enumeration by unranking ---------------- */
static uint64_t CAT[40];
static T unrank(int n, uint64_t r) {   /* binary trees with n leaves */
    if (n == 1) return 0;
    for (int i = 1; i < n; i++) {
        uint64_t cl = CAT[i - 1], cr = CAT[n - i - 1], cnt = cl * cr;
        if (r < cnt) { T L = unrank(i, r / cr); T R = unrank(n - i, r % cr); return app(L, R); }
        r -= cnt;
    }
    die("unrank");
    return 0;
}

/* language oracles for the congruence search.
 * ORACLE 0: t has a head normal form.   1: Boehm tree of t is finite.   2: Boehm tree has no bottom.
 * Bottom (no hnf) is decided by head reduction with budget 4|t|+B (exact if conjecture C2 holds).
 * Depth cap BTCAP: reaching it counts as an infinite (and, for 2, bottom-free) branch. */
static int ORACLE = 0, BTCAP = 400; static uint64_t bt_visits;
static int bt_lang(T t, int d, uint64_t B) {   /* returns 1 if property holds for the subtree */
    if (++bt_visits > 2000000) return -1;
    if (d >= BTCAP) return ORACLE == 1 ? 0 : 1;
    if (MEMOG[t] == gen) return (int)MEMO[t];
    uint64_t st; T h;
    int rc = hnf(t, 4 * NSZ[t] + B, 1u << 22, &st, &h);
    int res;
    if (rc != 1) res = (ORACLE == 1) ? 1 : 0;          /* bottom leaf: finite, but not bottom-free */
    else if (h == 0) res = 1;
    else if (NL[h] == 0) res = bt_lang(NR[h], d + 1, B);
    else { int r1 = bt_lang(NR[NL[h]], d + 1, B); res = (r1 == 1) ? bt_lang(NR[h], d + 1, B) : r1; }
    if (res >= 0 && (ORACLE == 2 || res == 1)) { MEMO[t] = (T)res; MEMOG[t] = gen; }
    return res;
}
static int oracle(T ct, uint64_t B, uint64_t *st, T *h) {
    if (ORACLE == 0) return hnf(ct, B, 1u << 20, st, h);
    bt_visits = 0;
    int r = bt_lang(ct, 0, B);
    if (r < 0) { printf("bt visit budget exceeded\n"); return -1; }
    return r;
}

/* one-hole contexts: binary tree with n leaves, leaf number hole_pos (left-to-right) is the hole */
static T hole_t; static int hole_ctr, hole_pos;
static T unrank_ctx(int n, uint64_t r) {
    if (n == 1) { T x = (hole_ctr == hole_pos) ? hole_t : 0; hole_ctr++; return x; }
    for (int i = 1; i < n; i++) {
        uint64_t cl = CAT[i - 1], crr = CAT[n - i - 1], cnt = cl * crr;
        if (r < cnt) { T L = unrank_ctx(i, r / crr); T R = unrank_ctx(n - i, r % crr); return app(L, R); }
        r -= cnt;
    }
    die("unrank_ctx");
    return 0;
}
/* two-hole templates: leaf number hole2_px gets hole2_x, leaf hole2_py gets hole2_y */
static T hole2_x, hole2_y; static int hole2_px, hole2_py;
static T unrank_ctx2(int n, uint64_t r) {
    if (n == 1) { T x = (hole_ctr == hole2_px) ? hole2_x : (hole_ctr == hole2_py) ? hole2_y : 0; hole_ctr++; return x; }
    for (int i = 1; i < n; i++) {
        uint64_t cl = CAT[i - 1], crr = CAT[n - i - 1], cnt = cl * crr;
        if (r < cnt) { T Lt = unrank_ctx2(i, r / crr); T Rt = unrank_ctx2(n - i, r % crr); return app(Lt, Rt); }
        r -= cnt;
    }
    die("unrank_ctx2");
    return 0;
}
static int memcmp_u64(const uint64_t *a, const uint64_t *b, size_t w) { for (size_t i = 0; i < w; i++) if (a[i] != b[i]) return 1; return 0; }
static size_t popcount_w(const uint64_t *a, size_t w) { size_t c = 0; for (size_t i = 0; i < w; i++) c += (size_t)__builtin_popcountll(a[i]); return c; }

/* finite S-model loaded from a 'cong' output file: classes, F flags, product table */
static int MN, MS, *MT, *MF, *CLS; static uint32_t *CLSG;
static void load_model(const char *path) {
    FILE *f = fopen(path, "r"); if (!f) die("model file");
    static char line[1 << 16];
    int ncl = 0, row = 0, intab = 0;
    MT = malloc(sizeof(int) * 256 * 256); MF = malloc(sizeof(int) * 256); MS = -1;
    while (fgets(line, sizeof line, f)) {
        if (!strncmp(line, "class ", 6)) {
            int k = (int)strtoll(line + 6, 0, 10); char *p = line; while (*p && strncmp(p, "HN=", 3)) p++;
            MF[k] = p[3] == '1';
            char *q = line; while (*q && strncmp(q, " rep ", 5)) q++;
            if (q[5] == 'S' && (q[6] == '\n' || q[6] == '\r' || q[6] == 0)) MS = k;
            ncl++;
        } else if (!strncmp(line, "# product table", 15)) intab = 1;
        else if (line[0] == '#') intab = 0;
        else if (intab) {
            char *p = line;
            for (int j = 0; j < ncl; j++) { char *e; MT[row * 256 + j] = (int)strtoll(p, &e, 10); p = e; }
            row++;
        }
    }
    fclose(f);
    MN = ncl;
    if (MS < 0 || row != ncl) die("bad model file");
}
static int cls_of(T t) {   /* class of a term in the loaded model (memo per node) */
    if (t == 0) return MS;
    if (CLSG[t] == gen) return CLS[t];
    int c = MT[cls_of(NL[t]) * 256 + cls_of(NR[t])];
    CLS[t] = c; CLSG[t] = gen;
    return c;
}

static uint64_t argu(char **argv, int argc, int i, uint64_t dflt) { return i < argc ? (uint64_t)strtoll(argv[i], 0, 10) : dflt; }

int main(int argc, char **argv) {
    if (argc < 2) { printf("usage: see source\n"); return 1; }
    const char *mode = argv[1];
    CAT[0] = 1; for (int i = 1; i < 40; i++) { CAT[i] = 0; for (int j = 0; j < i; j++) CAT[i] += CAT[j] * CAT[i - 1 - j]; }

    if (!strcmp(mode, "hnf")) {
        store_init(1u << 26);
        T t = parse(argv[2]); uint64_t ms = argu(argv, argc, 3, 100000000ull);
        uint64_t st; T h; int r = hnf(t, ms, 1u << 28, &st, &h);
        if (r == 1) printf("HNF after %llu head steps, size %llu: %s\n", (unsigned long long)st, (unsigned long long)NSZ[h], show(h));
        else printf("no hnf: code %d after %llu steps (stack %llu, nodes %u)\n", r, (unsigned long long)st, (unsigned long long)stn, nnodes);
        return 0;
    }
    if (!strcmp(mode, "nf")) {
        store_init(1u << 26); memo_init();
        T t = parse(argv[2]); nf_budget = argu(argv, argc, 3, 100000000ull);
        nf_fail = 0; T n = nf_rec(t, 0);
        if (!nf_fail) printf("NF size %llu (head steps %llu): %s\n", (unsigned long long)NSZ[n], (unsigned long long)hsteps_total, show(n));
        else printf("nf failed code %d (head steps %llu, nodes %u)\n", nf_fail, (unsigned long long)hsteps_total, nnodes);
        return 0;
    }
    if (!strcmp(mode, "bt")) {
        store_init(1u << 26);
        T t = parse(argv[2]); int d = (int)argu(argv, argc, 3, 6); bt_steps = argu(argv, argc, 4, 1000000ull);
        plen = 0; pc(0); plen = 0; pbuf[0] = 0; bt_rec(t, d); printf("%s\n", pbuf);
        return 0;
    }
    if (!strcmp(mode, "lo")) {
        store_init(1u << 26);
        T t = parse(argv[2]); uint64_t n = argu(argv, argc, 3, 1000);
        FILE *f = fopen(argv[4], "w"); if (!f) die("open out");
        for (uint64_t i = 0; i <= n; i++) {
            fprintf(f, "%llu\n", (unsigned long long)NSZ[t]);
            if (NNF[t]) { fprintf(f, "# normal form at step %llu\n", (unsigned long long)i); break; }
            if (nnodes > cap - (cap >> 2)) t = gc_root(t);
            t = lo_step(t);
            if (overflow) { fprintf(f, "# overflow at step %llu\n", (unsigned long long)i); break; }
        }
        fclose(f);
        return 0;
    }
    if (!strcmp(mode, "trace")) {
        store_init(1u << 24);
        T t = parse(argv[2]); uint64_t n = argu(argv, argc, 3, 30);
        stn = 0; push_args(t);
        for (uint64_t s = 0; s <= n && stn >= 1; s++) {
            printf("%3llu |%llu|:", (unsigned long long)s, (unsigned long long)stn);
            for (size_t i = stn; i-- > 0 && stn - i <= 12;) { plimit = 60; printf("  [%s]", show(ST[i])); }
            printf("\n");
            if (stn < 3) break;
            T a = ST[stn - 1], b = ST[stn - 2], c = ST[stn - 3]; stn -= 3;
            T bc = app(b, c); push(bc); push(c); push_args(a);
        }
        return 0;
    }
    if (!strcmp(mode, "enum")) {
        int n = (int)argu(argv, argc, 2, 8);
        uint64_t lo = argu(argv, argc, 3, 0), hi = argu(argv, argc, 4, CAT[n - 1]);
        uint64_t hs = argu(argv, argc, 5, 100000), ns = argu(argv, argc, 6, 100000);
        if (hi > CAT[n - 1]) hi = CAT[n - 1];
        store_init(1u << 22); memo_init();
        FILE *f = fopen(argv[7], "w"); if (!f) die("open out");
        uint64_t cnt_h = 0, cnt_nh = 0, cnt_n = 0, cnt_nn = 0;
        for (uint64_t r = lo; r < hi; r++) {
            store_reset();
            T t = unrank(n, r);
            uint64_t st; T h; int rh = hnf(t, hs, 1u << 20, &st, &h);
            nf_budget = ns; nf_fail = 0; hsteps_total = 0;
            T nfm = 0;
            if (rh == 1) nfm = nf_rec(t, 0);
            int rn = (rh == 1) ? (nf_fail ? -nf_fail : 1) : -9;
            /* fields: rank hnfcode hsteps hnfsize nfcode nfsteps nfsize term */
            fprintf(f, "%llu %d %llu %llu %d %llu %llu ", (unsigned long long)r, rh, (unsigned long long)st,
                    (unsigned long long)(rh == 1 ? NSZ[h] : 0), rn, (unsigned long long)hsteps_total,
                    (unsigned long long)(rn == 1 ? NSZ[nfm] : 0));
            store_reset(); t = unrank(n, r); plimit = 4000; fputs(show(t), f); fputs("\n", f);
            if (rh == 1) cnt_h++; else cnt_nh++;
            if (rn == 1) cnt_n++; else cnt_nn++;
        }
        fprintf(f, "# n=%d range [%llu,%llu) hnf=%llu nohnf=%llu nf=%llu nonf=%llu\n", n, (unsigned long long)lo, (unsigned long long)hi,
                (unsigned long long)cnt_h, (unsigned long long)cnt_nh, (unsigned long long)cnt_n, (unsigned long long)cnt_nn);
        fclose(f);
        return 0;
    }
    if (!strcmp(mode, "btenum")) {
        /* btenum n lo hi D hsteps out : Boehm-tree depth census (D = depth cap) */
        int n = (int)argu(argv, argc, 2, 8);
        uint64_t lo = argu(argv, argc, 3, 0), hi = argu(argv, argc, 4, CAT[n - 1]);
        int D = (int)argu(argv, argc, 5, 20); uint64_t hs = argu(argv, argc, 6, 10000);
        if (hi > CAT[n - 1]) hi = CAT[n - 1];
        store_init(1u << 23);
        FILE *f = fopen(argv[7], "w"); if (!f) die("open out");
        uint64_t hist[256] = {0};
        for (uint64_t r = lo; r < hi; r++) {
            store_reset();
            T t = unrank(n, r);
            int dep = btdepth(t, D, hs);
            hist[dep]++;
            if (dep >= 6 || btd_fail) {
                store_reset(); t = unrank(n, r); plimit = 4000;
                fprintf(f, "%llu depth %d%s %s\n", (unsigned long long)r, dep, btd_fail ? " (budget)" : "", show(t));
            }
        }
        fprintf(f, "# n=%d range [%llu,%llu) D=%d hist:", n, (unsigned long long)lo, (unsigned long long)hi, D);
        for (int i = 0; i <= D; i++) fprintf(f, " %llu", (unsigned long long)hist[i]);
        fprintf(f, "\n");
        fclose(f);
        return 0;
    }
    if (!strcmp(mode, "btprof")) {
        /* btprof term D K hsteps : BFS over Boehm-tree nodes to depth D; per level report
         * #distinct node terms, #bottom, #distinct depth-K BT signatures, max/min node size */
        store_init(1u << 27);
        T t = parse(argv[2]); int D = (int)argu(argv, argc, 3, 12), K = (int)argu(argv, argc, 4, 6);
        uint64_t hs = argu(argv, argc, 5, 5000);
        HM = malloc(sizeof(T) * (size_t)cap); HMG = calloc((size_t)cap, 4); if (!HM || !HMG) die("hm");
        T *cur = malloc(sizeof(T) * 4), *nxt; size_t nc = 1, ccap = 4; cur[0] = t;
        for (int d = 0; d <= D && nc; d++) {
            size_t nb = 0; uint64_t mx = 0, mn = ~0ull;
            uint64_t *sigs = malloc(8 * nc);
            for (size_t i = 0; i < nc; i++) { sigs[i] = btsig(cur[i], K, hs); if (NSZ[cur[i]] > mx) mx = NSZ[cur[i]]; if (NSZ[cur[i]] < mn) mn = NSZ[cur[i]]; }
            /* count distinct signatures (n^2 for small, else sort) */
            size_t ds = 0;
            for (size_t i = 0; i < nc; i++) { size_t j; for (j = 0; j < i; j++) if (sigs[j] == sigs[i]) break; if (j == i) ds++; if (i > 4000) { ds = 0; break; } }
            /* next level */
            size_t ncap = 2 * nc + 4, nn = 0; nxt = malloc(sizeof(T) * ncap);
            for (size_t i = 0; i < nc; i++) {
                T h = hnf_memo(cur[i], hs);
                if (h == NIL) { nb++; continue; }
                T ch[2]; int j = 0;
                if (h != 0) { if (NL[h] == 0) ch[j++] = NR[h]; else { ch[j++] = NR[NL[h]]; ch[j++] = NR[h]; } }
                for (int q = 0; q < j; q++) {
                    size_t z; for (z = 0; z < nn && nn < 20000; z++) if (nxt[z] == ch[q]) break;
                    if (z == nn || nn >= 20000) nxt[nn++] = ch[q];
                }
            }
            printf("depth %2d: distinct nodes %6llu  bottom %5llu  distinct sig(K=%d) %5llu  size min %llu max %llu  (store %u)\n", d,
                   (unsigned long long)nc, (unsigned long long)nb, K, (unsigned long long)ds, (unsigned long long)mn, (unsigned long long)mx, nnodes);
            fflush(0);
            free(sigs); free(cur); cur = nxt; nc = nn; (void)ccap;
            if (overflow) { printf("store overflow\n"); break; }
        }
        return 0;
    }
    if (!strcmp(mode, "cong")) {
        /* cong Nr Nc budget outfile : approximate syntactic congruence of HN = {t : t has hnf}
         * representatives: all terms with <= Nr leaves; contexts: all one-hole contexts with <= Nc S-leaves */
        int Nr = (int)argu(argv, argc, 2, 8), Nc = (int)argu(argv, argc, 3, 5); uint64_t B = argu(argv, argc, 4, 400);
        store_init(1u << 22); memo_init();
        for (int ai = 6; ai < argc; ai++) if (argv[ai][0] == 'o') ORACLE = argv[ai][1] - '0';
        /* list contexts */
        size_t nctx = 0; for (int n = 0; n <= Nc; n++) nctx += (size_t)(n + 1) * CAT[n];
        int *cn = malloc(sizeof(int) * nctx); uint64_t *cr = malloc(8 * nctx); int *chp = malloc(sizeof(int) * nctx);
        size_t q = 0;
        for (int n = 0; n <= Nc; n++) for (uint64_t r = 0; r < CAT[n]; r++) for (int h = 0; h <= n; h++) { cn[q] = n + 1; cr[q] = r; chp[q] = h; q++; }
        size_t W = (nctx + 63) / 64;
        size_t nrep = 0; for (int n = 1; n <= Nr; n++) nrep += CAT[n - 1];
        uint64_t *sig = calloc(nrep * W, 8); int *rn = malloc(sizeof(int) * nrep); uint64_t *rr = malloc(8 * nrep);
        size_t ri = 0;
        for (int n = 1; n <= Nr; n++) for (uint64_t r = 0; r < CAT[n - 1]; r++) {
            rn[ri] = n; rr[ri] = r;
            for (size_t c = 0; c < nctx; c++) {
                store_reset();
                T t = unrank(n, r);
                hole_t = t; hole_ctr = 0; hole_pos = chp[c];
                T ct = unrank_ctx(cn[c], cr[c]);
                uint64_t st; T h; int rc = oracle(ct, B, &st, &h);
                if (rc == 1) sig[ri * W + c / 64] |= 1ull << (c % 64);
                else if (rc < 0) { printf("overflow rep %zu ctx %zu\n", ri, c); }
            }
            ri++;
        }
        /* classes */
        int *cls = malloc(sizeof(int) * nrep); size_t ncls = 0; size_t *crep = malloc(sizeof(size_t) * nrep); size_t *ccount = calloc(nrep, sizeof(size_t));
        for (size_t i = 0; i < nrep; i++) {
            size_t k;
            for (k = 0; k < ncls; k++) if (!memcmp_u64(sig + crep[k] * W, sig + i * W, W)) break;
            if (k == ncls) { crep[ncls++] = i; }
            cls[i] = (int)k; ccount[k]++;
        }
        FILE *f = fopen(argv[5], "w");
        fprintf(f, "# Nr=%d Nc=%d contexts=%zu reps=%zu classes=%zu budget=%llu\n", Nr, Nc, nctx, nrep, ncls, (unsigned long long)B);
        for (size_t k = 0; k < ncls; k++) {
            store_reset(); T t = unrank(rn[crep[k]], rr[crep[k]]); plimit = 200;
            int hn = (int)(sig[crep[k] * W] & 1); /* context 0 = hole itself */
            fprintf(f, "class %zu HN=%d count %zu ctxHN %zu rep %s\n", k, hn, ccount[k], popcount_w(sig + crep[k] * W, W), show(t));
        }
        int quick = 0; for (int ai = 6; ai < argc; ai++) if (argv[ai][0] == 'q') quick = 1;
        if (quick) { fclose(f); printf("classes %zu\n", ncls); return 0; }
        /* product table on class representatives, with signatures of products */
        int *tab = malloc(sizeof(int) * ncls * ncls); size_t newc = 0;
        uint64_t *ps = malloc(8 * W);
        for (size_t a = 0; a < ncls; a++) for (size_t b = 0; b < ncls; b++) {
            memset(ps, 0, 8 * W);
            for (size_t c = 0; c < nctx; c++) {
                store_reset();
                T ta = unrank(rn[crep[a]], rr[crep[a]]); T tb = unrank(rn[crep[b]], rr[crep[b]]);
                hole_t = app(ta, tb); hole_ctr = 0; hole_pos = chp[c];
                T ct = unrank_ctx(cn[c], cr[c]);
                uint64_t st; T h; int rc = oracle(ct, B, &st, &h);
                if (rc == 1) ps[c / 64] |= 1ull << (c % 64);
            }
            size_t k; for (k = 0; k < ncls; k++) if (!memcmp_u64(sig + crep[k] * W, ps, W)) break;
            tab[a * ncls + b] = k < ncls ? (int)k : -1; if (k == ncls) newc++;
        }
        fprintf(f, "# product table (rows a, cols b: class of rep(a) rep(b); -1 = new class); new=%zu\n", newc);
        for (size_t a = 0; a < ncls; a++) { for (size_t b = 0; b < ncls; b++) fprintf(f, "%d ", tab[a * ncls + b]); fprintf(f, "\n"); }
        /* well-definedness: for every rep pair (i,j) with both sizes small, check class(i j) == tab[cls i][cls j] */
        size_t bad = 0, tested = 0;
        for (size_t i = 0; i < nrep; i++) for (size_t j = 0; j < nrep; j++) {
            if (rn[i] + rn[j] > Nr) continue;
            /* product i j is itself a representative of size rn[i]+rn[j]: find it via signature lookup */
            memset(ps, 0, 8 * W);
            for (size_t c = 0; c < nctx; c++) {
                store_reset();
                T ta = unrank(rn[i], rr[i]); T tb = unrank(rn[j], rr[j]);
                hole_t = app(ta, tb); hole_ctr = 0; hole_pos = chp[c];
                T ct = unrank_ctx(cn[c], cr[c]);
                uint64_t st; T h; int rc = oracle(ct, B, &st, &h);
                if (rc == 1) ps[c / 64] |= 1ull << (c % 64);
            }
            size_t k; for (k = 0; k < ncls; k++) if (!memcmp_u64(sig + crep[k] * W, ps, W)) break;
            tested++;
            if ((int)k != tab[cls[i] * ncls + cls[j]]) bad++;
        }
        fprintf(f, "# well-definedness check: tested %zu products, inconsistent %zu\n", tested, bad);
        fclose(f);
        printf("classes %zu new-in-products %zu inconsistent %zu/%zu\n", ncls, newc, bad, tested);
        return 0;
    }
    if (!strcmp(mode, "botcert")) {
        /* botcert n lo hi pmodel hmodel cap maxvisits budget out : for every term of size n in [lo,hi) that the
         * productivity model puts in a non-productive class, search its Boehm tree breadth-first (distinct nodes) for a
         * node whose class in the HN model is bottom. By Theorem A such a node has no hnf: an unconditional certificate
         * of non-productivity. A node with an HN-model class in F whose hnf is not found within 4|u|+budget steps is an
         * ANOMALY (never counted as bottom). Reports the minimal certified depth histogram and the deepest case. */
        int n = (int)argu(argv, argc, 2, 8);
        uint64_t lo = argu(argv, argc, 3, 0), hi = argu(argv, argc, 4, CAT[n - 1]);
        if (hi > CAT[n - 1]) hi = CAT[n - 1];
        load_model(argv[5]); int PS = MS, *PT = MT, *PF = MF;          /* productivity model (arrays stay allocated) */
        load_model(argv[6]);                                          /* HN model -> MT, MF, MS used by cls_of */
        int D = (int)argu(argv, argc, 7, 300); uint64_t MV = argu(argv, argc, 8, 1000000), B = argu(argv, argc, 9, 1000);
        store_init(1u << 24);
        CLS = malloc(sizeof(int) * (size_t)cap); CLSG = calloc((size_t)cap, 4); if (!CLS || !CLSG) die("cls");
        uint32_t *VIS = calloc((size_t)cap, 4); int *PC = malloc(sizeof(int) * (size_t)cap); if (!VIS || !PC) die("vis");
        T *cur = malloc(sizeof(T) * MV), *nxt = malloc(sizeof(T) * MV); if (!cur || !nxt) die("bfs");
        int getenv_dbg = argc > 11;
        if (getenv_dbg) { printf("PS=%d MS=%d PF:", PS, MS); for (int k = 0; k < 39; k++) printf("%d", PF[k]); printf(" MF:"); for (int k = 0; k < MN; k++) printf("%d", MF[k]); printf(" PT==MT? %d PF==MF? %d\n", PT == MT, PF == MF); }
        FILE *f = fopen(argv[10], "w"); if (!f) die("open out");
        uint64_t hist[4096] = {0}, nbot = 0, nanom = 0, nnot = 0; int maxd = -1; uint64_t rmax = 0;
        for (uint64_t r = lo; r < hi; r++) {
            store_reset();
            T t = unrank(n, r);
            /* productivity class of t: nodes are created bottom-up, so a single pass over ids 1..t suffices */
            PC[0] = PS; for (T u = 1; u <= t; u++) PC[u] = PT[PC[NL[u]] * 256 + PC[NR[u]]];
            if (PF[PC[t]]) continue;
            if (getenv_dbg) { plimit = 4000; printf("DBG r=%llu PC=%d t=%u NLt=%u NRt=%u PCL=%d PCR=%d %s\n", (unsigned long long)r, PC[t], t, NL[t], NR[t], PC[NL[t]], PC[NR[t]], show(t)); }
            nbot++;
            size_t nc = 1; cur[0] = t; VIS[t] = gen; uint64_t vis = 1; int found = -1, anom = 0, over = 0;
            for (int d = 0; d <= D && nc && found < 0 && !anom && !over; d++) {
                size_t nn = 0;
                for (size_t i = 0; i < nc; i++) {
                    T u = cur[i];
                    if (!MF[cls_of(u)]) { found = d; break; }
                    uint64_t st; T h; int rc = hnf(u, 4 * NSZ[u] + B, 1u << 22, &st, &h);
                    if (rc != 1) { anom = rc == 0 ? 1 : 2; break; }
                    if (h == 0) continue;
                    T kid[2]; int k = 0;
                    if (NL[h] == 0) kid[k++] = NR[h]; else { kid[k++] = NR[NL[h]]; kid[k++] = NR[h]; }
                    for (int j = 0; j < k; j++) {
                        if (VIS[kid[j]] == gen) continue;
                        VIS[kid[j]] = gen;
                        if (++vis > MV) { over = 1; break; }
                        nxt[nn++] = kid[j];
                    }
                    if (over) break;
                }
                T *sw = cur; cur = nxt; nxt = sw; nc = nn;
            }
            if (found >= 0) { hist[found < 4095 ? found : 4095]++; if (found > maxd) { maxd = found; rmax = r; } continue; }
            store_reset(); t = unrank(n, r); plimit = 4000;
            if (anom) { nanom++; fprintf(f, "ANOMALY(%s) rank %llu term %s\n", anom == 1 ? "budget" : "resource", (unsigned long long)r, show(t)); }
            else { nnot++; fprintf(f, "NOT-FOUND(%s) rank %llu term %s\n", over ? "visits" : (nc ? "depth" : "finite-tree"), (unsigned long long)r, show(t)); }
        }
        store_reset(); T tm = unrank(n, rmax); plimit = 4000;
        fprintf(f, "# n=%d range [%llu,%llu) cap=%d nonproductive-class=%llu certified=%llu anomalies=%llu notfound=%llu maxdepth=%d at %s\n# hist:",
                n, (unsigned long long)lo, (unsigned long long)hi, D, (unsigned long long)nbot,
                (unsigned long long)(nbot - nanom - nnot), (unsigned long long)nanom, (unsigned long long)nnot, maxd, show(tm));
        for (int i = 0; i <= (maxd > 0 ? maxd : 0); i++) fprintf(f, " %llu", (unsigned long long)hist[i]);
        fprintf(f, "\n");
        fclose(f);
        return 0;
    }
    if (!strcmp(mode, "pverify")) {
        /* pverify n lo hi modelfile cap out [budget] : for every term of size n in [lo,hi): class in a finite model
         * (F = productive classes) versus the productivity oracle (ORACLE 2, Boehm-tree depth cap `cap`).
         * Reports every disagreement and every oracle budget failure. */
        int n = (int)argu(argv, argc, 2, 8);
        uint64_t lo = argu(argv, argc, 3, 0), hi = argu(argv, argc, 4, CAT[n - 1]);
        if (hi > CAT[n - 1]) hi = CAT[n - 1];
        load_model(argv[5]);
        ORACLE = 2; BTCAP = (int)argu(argv, argc, 6, 400);
        uint64_t PB = argu(argv, argc, 8, 200);        /* per-node head budget: 4|node| + PB */
        store_init(1u << 24); memo_init();
        CLS = malloc(sizeof(int) * (size_t)cap); CLSG = calloc((size_t)cap, 4); if (!CLS || !CLSG) die("cls");
        FILE *f = fopen(argv[7], "w"); if (!f) die("open out");
        uint64_t agP = 0, agB = 0, mPoB = 0, mBoP = 0, unk = 0;
        for (uint64_t r = lo; r < hi; r++) {
            store_reset();
            T t = unrank(n, r);
            int c = cls_of(t), m = MF[c];
            uint64_t st; T h; int o = oracle(t, PB, &st, &h);
            if (o == (m ? 1 : 0)) { if (m) agP++; else agB++; continue; }
            if (o < 0) unk++; else if (m) mPoB++; else mBoP++;
            store_reset(); t = unrank(n, r); plimit = 4000;
            fprintf(f, "%s rank %llu class %d term %s\n", o < 0 ? "ORACLE-UNKNOWN" : (m ? "MODEL-P-ORACLE-BOT" : "MODEL-BOT-ORACLE-P"),
                    (unsigned long long)r, c, show(t));
        }
        fprintf(f, "# n=%d range [%llu,%llu) cap=%d agreeProductive=%llu agreeBottom=%llu modelP_oracleBot=%llu modelBot_oracleP=%llu unknown=%llu\n",
                n, (unsigned long long)lo, (unsigned long long)hi, BTCAP, (unsigned long long)agP, (unsigned long long)agB,
                (unsigned long long)mPoB, (unsigned long long)mBoP, (unsigned long long)unk);
        fclose(f);
        return 0;
    }
    if (!strcmp(mode, "verify")) {
        /* verify n lo hi modelfile budget out : for every term of size n in [lo,hi):
         * class via finite model; if class in F, head-reduce with step budget; report max steps
         * and any term in F that fails to reach hnf within budget (candidate counterexample). */
        int n = (int)argu(argv, argc, 2, 8);
        uint64_t lo = argu(argv, argc, 3, 0), hi = argu(argv, argc, 4, CAT[n - 1]);
        if (hi > CAT[n - 1]) hi = CAT[n - 1];
        load_model(argv[5]);
        uint64_t B = argu(argv, argc, 6, 200);
        store_init(1u << 22);
        CLS = malloc(sizeof(int) * (size_t)cap); CLSG = calloc((size_t)cap, 4); if (!CLS || !CLSG) die("cls");
        FILE *f = fopen(argv[7], "w"); if (!f) die("open out");
        uint64_t nF = 0, nBot = 0, maxst = 0, rmax = 0, fails = 0;
        uint64_t hist[64] = {0};
        for (uint64_t r = lo; r < hi; r++) {
            store_reset();
            T t = unrank(n, r);
            int c = cls_of(t);
            if (!MF[c]) { nBot++; continue; }
            nF++;
            uint64_t st; T h; int rc = hnf(t, B, 1u << 20, &st, &h);
            if (rc != 1) { fails++; store_reset(); t = unrank(n, r); plimit = 4000; fprintf(f, "FAIL rank %llu code %d class %d term %s\n", (unsigned long long)r, rc, c, show(t)); continue; }
            /* the hnf must have a class equal to the term's class (model invariance sanity check) */
            if (cls_of(h) != c) { fprintf(f, "INVARIANCE-VIOLATION rank %llu\n", (unsigned long long)r); }
            hist[st < 63 ? st : 63]++;
            if (st > maxst) { maxst = st; rmax = r; }
        }
        store_reset(); T tm = unrank(n, rmax); plimit = 4000;
        fprintf(f, "# n=%d range [%llu,%llu) F=%llu bottom=%llu fails=%llu maxsteps=%llu at %s\n# hist:", n, (unsigned long long)lo, (unsigned long long)hi,
                (unsigned long long)nF, (unsigned long long)nBot, (unsigned long long)fails, (unsigned long long)maxst, show(tm));
        for (int i = 0; i < 64; i++) fprintf(f, " %llu", (unsigned long long)hist[i]);
        fprintf(f, "\n");
        fclose(f);
        return 0;
    }
    if (!strcmp(mode, "grid")) {
        /* grid nS J oracle cap fam out : all templates = binary trees with nS S-leaves plus two holes X,Y
         * (X before Y or after); fill X = fam(j), Y = fam(k) for j,k in 1..J; evaluate oracle.
         * fam: 'n' nest (S, SS, S(SS), S(S(SS)),...), 'c' chain (S, SS, SSS, ...).
         * Reports templates whose grid has >= J-1 distinct rows (counting behaviour). */
        int nS = (int)argu(argv, argc, 2, 3), J = (int)argu(argv, argc, 3, 10);
        ORACLE = (int)argu(argv, argc, 4, 1); BTCAP = (int)argu(argv, argc, 5, 400); char fam = argv[6][0];
        store_init(1u << 23); memo_init();
        FILE *f = fopen(argv[7], "w");
        int L = nS + 2; uint64_t ntree = CAT[L - 1]; size_t flagged = 0, total = 0;
        for (uint64_t r = 0; r < ntree; r++) for (int hx = 0; hx < L; hx++) for (int hy = 0; hy < L; hy++) {
            if (hx == hy) continue;
            total++;
            static int grid[64][64]; int distinct = 0;
            for (int j = 1; j <= J; j++) for (int k = 1; k <= J; k++) {
                store_reset();
                T X = 0, Y = 0;
                for (int q = 2; q <= j; q++) X = (fam == 'n') ? app(0, X) : app(X, 0);
                if (fam == 'n' && j >= 2) { X = 0; for (int q = 2; q <= j; q++) X = (q == 2) ? app(0, 0) : app(0, X); }
                for (int q = 2; q <= k; q++) Y = (fam == 'n') ? app(0, Y) : app(Y, 0);
                if (fam == 'n' && k >= 2) { Y = 0; for (int q = 2; q <= k; q++) Y = (q == 2) ? app(0, 0) : app(0, Y); }
                hole2_x = X; hole2_y = Y; hole2_px = hx; hole2_py = hy; hole_ctr = 0;
                T ct = unrank_ctx2(L, r);
                uint64_t st; T h; grid[j][k] = oracle(ct, 200, &st, &h);
            }
            for (int j = 1; j <= J; j++) { int same = 0; for (int j2 = 1; j2 < j; j2++) { int eq = 1; for (int k = 1; k <= J; k++) if (grid[j][k] != grid[j2][k]) { eq = 0; break; } if (eq) { same = 1; break; } } if (!same) distinct++; }
            if (distinct >= J - 1) {
                flagged++;
                store_reset(); hole2_x = 0; hole2_y = 0; hole_ctr = 0; hole2_px = hx; hole2_py = hy;
                fprintf(f, "template rank %llu holes X@%d Y@%d distinct rows %d\n", (unsigned long long)r, hx, hy, distinct);
                for (int j = 1; j <= J; j++) { fprintf(f, "  j=%2d:", j); for (int k = 1; k <= J; k++) fprintf(f, " %d", grid[j][k]); fprintf(f, "\n"); }
            }
        }
        fprintf(f, "# nS=%d J=%d oracle=%d fam=%c templates=%zu flagged=%zu\n", nS, J, ORACLE, fam, total, flagged);
        fclose(f);
        printf("templates %zu flagged %zu\n", total, flagged);
        return 0;
    }
    if (!strcmp(mode, "unary")) {
        /* unary nS J oracle cap fam out : one-hole contexts with <= nS S-leaves, hole := fam(j), j=0..J.
         * fam: 'n' nest N0=S, N(j+1)=S N(j);  'c' chain S..S (j+1 S's);  'a' A^j: A=SSS, A^0=S, A^(j+1)=A^j A.
         * Flags bit sequences that are not eventually periodic within the window
         * (no p<=J/4, j0<=J/2 with b(j)=b(j+p) for all j0<=j<=J-p). */
        int nS = (int)argu(argv, argc, 2, 4), J = (int)argu(argv, argc, 3, 40);
        ORACLE = (int)argu(argv, argc, 4, 1); BTCAP = (int)argu(argv, argc, 5, 400); char fam = argv[6][0];
        store_init(1u << 24); memo_init();
        FILE *f = fopen(argv[7], "w");
        size_t total = 0, flagged = 0;
        static int b[512];
        for (int n = 0; n <= nS; n++) for (uint64_t r = 0; r < CAT[n]; r++) for (int hp = 0; hp <= n; hp++) {
            total++;
            for (int j = 0; j <= J; j++) {
                store_reset();
                T X = 0;
                if (fam == 'n') for (int q = 0; q < j; q++) X = app(0, X);
                else if (fam == 'c') for (int q = 0; q < j; q++) X = app(X, 0);
                else { T A = app(app(0, 0), 0); X = 0; for (int q = 0; q < j; q++) X = (q == 0) ? A : app(X, A); }
                hole_t = X; hole_ctr = 0; hole_pos = hp;
                T ct = unrank_ctx(n + 1, r);
                uint64_t st; T h; b[j] = oracle(ct, 200, &st, &h);
            }
            int periodic = 0;
            for (int p = 1; p <= J / 4 && !periodic; p++) for (int j0 = 0; j0 <= J / 2 && !periodic; j0++) {
                int ok = 1; for (int j = j0; j + p <= J; j++) if (b[j] != b[j + p]) { ok = 0; break; }
                if (ok) periodic = 1;
            }
            if (!periodic) {
                flagged++;
                store_reset(); hole_t = 0; hole_ctr = 0; hole_pos = hp; T ct = unrank_ctx(n + 1, r); plimit = 200;
                fprintf(f, "ctx n=%d rank %llu hole@%d (hole shown as S) %s : ", n, (unsigned long long)r, hp, show(ct));
                for (int j = 0; j <= J; j++) fprintf(f, "%d", b[j] < 0 ? 9 : b[j]);
                fprintf(f, "\n");
            }
        }
        fprintf(f, "# nS=%d J=%d oracle=%d fam=%c contexts=%zu flagged=%zu\n", nS, J, ORACLE, fam, total, flagged);
        fclose(f);
        printf("contexts %zu flagged %zu\n", total, flagged);
        return 0;
    }
    if (!strcmp(mode, "infpath")) {
        /* infpath term depth cap : follow a Boehm-tree path along children with infinite BT (oracle 1 == 0);
         * prints node terms and which child (1st/2nd) was taken, and the sibling's BT-finiteness */
        store_init(1u << 26); memo_init();
        ORACLE = 1; BTCAP = (int)argu(argv, argc, 4, 300);
        T t = parse(argv[2]); int D = (int)argu(argv, argc, 3, 30);
        for (int d = 0; d < D; d++) {
            uint64_t st; T h; int rc = hnf(t, 4 * NSZ[t] + 200, 1u << 24, &st, &h);
            plimit = 300;
            printf("%3d |t|=%-6llu steps=%-4llu %s\n", d, (unsigned long long)NSZ[t], (unsigned long long)st, show(t));
            if (rc != 1) { printf("    (no hnf)\n"); break; }
            if (h == 0) { printf("    (leaf S)\n"); break; }
            T a = NL[h] == 0 ? NR[h] : NR[NL[h]], b = NL[h] == 0 ? 0 : NR[h]; int k = NL[h] == 0 ? 1 : 2;
            MEMOG[0] = 0; gen++;   /* invalidate memo between queries */
            uint64_t s2; T h2;
            int fa = oracle(a, 200, &s2, &h2); gen++;
            int fb = k == 2 ? oracle(b, 200, &s2, &h2) : 1; gen++;
            printf("    hnf has %d comps; BT-finite(comp1)=%d BT-finite(comp2)=%d\n", k, fa, fb);
            if (fa == 0) t = a; else if (k == 2 && fb == 0) t = b; else { printf("    both finite?!\n"); break; }
        }
        return 0;
    }
    if (!strcmp(mode, "closure")) {
        /* closure Nr Nc oracle cap maxcls out : BEKW-style closure of the syntactic congruence of a
         * language (oracle) w.r.t. one-hole contexts with <= Nc S-leaves. Start with all terms <= Nr leaves;
         * repeatedly add representatives of product classes not yet present, until closed (or > maxcls). */
        int Nr = (int)argu(argv, argc, 2, 7), Nc = (int)argu(argv, argc, 3, 6);
        ORACLE = (int)argu(argv, argc, 4, 1); BTCAP = (int)argu(argv, argc, 5, 400);
        size_t maxcls = (size_t)argu(argv, argc, 6, 300);
        store_init(1u << 24); memo_init();
        size_t nctx = 0; for (int n = 0; n <= Nc; n++) nctx += (size_t)(n + 1) * CAT[n];
        int *cn = malloc(sizeof(int) * nctx); uint64_t *cr = malloc(8 * nctx); int *chp = malloc(sizeof(int) * nctx);
        size_t q = 0;
        for (int n = 0; n <= Nc; n++) for (uint64_t r = 0; r < CAT[n]; r++) for (int h = 0; h <= n; h++) { cn[q] = n + 1; cr[q] = r; chp[q] = h; q++; }
        size_t W = (nctx + 63) / 64;
        size_t rcap = 1 << 16, nrep = 0; char **reps = malloc(sizeof(char *) * rcap);
        uint64_t *sig = malloc(8 * W * rcap);
        /* signature of a term given as string */
        #define SIGOF(str, out) do { memset((out), 0, 8 * W); for (size_t c_ = 0; c_ < nctx; c_++) { store_reset(); T t_ = parse(str); \
            hole_t = t_; hole_ctr = 0; hole_pos = chp[c_]; T ct_ = unrank_ctx(cn[c_], cr[c_]); uint64_t st_; T h_; \
            int rc_ = oracle(ct_, 200, &st_, &h_); if (rc_ == 1) (out)[c_ / 64] |= 1ull << (c_ % 64); } } while (0)
        size_t ncls = 0; size_t *crep = malloc(sizeof(size_t) * rcap);
        for (int n = 1; n <= Nr; n++) for (uint64_t r = 0; r < CAT[n - 1]; r++) {
            store_reset(); T t = unrank(n, r); plimit = 100000; const char *s = show(t);
            uint64_t *sg = sig + nrep * W; SIGOF(s, sg);
            size_t k; for (k = 0; k < ncls; k++) if (!memcmp_u64(sig + crep[k] * W, sg, W)) break;
            if (k == ncls) { reps[nrep] = malloc(strlen(s) + 1); memcpy(reps[nrep], s, strlen(s) + 1); crep[ncls++] = nrep++; }
        }
        printf("initial classes from terms <= %d leaves: %zu (contexts %zu)\n", Nr, ncls, nctx); fflush(0);
        int *tab = NULL; size_t tabn = 0; int round = 0;
        uint64_t *ps = malloc(8 * W);
        for (;;) {
            round++;
            size_t before = ncls, added = 0;
            free(tab); tab = malloc(sizeof(int) * ncls * ncls); tabn = ncls;
            for (size_t a = 0; a < tabn; a++) for (size_t b = 0; b < tabn; b++) {
                const char *A = reps[crep[a]], *B = reps[crep[b]];
                size_t la = strlen(A), lb = strlen(B);
                char *pr = malloc(la + lb + 5); pr[0] = '('; memcpy(pr + 1, A, la); pr[la + 1] = ')'; pr[la + 2] = '(';
                memcpy(pr + la + 3, B, lb); pr[la + lb + 3] = ')'; pr[la + lb + 4] = 0;
                SIGOF(pr, ps);
                size_t k; for (k = 0; k < ncls; k++) if (!memcmp_u64(sig + crep[k] * W, ps, W)) break;
                if (k == ncls) {
                    if (ncls >= maxcls || nrep >= rcap) { tab[a * tabn + b] = -1; free(pr); continue; }
                    memcpy(sig + nrep * W, ps, 8 * W); reps[nrep] = pr; crep[ncls++] = nrep++; added++;
                } else free(pr);
                tab[a * tabn + b] = (int)k;
            }
            printf("round %d: classes %zu -> %zu (added %zu)\n", round, before, ncls, added); fflush(0);
            if (added == 0 || ncls >= maxcls) break;
        }
        FILE *f = fopen(argv[7], "w");
        fprintf(f, "# closure Nr=%d Nc=%d oracle=%d cap=%d classes=%zu closed=%d\n", Nr, Nc, ORACLE, BTCAP, ncls, ncls == tabn);
        for (size_t k = 0; k < ncls; k++) {
            int inL = 0; { /* context 0 is the hole itself */ inL = (int)(sig[crep[k] * W] & 1); }
            fprintf(f, "class %zu HN=%d count 1 ctxHN %zu rep %s\n", k, inL, popcount_w(sig + crep[k] * W, W), reps[crep[k]]);
        }
        if (ncls == tabn) {
            fprintf(f, "# product table (rows a, cols b: class of rep(a) rep(b); -1 = new class); new=0\n");
            for (size_t a = 0; a < tabn; a++) { for (size_t b = 0; b < tabn; b++) fprintf(f, "%d ", tab[a * tabn + b]); fprintf(f, "\n"); }
            fprintf(f, "# end\n");
        }
        fclose(f);
        return 0;
    }
    if (!strcmp(mode, "evalfile")) {
        /* evalfile oracle cap infile outfile : one term per line; writes "result term" */
        store_init(1u << 25); memo_init();
        ORACLE = (int)argu(argv, argc, 2, 1); BTCAP = (int)argu(argv, argc, 3, 400);
        FILE *in = fopen(argv[4], "r"), *out = fopen(argv[5], "w"); if (!in || !out) die("files");
        static char line[1 << 16];
        while (fgets(line, sizeof line, in)) {
            size_t L = strlen(line); while (L && (line[L - 1] == '\n' || line[L - 1] == '\r' || line[L - 1] == ' ')) line[--L] = 0;
            if (!L) continue;
            store_reset(); T t = parse(line); uint64_t st; T h;
            int r = oracle(t, 200, &st, &h);
            fprintf(out, "%d %s\n", r, line);
        }
        fclose(in); fclose(out);
        return 0;
    }
    if (!strcmp(mode, "lang")) {
        /* lang oracle cap term... : evaluate the language oracle on given terms */
        store_init(1u << 24); memo_init();
        ORACLE = (int)argu(argv, argc, 2, 1); BTCAP = (int)argu(argv, argc, 3, 400);
        for (int i = 4; i < argc; i++) {
            store_reset(); T t = parse(argv[i]); uint64_t st; T h;
            int r = oracle(t, 200, &st, &h);
            printf("%d  %s\n", r, argv[i]);
        }
        return 0;
    }
    if (!strcmp(mode, "spine")) {
        /* spine term dir depth modelfile hsteps nfsteps : follow the Boehm tree along a path.
         * dir: string over {L,R,A}: L = first component, R = last component, A = auto (component of
         * larger size); last letter repeats. Prints node size/class and the side component's
         * class, size and normal-form size (or 'inf' if not normalizing within budget). */
        store_init(1u << 27); memo_init();
        T t = parse(argv[2]); const char *dir = argv[3]; int D = (int)argu(argv, argc, 4, 30);
        load_model(argv[5]); CLS = malloc(sizeof(int) * (size_t)cap); CLSG = calloc((size_t)cap, 4);
        uint64_t hs = argu(argv, argc, 6, 100000), ns = argu(argv, argc, 7, 200000);
        size_t dl = strlen(dir);
        for (int d = 0; d < D; d++) {
            uint64_t st; T h; int rc = hnf(t, hs, 1u << 26, &st, &h);
            printf("%3d |node|=%-8llu cls=%-2d steps=%-6llu", d, (unsigned long long)NSZ[t], cls_of(t), (unsigned long long)st);
            if (rc != 1) { printf(" no hnf (code %d)\n", rc); break; }
            int k = h == 0 ? 0 : (NL[h] == 0 ? 1 : 2);
            if (k == 0) { printf(" hnf S (leaf)\n"); break; }
            T a = k == 1 ? NR[h] : NR[NL[h]], b = k == 2 ? NR[h] : 0;
            char c = dir[d < (int)dl ? d : (int)dl - 1];
            T next, side; int hasside = (k == 2);
            if (c == 'A') c = (k == 2 && NSZ[b] > NSZ[a]) ? 'R' : 'L';
            if (c == 'R' && k == 2) { next = b; side = a; } else { next = a; side = b; c = 'L'; }
            printf(" k=%d go %c", k, c);
            if (hasside) {
                nf_budget = ns; nf_fail = 0; T nfm = nf_rec(side, 0);
                plimit = 70;
                printf(" | side cls=%-2d |side|=%-6llu nf=", cls_of(side), (unsigned long long)NSZ[side]);
                if (!nf_fail) printf("%-6llu %s", (unsigned long long)NSZ[nfm], show(nfm)); else printf("inf(code %d)", nf_fail);
            }
            printf("\n"); fflush(0);
            t = next;
            if (overflow) { printf("overflow\n"); break; }
        }
        return 0;
    }
    printf("unknown mode\n");
    return 1;
}
