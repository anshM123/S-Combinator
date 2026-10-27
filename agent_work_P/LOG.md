# agent_work_P LOG (parallel-evaluation universality agent)

## 2026-10-27 10:18 EDT start
Task: look for universal emulation by S under parallel (ReplaceAll-style) evaluation, or precise barriers. Deadline 15:00 EDT.

## 2026-10-27 10:50 EDT reading done; working picture
* Read PROOF.md (LZ/PL, time-to-data, CF, Master Reduction, CA, CA-par, transfer lemma, Lemmas 8-10, J), STATUS R34/43-47/63-65, PRIZE_ASSESSMENT rules, agent_work_U/LOG.md (it only says the clock channel was "argued contractive", no file).
* Working picture (to be proved below): under ReplaceAll every element at list position >= 4 evolves autonomously; elements interact only at the head. So a parallel run = the head machine on PROCESSES. An element x pushed at pass b that is opened at pass T delivers its hnf at pass max(T, b + h(x)) (h = its own parallel hnf time) -- a MAX-PLUS law -- while leftmost-outermost delivers at T + h_LO(x) (a sum). Control flow (Boehm tree) is identical (Prop. CF); what differs is timing (max vs +) and pre-evaluated syntax.
* Plan: (1) prove the max-plus law exactly (from Lemma LZ) and test it; (2) exact gadgets: join = max under ReplaceAll vs sum under LO, race gadget; (3) reduction: races + concurrency + polynomial-time processes would give universality via Hilbert's 10th problem / Krob (max-plus automata); find exactly which ingredient S lacks; (4) barriers that transfer to every order.
* ptools.py: helpers (direct ReplaceAll pass P from code/parallel_eval.py, head steps, tree calls/levels).
