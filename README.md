# S Combinator Challenge — research notes, theorems and tools

**Status: Wolfram's S Combinator Challenge is NOT solved here.** Nothing in this repository claims a proof that the
S combinator is, or is not, computation universal. It contains partial results, machine-checked lemmas, computer
certificates and documented failed approaches, each labelled:
PROVED / MACHINE-CHECKED / COMPUTATIONALLY CERTIFIED / EXPERIMENTALLY SUPPORTED / CONJECTURAL / REFUTED.

## Where to look
| File / folder | Contents |
|---|---|
| `RESULTS.md` | **start here**: one page with what is machine-checked, proved, and still open |
| `PROOF.md` | every theorem, lemma and conjecture with its status label, proof or certificate |
| `STATUS.md` | results table (R1–R84) |
| `PRIZE_ASSESSMENT.md` | what a complete proof in either direction would still need |
| `EXPERIMENTS.md` | experiment log (E1–E114) |
| `FAILED_APPROACHES.md` | approaches that did not work, and why |
| `NEXT_STEPS.md` | current plan and open problems |
| `PAPER_DRAFT.md` | draft write-up of the Böhm-tree results (not peer reviewed) |
| `code/` | Python and C tools: head machine, provers, model checkers. `verify_all.py` re-checks about 90 results, including every Lean file |
| `lean/` | 30 Lean 4 files (Theorem Q10, Theorem A, P2, Propositions Q and Q″, LP1, confluence, Proposition CF, head normalisation, F5, MW, barrier lemmas 8–12, Theorems J and N*, UR, the agents' obstruction theorems; list in `RESULTS.md`); `code/lean_check.py` compiles a file and lists its axioms |
| `data/` | finite S-models, census and enumeration data |
| `agent_work/`, `agent_work_U/` | exploratory logs and scripts for the non-universality and universality directions |

## Reproducing the checks
```
cd code
python verify_all.py
```
The Lean files need the Lean 4.35.0 toolchain (no Mathlib), e.g. `python lean_check.py ../lean/Q10.lean`. The full run
took about 15 minutes on the author's laptop (85/85 checks passed, 2026-10-27, 03:25 EDT), mostly for the kernel checks of
the finite models (`PropQ.lean` alone takes several minutes).

Not included: the third-party papers that were consulted (copyright), two raw data files over 50 MB (regenerable with
the scripts in `code/`), and compiled binaries (sources are in `code/*.c`).
