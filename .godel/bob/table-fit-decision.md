# Seed a neighboring moment fit from the certified table

**Decision.** At the decision to nominate a neighboring deletion law, try one refit on the old table's atom sites instead of reconstructing an extrema seed from scratch files, because the table is already accepted, and an exact positive-surplus repair, not convergence of the search, is the stopping test. The new Work cue does not mandate a solve on a settled span or rule out enrichment if one round fails.

**What the worker knew.** Gödel run `01a20d25-1a65-71ae-8979-e8cf17a8bb52`, Yah `01a20d25-1cbb-7ecb-84a2-8df095af345e`, launched `766e1d844630` with the separate Work prompt. There was an integer atom table for $[-192,192]$ and a conditional extension on free prime slabs, not a joint law for the full bilateral target. Child `VSTkRWJ` tested the old extension against a fixed price; its eventual rejection is not separation. In parallel, `BsUtEWM` used an earlier scratch mask and solver driver, extracted laws from the cone duals, and passed a reduced integer table to the exact checker. Work rightly adopted the bilateral and then half-line certificates, not a claim based on the fitted margin. The accepted mathematics through `d1ba5766fc9d` did not include a repository-only way to regenerate neighboring nominations from the old table. The record does not show the old seed was mathematically necessary or that Work considered and rejected using the table.

**Independent reason.** Alice's `d6739690f915` [gap-bracket decision](../alice/gap-bracket-decision.md) tests full candidate parts on retained reference support at the same square-root enumeration cost, rather than just the reference gcd. The comparable decision here is what to retain across fits: Keep the actual sites and reoptimize their masses, not just the old trace averages or mask. The local test is more informative without asserting it exhausts other supports. The proofs and costs are not comparable across programs.

**Targeted test, not a blind prompt trial.** The criterion was an integer table for *both* full bilateral first blocks, the retained second triple, exact admissibility after repair, and positive surplus. A numerical objective alone was insufficient. In Improve `01a20d32-edc5-75ae-8b14-3af7adc5c3d3`, `TTRpMUg` had the launch revision, table, target, and proposed table-seeding task, but no old scratch or later tables. The script reads only the old prime and circle **sites**, inherits them across slab subdivisions, and adds a fixed grid on new slabs. Weights and disk coordinates are free. On the original span it returned an `AlmostSolved` nomination (not certified here). On $[-256,256]$ the results were:

| Seed and rounds | Measured wall time, before exact check | Repaired surplus |
|---|---:|---:|
| Earlier mask, one round, replay of the old driver | 27.5 s | $1.21737\cdot10^{-5}$ or greater |
| Launch table sites, one round | 31.6 s | $2.40846\cdot10^{-5}$ or greater |
| Earlier mask, recorded six-round fit and subsequent support reduction | about 201 s including setup | $3.14641\cdot10^{-5}$ or greater |

The two one-round trials each passed the Gram/dilution inequalities, not just the solver's residual test. The one-round historical control rules out attributing success to skipping five *necessary* rounds. The wall times have different setup and are not throughput benchmarks. Both methods certify the same bilateral conclusion; the gain is a replayable nomination from accepted inputs. An initial check mistakenly passed the old-span output to the bilateral checker and correctly failed its first ramp-boundary assertion. It was the table for the requested block, not that control, that certified. Neither one round nor fixed sites are generally sufficient.

**Replay of the new route** (Python 3.12, NumPy 2.5.5, SciPy 1.18.1, Clarabel 0.11.1, then SageMath 10.9; scratch output may be anywhere):

```sh
b=.godel/bob
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1
python "$b/search-delete-33-table-fit.py" --left -256 --right 256 --table "$b/deletion-laws/delete-33.txt" --out /tmp/delete-33-refit.txt
/opt/sage-10.9/bin/python "$b/check-bilateral-deletion-33.py" --table /tmp/delete-33-refit.txt --min-surplus 240846/10000000000
```

**Prospective test inside Improve.** Using `delete-33-bilateral.txt` instead as input and `--left -320 --right 256` gave a joint refit past the known fixed-trace failure at $-257$ in one round. Its [integer witness, exact half-line proof, and remaining endpoint experiment](minus320-deletion-33.md) are the handoff; the older Work stdout predates them. No change to the graph, arithmetic claim, or live trial of the revised Work prompt. Revert the cue if it prompts repeated fits of settled blocks, delays a stronger analytic test, or treats failure on the inherited sites as unrestricted infeasibility.
