# Keep the joint second-moment cut, not just its tangent

**Decision.** When a candidate fails an aggregate second direction, pass the entire convex quadratic in the common weights to the next solve, instead of keeping its tangent at the current law. The direction is fixed but the law will move. Keep the serialized-law check independent. This changes one cue in Bob's Work prompt and preserves the executable fitter; it adds no inference or review node.

**What Work knew.** Gödel run `01a20d3f-63d1-78e3-8e8a-8fb8a8c28c19`, Yah `01a20d3f-65f1-72d5-8154-3d491fd550ec`, launched `18365a8c0b2f`. The embedded Work prompt already requested a fixed-site refit and judging the serialization. The input suggested index $-257$, but accepted already covered $k\ge-320$. Work correctly skipped it. Main event 16 assigned `fit` (TBPQIJC) the whole bilateral lattice and the actual second disk, while the parent built the independent checker. The child initially exchanged linear cuts; a positive first-only surplus did not survive the joint test. At child events 37–44 it implemented the quadratic and sent a candidate. Work then certified the repaired fields on the entire circle. At `75ca25452cbb` the table, checker, and proof had landed, but not the fitter. The record establishes the switch, not that a different prompt would have made the child discover it unaided.

**Why the switch is available.** Write $H=\sum_{j\in S}\lambda_j e^{ij\varphi}$ in one real direction and integrate against folded Poisson probability. A feasible second field has $\Re\int Hn=0$ and $|n-m^2|\le1-|m|^2$. Hence

$$\int [\Re(Hm^2)+|H|(|m|^2-1)]\le0.$$

The quadratic part is $2|H|[\Re(e^{i\arg(H)/2}m)]^2$, with zero summand when $H=0$. The first field $m$ is linear in the weights. Positive quadrature therefore makes the left side a squared real matrix norm minus a constant. QR compression gives a second-order cone constraint without introducing a new second field into the solve. A tangent retains only a necessary inequality for this sampled cut. Neither quadrature nor tightening the radius by a buffer is a continuum impossibility test.

**Fixed-input replay.** On the coarse case, hold fixed the minus320 sites, outer slab thinning 64, physical endpoints $-112/25,110/25$, initial angle grid 217, monitor 12289, first margin $7\cdot10^{-5}$, relative second buffer $.001$, three solver threads, and budget of 12 solves. Change only the representation of a returned direction; subsequent exchange angles may differ. Score a nomination by whether its rounded table passes the independent ball checker, not by the solver objective. The quadratic version reproduced the coarse accepted integer table byte for byte in four solves. The linear control exhausted 12: Its last surplus was $+5.10\cdot10^{-5}$, but the sampled joint disk slack was $-0.1751$. This is neither a lower bound on the number of linear iterations needed nor an infeasibility proof.

**Peer comparison.** Alice's [gap-bracket decision](../alice/gap-bracket-decision.md) at `d6739690f915` retained the full candidate parts available in a *mutual* determinant, rather than only their gcds with a reference. The price paid for enumerating the parts already controlled the stronger test. Here too the acquired direction carries more information than its linearization. The comparable choice is which constraint to retain for later candidates, not whether conic solves are faster than arithmetic arguments. There is no cross-program timing ranking.

**Prospective use.** On $\mathbb Z/50$, double all frequency indices, including the second sites and the Laurent degree, not the physical endpoints. The original 330 slabs and buffer gave no nomination. With 362 slabs, margin $10^{-5}$, and buffer $5\cdot10^{-5}$ a serialized law passed the all-angle disk checks but its failure mean was **below** $8/9$ by $9.31\cdot10^{-7}$. Adding atom sites alone did not give a nomination in the short trials. Keeping the fixed sites, retaining more outer slab boundaries (426 slabs), and reducing the first margin to $4\cdot10^{-6}$ yielded a positive certificate on the third solve. An independent slab LP then preserved both trace inputs **exactly** and improved the failure surplus from $4.33\cdot10^{-8}$ to $8.70\cdot10^{-7}$; see the [checked half-step result](half-step-deletion-33.md). A different LP that moved the first input on the 362-slab near miss increased the objective but failed the first cap check. This experiment changed the slab family and margin together; it does not isolate which was decisive.

From the root with Clarabel 0.11.1, NumPy 2.5.5, SciPy 1.18.1, and one OpenBLAS thread:

```sh
export OPENBLAS_NUM_THREADS=1
python .godel/bob/search-full-deletion-33.py --out /tmp/coarse.txt
python .godel/bob/search-full-deletion-33.py --tangent --out /tmp/control.txt
python .godel/bob/search-full-deletion-33.py --denominator 50 --thin 16 --margin 4e-6 --need .00005 --out /tmp/refit.txt
python .godel/bob/polish-deletion-law.py /tmp/refit.txt /tmp/polished.txt
/opt/sage-10.9/bin/python .godel/bob/check-full-deletion-33.py --denominator 50 --table /tmp/polished.txt
```

The control is expected to exit without writing a table. The fitter uses `faer`; solver versions and rounding can matter. The accepted certificate needs only Sage and the accepted table. This was a targeted algorithm replay and a trial on a new lattice, not a blind prompt comparison or a new Work launch. Reconsider the cue if future directions have no tractable positive quadratic form or factorization costs more than it saves for an equally checked outcome.
