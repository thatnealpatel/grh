# The complete pool balance at a genuine shift

At $q=100000007$, $\gamma=1/4$, and $r=D^2$, take the **whole prime band** and the arithmetic $H_r$ of the [joint arc test](jointly-separated-arc-test.md). For an unsigned pool $V$ of 16 starts, let $S(V)$ include both $|y|\le8$ cuts, both actual rounded slots, both tapers in the quadratic coordinate, and every labeled split. Put $P=\sum_V S(V)_+$ and $N=\sum_V(-S(V))_+$. Then $H_r=P-N$. These are not the Jordan masses obtained by taking positive and negative parts *before* summing within a pool.

| Shift $d$ | Eligible starts | Separated pools | Pools surviving the minimum-start bound | Positive / negative / zero pool totals |
|---:|---:|---:|---:|---:|
| 4 | 44 | 2,160 | 0 | 0 / 0 / 2,160 |
| 20 | 52 | 18,656 | 0 | 0 / 0 / 18,656 |
| 26 | 44 | 28,592 | 720 | 21 / 11 / 28,560 |

These are the three smallest nonempty *unsigned* pool families over $1\le d\le5D$. The selection stops at the first survivor of a necessary unsigned window test, not the first favorable sign. In particular $A_d>1/4$ at all three shifts, but the nulls are failures of the windows, not perfect cancellation. At $d=26$ the full ordered counts after the two windows, the two gates, and the two nonzero tapers are 214,990,848, 104,882,688, and 77,096,448, respectively. All zero pool totals in the table are structural.

In units of $10^{-21}$ the outward bounds are

$$2.5854379316909998<P/10^{-21}<2.5854379316910000,\qquad
1.2205507807515102<N/10^{-21}<1.2205507807515103.$$

Thus $1.3648871509394895<H_r/10^{-21}<1.3648871509394896$. Negative totals pay about 47.21% of the positive totals. The residual divided by $((X/D)16^{-n}/t)^2$ lies in $(16265.69,16265.70)$. That denominator is a **reference scale** from the asymptotic common-dip implication, not a proved finite threshold. One shift at one center is neither evidence of a common dip nor an obstruction to an $o(D)$ exceptional-shift estimate.

**Reproduce.** Run `python3 .godel/bob/check-complete-shift.py` with assertions enabled (Python 3.12, standard library). Gaps of at least 50 are equivalent to joint separation here, force distinct endpoints, make every slot private, and leave no starts within $R_*<2$ of the other support. An independent skip-or-take count checks the enumeration. To see the unsigned pruning bound, put the minimum start of $V$ on the positive side of its block *only for this bound*. Write $f(p)=1+d/p$. A lower bound $R$ for its ratio is $f(\min V)$ times the three smallest remaining $f$'s divided by the four largest remaining $f$'s. If $R>1$ and $t(1-1/R)>8$, neither orientation can pass. This rejects a pool without any assumption about its gates or phases.

For the survivors, join disjoint four-sets in order of their ratios, using pool incidence and complementary supports. Test the exact fifth-power window in each orientation. Count the actual rounded positive labels separately, not by doubling under reversal. For an eight-start support sum $gT(a)\cos a$ and $gT(a)\sin a$ over its balanced signings, with $g$ the number of admissible designated starts. The dot product for complementary supports recovers the cosine difference. Restore $2(3!4!)^2\prod_{p\in V}w_p$ for unordered support pairs. The script encloses logarithms, phases, and accumulated weights outward, and checks the optimized calculation by direct label and phase evaluation on fixtures, including one block with two valid labels in one orientation and one in the reverse.

**Next decision.** Do not seek another isolated negative coefficient to decide whether the negative mass suffices. For an allocation argument, bound how much *simultaneous* positive demand can be paid with each negative capacity used only once, distinguishing terms from net pool totals. For a direct signed argument, no allocation is required: The missing estimate is an upper bound on the split-weighted residual on the required shifts, with the precision of the [joint comparison](jointly-separated-arc-test.md), not a fixed fraction of $P$. Use the table as a finite check on an identity or on an inequality claimed at this center, not as a test that can refute an eventual bound. See the [decision review](pool-balance-review.md) for why this is a local handoff.
