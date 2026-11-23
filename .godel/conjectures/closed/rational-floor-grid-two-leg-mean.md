---
evidence_revision: 1ac7e41bd8d353968bfaae498f99526d9c84d203
outcome: refuted
---

# Can the two-leg phase mean be summed separately on the rational floor grids?

**Claim tested:** On the nested grids $h_j=2^{-j}$, $m_j=4^j$, take the full metric $w_a(x)=e^{2a|x|}(1+x^2)^2$, $0\le a<1/2$. At fixed smooth nonnegative nonzero compact position cutoff $\rho$, use the [global trace card](../open/rational-normalized-global-geometric-trace.md)'s test $f=b'$ for $0\ne b\ge 0$ smooth and compactly supported in $(0,\log 2)$. On a physical orthonormal basis of each new detail space, write each profile locally as its phase mean times $g(x)=2e^{-x/2}$ plus its centered part. If this split is made on **both** legs of $M_\rho A_f$, do the mean–mean partial sums and the remaining partial sums converge separately as the level grows?

**Refuted at fixed cutoff.** [`Masullo.exists_floorGridMeanPartial_counterexample`](../../../Proofs/Theorems/FloorGridMeanObstruction.lean) gives one such bump $b$ with $\int b'=0$. Set $\rho=b$. For every $0\le a<1/2$ and every starting level $j$, the mean–mean partial sums tend to $-\infty$. In fact, `tendsto_floorGridMeanPartial_atBot` allows any nonzero nonnegative continuous compact cutoff independent of $b$.

Let $E_j$ be the squared norm of the phase-mean functional restricted to level $j$ in the whole-line metric. The $k=2$ column has phase mean $1/2$ at every level but norm tending to zero, so $E_j\to\infty$. Both legs are returned to physical coordinates before convolution. For **any** orthonormal detail basis, `floorGridDetail_trace_split` identifies the mean–mean part of the actual finite matrix trace as $C(E_{j+1}-E_j)$, with both mixed terms and the centered–centered term left in the remainder. Here
$$
C=-2\left(\int \rho(x)w_a(x)e^{-x}\,dx\right)\left(\int b(z)e^{z/2}\,dz\right)<0.
$$
Thus the sum over $n$ successive details is exactly $C(E_{j+n}-E_j)$ (`floorGridMeanPartial_eq`). No rate or interchange of limits is needed.

Separate finite limits are therefore impossible. **If** the recombined traces have a finite limit at this cutoff, the remaining partial sums must cancel the divergence; the proof does not establish that limit. It does not refute an input-only signed pairing or evaluate the global remainder required by the [open parent claim](../open/rational-normalized-global-geometric-trace.md).
