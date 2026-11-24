# The new negative slabs absorb the first-mask probes

In the [deletion comparison](three-term-deletions.md), write $E_k=e^{ik\varphi}$, $I=\{-192,\ldots,192\}$, and $P=\{193,\ldots,256\}$. Put $\mathcal H=\{H_{-7},H_6,H_{19},H_{33}\}$, the four integer product masks defined there. For **each deletion**, independently choose one of the following real first-mask spaces at each of $t$ and $3t$:

- The old span of $E_k$, $k\in I$, enlarged by **all four** members of $\mathcal H$;
- The span of $E_k$ for $k=-192,\ldots,256$.

No refit in these two chosen spaces, or of the three retained real second coefficients, separates. There is one matching law per deletion and pair of choices. It has the **same strict failure surplus** as in the old-span theorem. The conclusion holds before the finite $t$ surcharge and hence also at $L=2048,8192$. This does not match both enlargements at the same height, or the full bilateral 513-site span.

## Proof

Keep both repaired traces fixed. Before the global dilution by $\delta$, the old prime extension has $X=0$ on the 64 slabs $[-j/25,-(j-1)/25)$, $j\in P$. Every old first ramp and the positive-$z$ failure weight vanish there. Specify undiluted values $a_j=\mathbb E X$, $b_j=\mathbb E(4X^3-3X)$ on each slab. Below we solve the two linear matching problems separately, then realize their solutions by a **common** probability law on $X$. Thus no independence assumption about $a_j$ and $b_j$ enters the obstruction.

Use $Y=A$ or $B$, $D=C_t$ or $C$, and the corresponding tabulated trace profile $v=t$ or $m$ and old correction $q=q_t$ or $q_3$ from the deletion proof. Let $y_k=p_k(Y)$ for the zero extension. Dilution multiplies both sides of the new first matches by $1-\delta$, so the undiluted target increment at index $k$ is $d_k=D L_k(v+q)-y_k$. The columns for a change on slab $j$ are zero for $k<j$. For $k,j\in P$ they form the triangular matrix

$$T_{kj}=e^{-k/50}\int_{-j/25}^{-(j-1)/25}e^{-z}(z+k/25)_+\,dz.$$

Its diagonal is positive. For the positive-index enlargement solve $T s=(d_k)_{k\in P}$ by forward substitution. To enclose the exact repair contribution without subtracting large nearly equal coefficients, put $r=e^{-1/50}$. Since $q$ is a sum of $E_{-i}$ with $i\in I$, $L_k(q)=r^{k-192}L_{192}(q)$ for $k\ge192$ by the geometric kernel. At the endpoint $D L_{192}(q)=y_{192}-D L_{192}(v)$ exactly.

For the probe enlargement write $h_{ik}$ for the real coefficient of $E_k$ in $H_i$ and $W=(h_{ik})_{i,\ k\in P}T$. Although only $P$ enters this response matrix, the targets $b_i'=\sum_{k=-256}^{256}h_{ik}d_k$ include **both tails**. Bound the unknown repair term in each target by $D\|q\|_\infty\sum_k|h_{ik}|$. The checker certifies $\det(WW^T)>0$ and encloses the exact solution $s=W^T(WW^T)^{-1}b'$. Thus every probe matches the *same* admissible trace, not merely its separate price.

For each combination of solutions take $a_j$ from the $t$ calculation and $b_j$ from the $3t$ calculation. The atom pairs $(X,4X^3-3X)$ at $X=1,1/2$ are $(1,1),(1/2,-1)$; their negatives are also available. The coefficients in this basis are $(2a_j+b_j)/3$ and $2(a_j-b_j)/3$. Use their absolute values as probabilities on the corresponding signed atoms and put the remaining probability at $X=0$. The maximum sum of those probabilities over all slabs and the four combinations has the following outward upper bounds:

| Deleted index | Upper bound |
|---:|---:|
| $-7$ | $0.243$ |
| $6$ | $0.149$ |
| $19$ | $0.195$ |
| $33$ | $0.157$ |

The modified prime law is therefore admissible. Apply the original dilution. The old first answers, the three retained second matches, and the positive-$z$ mean are unchanged. Linearity on the chosen spaces and the original price comparison finish the proof.

**Check:** Run `/opt/sage-10.9/bin/python .godel/bob/check-deletion-laws.py` with assertions enabled. The original finite-price rejection still tests the zero extension; it is not contradicted by this different prime law.

**Handoff:** Do not refit with a single probe, all four probes, or just additional positive indices as above. To test a genuinely new two-sided direction, start with the positive-index law for the deletion of 33. Subtract from its probe all terms at $k\ge-192$, which already match. Compute the remaining negative-tail mismatch with the repaired trace. The free negative slabs have *zero* response to those indices; more fitting of these slabs alone cannot change that mismatch. If it is nonzero, price a change of trace preserving the enlarged span before a global refit. Failure of one such repair would reject only that repair, not prove separation. Other triples, the unrestricted three-versus-four question, and the signed arithmetic premise are open.
