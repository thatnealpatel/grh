# Three-term deletions cannot separate on the old first span

Delete any one index from the [four-term second mask](four-shift-10-2.md) at $3t$. In the $(10,2)$ comparison at $c=39/20$, **no real coefficients on the retained triple and no refit of either first mask on $l=-192,\ldots,192$ can give a positive priced margin**. The shifts are $l/25$. This is a separate obstruction for each deletion, not one law for all four. The first span tested includes all 385 indices, not just the 209 used by the four-term search. No restriction on coefficient size is needed.

| Deleted index | Joint refit margin, chord / barycenter | Finite surcharge at $t$ | Certified failure surplus, lower bound |
|---:|---:|---:|---:|
| $33$ | $-35.0854$ / $-34.8461$ | $0.0151$ | $24.13$ |
| $19$ | $-20.7803$ / $-20.5643$ | $0.0162$ | $16.83$ |
| $6$ | $-49.1342$ / $-48.8546$ | $0.0164$ | $44.50$ |
| $-7$ | $-37.0929$ / $-36.6802$ | $0.0178$ | $32.92$ |

All entries are in units of $10^{-6}$. The two middle columns are floating reprices of nominated masks, not optimized upper bounds. Both first masks and all retained second coefficients were free. The refit used the previous 209 first sites, six cut rounds, phase-aligned grouping of the $t$ rows, and the full $L=8192$ finite sum in the reprice. **The proof is the last column:** The negative of the surplus is an upper bound on the priced margin throughout the larger span, even before the finite surcharge.

## Matching on the finite span

Put $C=\cosh(c)/3$, $C_t=C/(2\cos(\pi/12))$, $d\mu=dx/(2\pi(1/4+x^2))$, and $\varphi=x/25$. The [tables](deletion-laws/) specify one prime law and preliminary trace moments per deletion. A prime row gives $400z$ followed by pairs $(10^9 u,p)$, constant to the next row and extended forever after the last. Normalize each row by its own sum of weights $p$. Set $X=0$ to the left of the first row; on the rows $X=2u^2-1$. Write $A=\mathbb E X$, $B=\mathbb E(4X^3-3X)$, and $U=\mathbb E\sqrt{(1+X)/2}$. For a first index $l$ and either profile $Y=A,B$ the prime answer in multiplier coordinates is

$$p_l(Y)=\int e^{-z-l/50}(z+l/25)_+Y(z)\,dz.$$

The trace row for cell $i$ gives the real and imaginary parts of $10^9 t_i$, followed by pairs (angle in billionths of a turn, relative weight) for a circle variable $Z_i$ with moments $m_i=\mathbb E Z_i$, $n_i=\mathbb E Z_i^2$. The checker verifies $|t_i|\le1$ and uses exact normalized row probabilities. Use conjugate reflection on negative angles and extend periodically. For $L_l(v)=\Re\int e^{il\varphi}v\,d\mu$, the equalities we need are

$$p_l(A)=C_t L_l(t),\qquad p_l(B)=C L_l(m)\quad (|l|\le192),\qquad L_k(n)=0\quad(k\text{ retained}).$$

These are support-price signs. In the zero-answer convention use the opposite first circle means, rotating $Z$ by $\pi$ at $3t$ without changing its second moment. At $t$ the disk $|t|\le1$ gives an actual first circle mean of magnitude at most $1/(2\cos(\pi/12))$, with moments two through ten zero by the [twelve-angle construction](single-shift-10-2.md).

**Exact repair.** Before repair, let $v_t=p(A)-C_tL(t)$, $v_3=p(B)-CL(m)$, and $v_2=-L(n)$ on their respective index sets. On any one such ordered set $I$, the multiplier

$$q(v)=\sum_{j\in I}(G^{-1}v)_j e^{-ij\varphi},\qquad G_{ij}=e^{-|i-j|/50},$$

has $L_i(q)=v_i$ and $\|q\|_\infty\le\|G^{-1}v\|_1$. The inverse used here follows from the [consecutive-correlation difference formula](frozen-deletions.md). Abbreviate $q_t=q(v_t)/C_t$, $q_3=q(v_3)/C$, and $q_2=q(v_2)$. The checker bounds their norms by $e_t,e_3,e_2$ respectively. With $\delta=10^{-6}$ it certifies

$$(1-\delta)e_t<\delta,\qquad 2(1-\delta)(e_3+e_2)<\delta.$$

Mix the prime law with mass $\delta$ at $X=0$. Its two answers scale by $1-\delta$. Use $(1-\delta)(t+q_t)$ in the unit disk. At $3t$ keep mass $1-\delta$ of the tabulated law and **add a positive measure** with density relative to uniform angle $\theta$ given by

$$\delta+2(1-\delta)\Re\big(q_3 e^{-i\theta}+q_2 e^{-2i\theta}\big).$$

It has mass $\delta$ and the two desired correcting moments. Thus all displayed equalities hold *exactly*, while the repaired mean is $(1-\delta)\int z_+e^{-z}U(z)\,dz+\delta/\sqrt2$. This proves the last column by outward rounding. Rounding a tiny residual to zero without the repair would not prove the result for arbitrary multipliers.

**Price implication.** Evaluate the prime infimum on this law, average the $3t$ angular maximum on its matching repaired circle, and bound the first $t$ contribution by $C_t\int|H_t|\,d\mu$. The linear terms cancel or have the favorable sign and the remaining upper bound for the signed margin is $8/9$ minus the repaired mean. The [finite construction](sparse-10-2.md) recovers $H_t=\sum_pD_pV_p$ with $D_p\ge0$, hence $T_L=C_t\int\sum_pD_p|V_p|\,d\mu\ge C_t\int|H_t|\,d\mu$ whenever it recovers these indices. In particular the result holds for the actual costs at $L=8192$ and $2048$; it is not based on assuming that a limiting price equals a finite price.

**Integration and replay.** The prime rows split at zero and every first ramp knot, so only elementary exponential mass and first moment integrals are needed, including on the final tail. On trace cell $[\pi(i/512)^2,\pi((i+1)/512)^2]$ integrate characters against the folded Poisson density $(1-r^2)/(\pi(1+r^2-2r\cos\varphi))$, $r=e^{-1/50}$. The checker uses its CDF, logarithmic first sine integral, and [character recurrence](frozen-deletions.md) through order 256 with 512-bit balls in the extended checker. The nominations came from dual multipliers of a finite cone discretization using slab laws and cell laws; no optimality or discretization error claim enters the proof. Run, from the repository root with SageMath 10.9 and assertions enabled:

```sh
/opt/sage-10.9/bin/python .godel/bob/check-deletion-laws.py
```

## The obstruction does not persist unchanged on the next span

For each table, **one explicit first mask at $t$** on $|l|\le256$ detects that repaired prime law, irrespective of its trace completion. This tests the prime law *as extended above*, not all ways of changing the negative slabs. For the two integer columns $a_j,b_j$ of its `.probe` file ($0\le j\le256$), form $H=(\sum a_j e^{ij\varphi})\overline{(\sum b_j e^{ij\varphi})}$. Write $h_l$ for its real Laurent coefficients and $V=|(1-\delta)\sum_l h_l p_l(A)|$ for the repaired answer. The jump at $z$ of the undiluted $A$ contributes its jump size times the step integral $e^{s/2}$ if $z+s\le0$, and $(1+z+s)e^{-z-s/2}$ otherwise, where $s=l/25$. The checker uses this formula through the extended range, not the old slab-knot shortcut.

The ideal cost is at most $C_t\sqrt{(a^TGa)(b^TGb)}$ by Cauchy–Schwarz. Each ratio of $V$ to this upper bound exceeds $1.00026$. The probe columns were nominated by maximizing this bilinear ratio numerically; their optimality is immaterial. More importantly, the [finite FFT price](check-four-shift-10-2.py) gives the following $V/T_L(H)$ (rounded displays):

| Deleted index | $L=8192$ | $L=2048$ |
|---:|---:|---:|
| $33$ | $1.001264$ | $0.991324$ |
| $19$ | $1.000194$ | $0.995762$ |
| $6$ | $1.009862$ | $1.004590$ |
| $-7$ | $1.005791$ | $0.997532$ |

At 8192 *all four* ratios exceed one. At 2048 only the deletion of 6 clears one **on its specified probe**. Hence the finite price can change an extension decision even though its surcharge was small on the initial separator fits. These tests distinguish the individual tabulated laws, not the set of prime laws: A prime infimum for a separator must range over that whole set.

## Decision

The minimum remains three or four. For each of the four triples the [five-law constant library](three-shift-library.md) fails with all first translates imposed. Conversely the finite-span obstructions here match all three replies simultaneously but not all first translates. A [separate all-first refit](triple-named-refit.md) narrows the named scalar margin for the deletion of $33$ without reaching zero.

Do not repeat the three-term coefficient search on the old first span. The original next fixed-support experiment was: Retain $(-7,6,19)/25$, enlarge just the $t$ span by its integer probe direction, and jointly refit with the $L=8192$ price. Admit new prime slabs down to $-256/25$ in the primal alternative, rather than fixing an untested part of the law. A new matching witness would rule out that one-direction enlargement; a candidate positive margin needs the full prime floor and both trace prices checked again. The signed arithmetic lower bound at actual endpoint failures remains a separate, open premise.

**Update:** The [free-slab repair](free-slab-extensions.md) settles this experiment without a joint refit. It also obstructs all four probe directions together, or all 64 additional positive indices, independently at each height. These alternatives do not assert their union at the same height. See the new handoff before trying a two-sided extension.
