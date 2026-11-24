# Delete 33: one matching law on the full bilateral first span

At depth $c=39/20$, retain the second shifts $S/25=(-7,6,19)/25$ at $3t$. There is **one common prime law and one trace law at each height** matching all first indices $I=\{-256,\ldots,256\}$ at both heights simultaneously, with zero second answers on $S$ at $3t$ and zero orders two through ten at $t$. The failure surplus is greater than $3.146\cdot 10^{-5}$. In particular no refit of the two first masks in these spans or of the three retained second coefficients gives a positive priced margin in the [deletion comparison](three-term-deletions.md). This includes the finite prices at $L=2048,8192$. It is not an obstruction for arbitrary first shifts or for a different triple.

The base `766e1d844630083d0987c269b6903528be5f769e` covered [the positive-side extension and, separately, the four probes](free-slab-extensions.md) via the new negative slabs. The bilateral experiment refits the prime law and both traces together; it does not require the old law or its traces to stay fixed.

## Table and moment coordinates

Put $\varphi=x/25$, $d\mu=dx/(2\pi(1/4+x^2))$, $C=\cosh(c)/3$, $C_t=C/(2\cos(\pi/12))$, and

$$p_k(Y)=\int e^{-z-k/50}(z+k/25)_+Y(z)\,dz,\qquad L_k(v)=\Re\int e^{ik\varphi}v\,d\mu.$$

In the [table](deletion-laws/delete-33-bilateral.txt), each prime row gives $400z$ then pairs $(10^9u,p)$ for a probability law on $u\in[0,1]$ to the next row, with the last row extending to infinity. Use $X=0$ before the first row at $-256/25$. The weight $p$ is divided by the sum of weights in its row. The **same** atoms define $A=\mathbb E X$, $B=\mathbb E(4X^3-3X)$ and $U=\mathbb E u$ with $X=2u^2-1$.

Trace row $i$ applies to $[\pi(i/512)^2,\pi((i+1)/512)^2]$ in $\varphi$. The first two integers are the real and imaginary parts of the unit-disk proxy $10^9v_t^0$. The remaining pairs are angles in billionths of a turn and positive relative weights for one circle law at $3t$, with moments $m^0=\mathbb E Z$, $n^0=\mathbb E Z^2$. Reflect by conjugation at negative angles and extend periodically. The checked targets, in support-price signs, are $p_k(A)=C_t L_k(v_t)$, $p_k(B)=C L_k(m)$ for every $k\in I$, and $L_j(n)=0$ for every $j\in S$.

## Exact correction and admissibility

The table is preliminary; the following formula defines the witness exactly. Let $Q_J(b)=\sum_{j\in J}(G_J^{-1}b)_j e^{-ij\varphi}$, with $(G_J)_{ij}=e^{-|i-j|/50}$ on a sorted set $J$. Then $L_i(Q_J(b))=b_i$ for $i\in J$ and $\|Q_J(b)\|_\infty\le\|G_J^{-1}b\|_1$. For $r=e^{-1/50}$ and consecutive correlations $p_i=r^{j_i-j_{i-1}}$, the rows of the map $b\mapsto(b_0,(b_i-p_ib_{i-1})/\sqrt{1-p_i^2})$ whiten $G_J$, by its product identity. The checker applies the transpose of that map to itself to bound the correction norms.

Using the exact pre-repair profiles, set

$$q_t=Q_I\big(p(A)/C_t-L(v_t^0)\big),\quad
q_3=Q_I\big(p(B)/C-L(m^0)\big),\quad q_2=Q_S\big(-L(n^0)\big),$$

where the vectors run over the indicated index sets. Write $e_t,e_3,e_2$ for the corresponding norm bounds. The replay verifies $(1-\delta)e_t<\delta$ and $2(1-\delta)(e_3+e_2)<\delta$ for $\delta=10^{-6}$. Dilute the prime law by mass $\delta$ at $X=0$. Both first prime profiles scale by $1-\delta$. Take $v_t=(1-\delta)(v_t^0+q_t)$, still in the unit disk. At $3t$ keep mass $1-\delta$ of the table law and **add** the measure with density

$$\delta+2(1-\delta)\Re(q_3 e^{-i\theta}+q_2 e^{-2i\theta})$$

relative to uniform circle measure. It is positive, has mass $\delta$, and adds exactly the first and second moment corrections $(1-\delta)q_3,(1-\delta)q_2$. Thus the repaired law satisfies the targets exactly; residual balls are not treated as equalities.

For zero-answer signs use the opposite first circle means. At $3t$ rotate the repaired circle law by $\pi$; the second moment is unchanged. At $t$ realize $m_t=-v_t/(2\cos(\pi/12))$ using the [twelve-angle law](single-shift-10-2.md): weights $(1-2|m_t|\cos\psi_j)/12$ at $\psi_j=(2j+1)\pi/12$, rotated by $\arg(-m_t)$ when nonzero. The weights are nonnegative and the roots-of-unity sums give the specified first mean and moments two through ten zero. These are conditional circle laws at the shallow edge depths in the accepted comparison.

## Price and replay

The failure surplus is $M-8/9$ with $M=(1-\delta)\int z_+e^{-z}U(z)\,dz+\delta/\sqrt2$. Evaluating the prime infimum on the repaired law gives an upper bound by $8/9-M$ plus its two first answers. The ideal $t$ price $C_t\int|H_t|\,d\mu$ bounds its first answer from above. Averaging the $3t$ angular maximum over the repaired law bounds the $3t$ price from below by its matching first answer because all three second terms vanish. Hence the priced margin is at most $8/9-M$ for arbitrary real coefficients in the specified spans. The [finite $t$ recovery](sparse-10-2.md) is a positive-mask sum and prices at least the ideal cost by the triangle inequality; no finite-to-limit approximation is used.

Run with SageMath 10.9 and assertions enabled, from the repository root:

```sh
/opt/sage-10.9/bin/python .godel/bob/check-bilateral-deletion-33.py
```

The standalone checker reads only the integer table and uses 512-bit real and complex balls. For the prime side it checks the ramp knots and zero are slab boundaries and integrates each original ramp exactly in terms of exponential endpoints, including the final tail. The trace moments use the [folded Poisson density and character recurrence](frozen-deletions.md), integrated over whole cells, including both frequency signs and the zero index. The checker bounds the repairs and recomputes the strict surplus after dilution.

## Numerical nomination

The restricted model maximizes the failure mean under the displayed moment equalities. It uses 813 constant prime slabs with all bilateral ramp knots, the 512 folded trace cells above, a full normalized unit disk for each $t$ cell, and nonnegative, row-normalized atom weights on finite dictionaries for the prime and $3t$ cells. No first coordinates are dropped. The
[dual cone assembly](search-two-shift-10-2.py) uses ramp values at exponential cell barycenters and mean characters from 20-point Gauss integration per trace cell, with the corresponding cell masses as objective weights. The initial prime dictionaries include $u=0,1/2,3/4,7/8,1$; the initial circle dictionaries include the four quarter turns. They also use extrema from the old-mask seed. The search exchanges in violated angular extrema, for at most six rounds. Clarabel 0.11.1 used one thread, the `faer` direct solve, a 120-iteration cap per inner solve, and requested primal feasibility and absolute/relative gap tolerances of $2\cdot10^{-11}$.

The returned cut objective in **margin** signs was $-3.1645983\cdot10^{-5}$. The extracted laws instead had numerical **surplus** $+3.1645964\cdot10^{-5}$ before dilution and final weight rounding. These are restricted-model floating results, not claims of optimality. The admissibility certificate uses only the final table (four prime atoms per slab, five circle atoms per cell after numerical support reduction) and the exact construction above. Substitution into the original moment equations, not just the cone rows, gives the following outward pre-repair bounds in the ball replay:

| Moment block | Maximum absolute residual | Correction norm bound |
|---|---:|---:|
| First at $t$ | $1.164\cdot10^{-9}$ | $1.649\cdot10^{-8}$ |
| First at $3t$ | $3.993\cdot10^{-10}$ | $2.050\cdot10^{-8}$ |
| Second at $3t$ | $3.978\cdot10^{-10}$ | $4.924\cdot10^{-10}$ |

The repaired surplus is enclosed at $3.14641520622\ldots\cdot10^{-5}$. Do not repeat the delete-33 reprice/refit within these first spans: the common-law obstruction is now checked. Other deletions and the extension beyond these first spans were not tested.
