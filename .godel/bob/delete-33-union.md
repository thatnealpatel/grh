# The delete-33 positive-index law cannot match its own probe at t

**Fixed-law result.** At the accepted base `766e1d844630083d0987c269b6903528be5f769e`, fix the delete-33 law from the positive-index branch of [the free-slab extension](free-slab-extensions.md) at both heights. Its admissible baseline traces match every first coefficient at both heights for $-192\le k\le256$, and the three retained second coefficients $-7,6,19$ at $3t$. Adding $H_{33}$ at $t$ rejects this **particular prime law**: no change of the $t$ trace preserving the enlarged first coefficients fits its probe. This does not assert separation from other prime laws.

## Baseline and sign of the missing answer

Use the support-price signs of [the deletion certificate](three-term-deletions.md). Put $r=e^{-1/50}$, $C=\cosh(39/20)/3$, $C_t=C/(2\cos(\pi/12))$, $E_k=e^{ik\varphi}$, and $L_k(v)=\Re\int E_kv\,d\mu$. Write $I=[-192,192]\cap\mathbb Z$, $P=[193,256]\cap\mathbb Z$, $J=I\cup P$, and $N=[-256,-193]\cap\mathbb Z$. The entries $a_i,b_i$ of [`delete-33.probe`](deletion-laws/delete-33.probe) give $H=H_{33}=(\sum_i a_iE_i)\overline{(\sum_i b_iE_i)}=\sum_k h_kE_k$. For a real-coefficient mask $F$ put $L_F(v)=\Re\int Fv\,d\mu$.

Let $v_0=(1-\delta)(t_0+q_t)$ be the $t$ baseline, where $t_0$ is the tabulated unit-disk profile, $q_t$ its old Gram correction, and $\delta=10^{-6}$. Let $p_k^*$ be the **diluted** $t$ prime answer after the positive-index extension. Then $p_k^*=C_tL_k(v_0)$ on $J$. On $P$ this is the triangular slab identity: solve for the mean on slab $[-j/25,-(j-1)/25)$, $j\in P$, using the ramp response $T_{kj}$ of the free-slab extension. The right-hand side before dilution is $C_tL_k(t_0+q_t)-p_k(A)$, with the original table and zero extension used in $p_k(A)$. For $k>192$, $L_k(q_t)=r^{k-192}L_{192}(q_t)$ by the Gram kernel. Every added slab gives exactly zero to $p_k^*$ for $k\le192$, including the entire negative tail. In particular on $N$, $p_k^*=(1-\delta)p_k(A)$, whereas the trace still includes the correction $q_t$.

The positive-index construction and the old repair equations determine the baseline **exactly**. For the joint prime law on each new slab use $A_j,B_j$ from the two triangular solves. At $X=1,1/2$ the moment pairs $(X,4X^3-3X)$ are $(1,1),(1/2,-1)$, and their negatives occur at the negative atoms. Use masses $|(2A_j+B_j)/3|,|2(A_j-B_j)/3|$ on the atoms with the corresponding signs, and the rest at $X=0$, before the original dilution. The largest sum of these two masses is below $0.156195265$. The $t$ Gram correction has $\ell^1$ coefficient bound $<1.464\cdot10^{-8}$; the $3t$ first and second corrections have bounds $<1.760\cdot10^{-8}$ and $<2.908\cdot10^{-10}$. These pay for the unit disk at $t$ and the positive correcting density at $3t$ as in the original certificate. Since none of the new slabs meets $z>0$, the same failure surplus is in $(0.00002413784023,0.00002413784024)$.

Subtract the contributions from $I$ and $P$ separately: the former are the old retained answers, the latter are the fixed positive-index matches. In the convention **prime minus trace**, the required change is

$$R=p^*(H)-C_tL_H(v_0)=\sum_{k\in N}h_k\big[(1-\delta)p_k(A)-C_t L_k(v_0)\big].$$

Each entry below is the lower endpoint of a certified interval of width $0.01$, in the original integer-mask normalization.

| Quantity | Lower endpoint |
|---|---:|
| Prime contribution on $N$ | 527,324,409,074.03 |
| Baseline trace contribution on $N$ | 465,073,773,170.19 |
| **Required increase $R$** | **62,250,635,903.84** |
| Matched old contribution on $I$ | 60,874,450,406,804.82 |
| Matched positive contribution on $P$ | 524,014,906,040.29 |
| Of the prime contribution on $P$, increment from the new slabs | −26,691,396,721.36 |
| Total matched contribution on $J$ | 61,398,465,312,845.11 |
| Full baseline $C_t L_H(v_0)$ | 61,863,539,086,015.31 |
| Full fixed prime $p^*(H)$ | 61,925,789,721,919.15 |

## Uniform price for all trace repairs

Let $w$ be any measurable change, without a truncation or regularity assumption. To qualify, it must satisfy $L_k(w)=0$ for **all** $k\in J$ and $|v_0+w|\le1$ almost everywhere. The aggregate probe response is then exactly $C_tL_H(w)=C_t\sum_{k\in N}h_kL_k(w)$, not the sum of separate per-coefficient response bounds. Price the full mask against the new trace, then subtract the baseline:

$$C_t L_H(w)\le C_t\int |H|\,d\mu-C_tL_H(v_0)
 \le U-C_t L_H(v_0),\qquad U=C_t\sqrt{(a^TGa)(b^TGb)},\quad G_{ij}=r^{|i-j|}.$$

The first inequality is the pointwise disk bound; the second is Cauchy–Schwarz on the two factors of the original probe. It prices every admissible change at once, including directions not expressible in a finite basis and changes that spend more than the baseline's uniform dilution slack. The finite price $T_L(H)$ can also be used in place of $U$ when it recovers the mask, since it dominates the ideal disk price. The same outward cent convention applies here:

| Price used | Total price | Price minus baseline | Fixed prime minus price |
|---|---:|---:|---:|
| $U$ (ideal upper bound) | 61,866,026,525,025.04 | 2,487,439,009.73 | 59,763,196,894.10 |
| $T_{8192}(H)$ | 61,874,265,747,026.86 | 10,726,661,011.55 | 51,523,974,892.29 |
| $T_{2048}(H)$ | 62,494,696,068,706.82 | 631,156,982,691.51 | −568,906,346,787.68 |

The ideal upper bound allows less than $4.0\%$ of the required increase; it is not claimed to be the optimum subject to the preserved moments. The fixed law even loses to the standalone probe at $L=8192$ (ratio $1.00083272058698\ldots$). The quoted $L=2048$ price does not witness rejection, but does not give an admissible repair. The ideal rejection already uses the full probe and so also applies to any variant with the same $t$ prime answers, independently of the $3t$ trace or prime-side second profile.

## Replay and next decision

From the repository root, with SageMath 10.9 and assertions enabled:

```sh
/opt/sage-10.9/bin/python .godel/bob/check-delete-33-union.py
```

The [checker](check-delete-33-union.py) reads the original delete-33 table and integer probe. It uses exact rational row probabilities and 512-bit outward balls for the prime ramp and Poisson-cell integrals, including the full final prime tail and full folded trace period. It takes two backward differences of the triangular slab equations after extracting $r^k$: each resulting column vanishes below its knot $j$ and is affine for $k\ge j$, so only its $j$ and $j+1$ entries survive the differences. It cross-checks by inserting the two slab jumps in the original prime functional. The old Gram repairs and triangular identities give exact moment equality, not equality to a solver tolerance. The direct extended moment comparisons enclose discrepancies below $10^{-48}$; the full residual and its pure negative-tail reconstruction differ by less than $10^{-32}$ in the computational enclosures. The finite prices use the existing 128-bit ball FFT, including its deconvolution and weights, not a sampled ideal norm. The displayed ball errors are below $10^{-40}$ for the residual and full prime and trace answers, and below $10^{-20}$ for both finite prices; no unbounded integration tail is dropped.

The obstruction to **reusing this law** is now decided. Do not infer a separator by minimizing against only this law. In fact, the parallel campaign output `bcb3773b73605d02c17cfa0bda7326673960b4e5` (sibling based on `766e1d84`, `.godel/bob/bilateral-deletion-33.md`) reports a checked **different** law for delete 33 that matches the whole bilateral span at both heights. That span contains the union considered here, so do not repeat a global union refit for this triple if the bilateral certificate is adopted. The analogous bilateral obstructions for the other deletions, and the signed arithmetic premise, are not decided by this fixed-law experiment.
