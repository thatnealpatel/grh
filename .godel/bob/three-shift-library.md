# Every deletion of the four-shift support defeats the convex library

At depth $39/20$ take the three second translates $(-7,6,19)/25$ at $3t$, with positive Fourier weights $(3,5,4)/12$. No constant convex mixture of the five tabulated first laws `single-shift`, `hard-pair`, `midgap-sector`, `right-sector`, and `two-term` admits a simultaneous zero answer at those three shifts in the [moment comparison](single-shift-decision.md). In fact every second completion of these first representers has normalized real moment **greater than $.00268$** on this one scalar mask. The other three deletions of $(-7,6,19,33)/25$ also have library separators, given below. These tests include mixing the prime laws *before* taking their second-moment disks, as well as mixing complete witnesses. They restrict a library, not arbitrary first laws or arithmetic phases, and do not show that three shifts suffice.

Write $H(x)=\sum h_l e^{ilx/25}$ for the given mask, $C=\cosh(39/20)/3$, and $d\mu=dx/(2\pi|1/2+ix|^2)$. For first moment $m$, the least possible real second response is

$$\Re\int Hm^2\,d\mu-\int |H|(1-|m|^2)\,d\mu.$$

This follows from the conditional unit-circle second-moment disk. It also bounds shallow interior depths: The multipliers $\cosh(jd)/\cosh(jc)$ are the circle Fourier coefficients of harmonic exit measure on the two edges of the strip, projected onto the periodic angle (apply harmonic extension to each cosine and sine). One can thus replace a shallow conditional depth and phase by a boundary circle law with the same first and second moments. For real first-translate data one may symmetrize at opposite ordinates by conjugation without changing any real translated answer; the Fourier uniqueness theorem then pins the symmetrized first moment when every real first translate is matched.

Set $U=|H|^2\le1$. The majorant $M=1-(1-U)/2-(1-U)^2/8\ge\sqrt U$ follows by truncating the binomial series with negative remaining terms (and by continuity at zero). It is a Laurent polynomial on the shift lattice. For first law $i$ write $m_i=-\sum_a b_{i,a}e^{iax}/(1/2+ix)$, $b_{i,a}=e^{-a/2}\Delta B_i(a)/C$, with $B_i$ the slab expectation of $4X^3-3X$. If $m=\sum\lambda_i m_i$ for convex weights, then the negative of the least response is bounded above by $\sum\lambda_i\lambda_j K_{ij}$, where

$$K_{ij}=\int M\big(1-\Re(m_i\overline{m_j})\big)\,d\mu-\Re\int Hm_i m_j\,d\mu.$$

The constant term is polarized using $\sum\lambda_i=1$. Only the mixed *upper bounds* need checking, not the continuum of mixtures. For the common prime mixture the first representer is linear. Every complete-witness mixture also lies in its disk, so the negative upper bound covers both mix orders.

**Replay.** Run `sage .godel/bob/check-three-shift-library.py` from the repository root, with assertions enabled. The inputs are the five unchanged `*-10-2.txt` law tables at `10c1c87ac21e06f8c8d7df1c32ab86c6a80a2c15`. For the difference integral the checker uses the average of the [difference kernels](separated-second-shifts.md) at $a-b\pm l/25$ for each pair of weighted jumps, since the coefficient of $\Re(m_i\bar m_j)$ is real and even. For the sum integral the kernel is $(1+y_++y_+^2/2)e^{-|y|/2}$ at $y=a+b+l/25$. The constant has kernel $e^{-|l|/50}$. Finite sums with 128-bit outward-rounded balls check all fifteen distinct entries $K_{ij}$ for each mask, without angular sampling or quadrature. For the original deletion of $33$, the closest entry is `midgap-sector` against itself, about $-.002687<-.00268$.

## The three deletions retaining $33$

For each row the weights are in the displayed order of lattice indices, with shifts obtained by dividing by $25$. The replies are $r_l=\Re\int e^{ilx/25}\mathbb E[Z^2\mid x]d\mu$; the lower bound is on $\sum_l h_l r_l$. In particular, the measured spline weights are proportional to $h_l e^{-l/50}$, not $h_l$. Three separate zero replies would force this sum to be zero.

| Deleted index | Retained indices | Fourier weights $h$ | Majorant degree | Largest $K_{ij}$ (rounded) | Uniform lower bound |
|:---|:---|:---|---:|---:|---:|
| $-7$ | $(6,19,33)$ | $(50,35,15)/100$ | 4 | $-.00138430257429$ | $.0013$ |
| $6$ | $(-7,19,33)$ | $(43,35,22)/100$ | 12 | $-.000326564338039$ | $.0003$ |
| $19$ | $(-7,6,33)$ | $(28,42,30)/100$ | 2 | $-.00425775022915$ | $.0042$ |

Use the same polarizations and kernels as above, with $M_d=1-\sum_{n=1}^d a_n(1-|H|^2)^n$, $a_1=1/2$, $a_{n+1}=a_n(n-1/2)/(n+1)$. The positive $a_n$ are the negatives of the nonconstant coefficients of $\sqrt{1-z}$; since $0\le 1-|H|^2\le 1$, every truncation is an upper bound, including at the endpoints by continuity. All Laurent coefficients are rational. The checker tests all fifteen mixed entries separately for each row. In fact the largest entry upper bound in each row is strictly less than the **negative** of its stated lower bound. Thus for every constant simplex vector $\lambda$ the quadratic bound is strictly negative, since the weights $\lambda_i\lambda_j$ are nonnegative and sum to one over ordered pairs. This prices the full disk of the mixed first law, not just convex combinations of sampled replies. Mixing complete witnesses uses linear matching and the same trace marginal, so the mixed law has the same prescribed first moment, the zero higher replies at $t$, and the strict failure mean; its second moment is in that mixed disk.

**Decision.** None of these four triples admits a zero-answer witness from the five laws or their constant mixtures. Reweighting the library cannot settle the three-shift question for these supports. A constructive test needs a new first profile: refit slab probabilities while preserving both first caps and the $8/9$ mean, then check simultaneous feasibility (passing a single scalar direction is only necessary). Alternatively seek a separator against *all* first laws on a fixed triple. The present prices do not cover slab-dependent mixing or any infimum over all common prime laws.
