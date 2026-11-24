# A full-profile prime law for the mid-gap two-shift sector

At depth $c=39/20$, the [248-slab table](midgap-sector-10-2.txt) gives a single admissible prime profile for the fixed-spline comparison in [two-term-10-2.md](two-term-10-2.md). Its shallow law at $3t$ can be chosen to match zero for each same-sign mask

$$H(x)=a e^{isx}+b e^{i(s+d)x},\qquad ab\ge0,\quad |a|+|b|=1,\quad s\le-9/50,\quad 1\le d\le2.$$

Here $s$ is the earlier shift regardless of which coefficient is larger. The normalized scalar gap $F(H)$ is strictly above $3.51\cdot10^{-5}$ on this half-strip, uniformly in the two coefficient magnitudes. This does not claim simultaneous matching by this table for all pairs or all signs; for joint matching at a fixed pair, the opposite-sign separating directions must also be excluded. The result is in the comparison model, not arithmetic realizability or RH/GRH.

## Admissibility and replay

Knots are $64z_j$ with $X=0$ before $-10$, and the last slab extends from $16$ to infinity. Every atom and probability is rational with denominator $10^8$. Form $A=\mathbb EX$, $B=\mathbb E(4X^3-3X)$ and $U=\mathbb E\sqrt{(1+X)/2}$. The checker verifies the atom and probability constraints, then encloses the angular mean surplus above $8/9$ at $1.8159544451897402\ldots\cdot10^{-7}$. It verifies $\|G_A\|_\infty<.618660<C_1/(2\cos(\pi/12))$ and $\|G_B\|_\infty<1.195160<C_1$, where $C_1=\cosh(c)/3$. The cap checks use Taylor bisection on $[0,64]$ (641 and 83 boxes), reflection and jump-sum tails. Thus the entire first-translate and order-two-through-ten conditions at $t$ are unchanged, as are all first translates at $3t$.

From the repository root (SageMath 10.9, assertions on):

```sh
sage .godel/bob/check-midgap-sector.py
MIDGAP_BASELINE=1 sage .godel/bob/check-midgap-sector.py
```

The first run checks admissibility and the directional certificate in 128-bit ball arithmetic. Table SHA-256: `6841c5d6a8accd5a05bde88ef0fab89c6d17949e688a8252bdc8d669d02443c9`. The second run rigorously prices three earlier hard-pair-law failures; the weights are $(a,1-a)$ and the shifts $(s,s+d)$:

| $s$ | $d$ | $a$ | Hard-pair normalized slack strictly below |
|---:|---:|---:|---:|
| $-13/20$ | $1$ | $37/100$ | $-.00109$ |
| $-15/16$ | $7/5$ | $41/100$ | $-.00759$ |
| $-8/5$ | $2$ | $33/100$ | $-.00039$ |

These failures are for one prime law, not separation over the admissible class. All three directions are covered by the new law.

## Uniform coefficient certificate

With $m=-G_B/C_1$, let $d\nu=(1-|m|^2)d\mu$ and $S(t)=\Re\int e^{itx}m^2\,d\mu$, in the sign convention of the existing checker. Remove the common coefficient sign and put $\eta=|a-b|$. The exact capacity is

$$C(d,\eta)=\int\sqrt{\cos^2(dx/2)+\eta^2\sin^2(dx/2)}\,d\nu.$$

The worst absolute center over both coefficient orientations equals $(|S(s)+S(s+d)|+\eta|S(s)-S(s+d)|)/2$, by $\max(|p+q|,|p-q|)=|p|+|q|$. Concavity of the square root and positivity of $\nu$ give a capacity lower bound by the chord in **squared** imbalance between each pair of adjacent nodes $0,1/8,1/4,1/2,3/4,1$. For positive nodes use the normalized binomial price at $q=(1-\eta)/(1+\eta)$ truncated at degree 128; at zero use 96 cosine harmonics. Each truncation has integrated error below $10^{-12}$ uniformly in the claimed gap interval. For the balanced tail, with $D$ the maximum knot difference and $L=\sum_j|\beta_j|$ as in the existing jump kernel, for $u>D$ use $|E(u)|\le L^2(2+u+D)e^{-(u-D)/2}$. On $d\ge1$ its omitted-term envelope is bounded by its value at $u=k$, and the envelope ratio is at most $e^{-1/3}$ from $k=97$ onward.

At a rectangle corner, on each imbalance segment the chord minus the worst price is a quadratic in $\eta$. The checker uses outward capacity and center endpoints and minimizes this quadratic exactly over the segment, including any interior critical point. To pass from corners to the rectangle, keep $\eta$, the orientation and the center sign fixed. The approximate capacity chord is a convex combination of two smooth truncated capacities with weights independent of $s,d$. Put $T=\int x^2|m|^2d\mu$. A bound in $s$ for the second derivative of the signed gap is $T$. A bound in $d$ is $T$ plus the maximum over nodes of the sum of absolute cosine coefficients times $k^2(T+e^{-k/2}/4)$; the checker uses the looser $k^2(T+1/4)$ for nonzero imbalance nodes. Successive interpolation in the two coordinates costs $M_s h_s^2/8+M_d h_d^2/8$, and the exact capacity loses at most another $10^{-12}$ to truncation. This argument works for every fixed branch before taking the infimum, so no smoothness of the worst-price absolute value or the minimized slack is assumed. The 453 accepted rectangles on $[-5,-9/50]\times[1,2]$ give a minimum lower enclosure above $3.51\cdot10^{-5}$.

For $s\le-5$ both center arguments are at most $-3$. To the left of $-32$, $S(t)$ is a constant times $e^{t/2}$ since every sum-kernel argument is nonpositive there. On $[-32,-3]$ bound $|S|$ by $1/8$-mesh endpoint values plus $T/512$. This gives a price upper bound $.105281$. The balanced capacity bounds all capacities below, and its $1/32$ mesh on $[1,2]$, minus the curvature and truncation allowances, bounds it below by $.376442$. Thus the normalized gap in the remaining left tail exceeds $.27$.

## Discovery record

The starting probe used exact jump-kernel formulas evaluated in floating point, a 96-harmonic FFT capacity price, and meshes $.0125$ in $s$, $.025$ in $d$, $.01$ in $\eta$. It identified the hard-pair law's trough near the middle witness above. A first, broader conic fit had negative sampled margin and does not provide a separation certificate. The successful fit instead optimized this negative-earlier-shift sector, scanning both coefficient orientations and both center signs, using a Clarabel exchange variant of [`search-two-term-law.py`](search-two-term-law.py). The initial $(s,d,b/a)$ tests were $(-.9375,1.4,59/41),(-.72,1.1,1.6),(-1.48,1.875,1.94),(-.35,1,1),(-1.95,2,1.8)$, positive center branch. Scans used $s$ spacing $.025$, $d$ spacing $.05$, and smaller-to-larger weight ratios $0,.05,\ldots,1$. Each round added up to four near-worst tests separated by at least $.30$ in the sum of differences of their oriented parameters, and exchanged violated hull facets and cap frequencies. The objective was margin per $|a|+|b|$, not per mask integral. Input used the single-shift knots extended to $-10$, with $1/64$ refinement on $[-.75,.5)$ and $1/32$ on $[.5,3)$; solver settings included `--refine --left 10 --atoms 96 --steps 13 --mean 8e-8 --fpad 1.6e-6 --seconds 16`, Clarabel 0.11.1, SciPy 1.18.1, four solver threads, `faer`, and Gram eigenvalue cutoff $2\cdot10^{-9}$. The first reconstructed table (round 6, zero indexed) was retained despite `MaxTime`: primal and dual residuals were approximately $1.93\cdot10^{-9}$ and $2.45\cdot10^{-6}$ and the normalized objective about $.011804$. These are discovery diagnostics only. An independent numerical evaluator gave a sampled sector minimum about $.011725$ on the rounded table, before the uniform exact checker replaced the sampled estimate.

**Next decision.** Combine this half-strip with certified complementary sign and shift regions. For a fixed pair, if different admissible prime laws supply ranges containing zero in different separating directions, take the convex hull of their compact joint images: mixing the paired prime and shallow laws with the same weights preserves the linear constraints and the strict mean, so exclusion of every separating direction suffices for simultaneous matching for that pair. No single common mixture for all pairs follows.
