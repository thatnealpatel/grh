---
evidence_revision: 61af82a6f5935dbfe5d699c03bcbd3e804b71c1d
outcome: established
---

# Polynomial-grid signs of the mod-four prime ramp

Let $\chi_4$ be the primitive real character modulo $4$ and
let $P(X)=\sum_{p<X}\chi_4(p)\log p\,\log(X/p)$ for real
$X\ge1$, over genuine primes with natural logarithms.

**Proposition to test:** For every fixed integer $k\ge5$,
$\exists N\in\mathbb N\;\forall n\in\mathbb N,\ n\ge N:
P(n^k)\le0$ if and only if every nontrivial zero of
$L(s,\chi_4)$ has real part $1/2$. Each individual $k$ has
its own premise; no simultaneous signs, rate, or between-
sample signs are assumed.

**Source and payoff:** This operator conjecture extends the
[fourth-power criterion](../closed/mod-four-prime-ramp-fourth-power-sign.md)
at the evidence revision, using the identical ramp from
Bob's [equation (1)](../../bob/fixed-strip-endpoints.md#the-product-mean-at-the-original-endpoint-weight)
at `bbca37033019090f6f40e6223b5054d382c9d789` with
$(d_i,d_j)=(1,-4)$ and $v=0$. The [all-cutoff criterion](../closed/mod-four-prime-ramp-eventual-sign.md)
landed at `dca062832345d6f827769b6a1af9b923d21e3b0e`.
Neither source claims this extension. It would test whether
a sharper slope bound and iteration can replace the one-shot
cell bound without any new assumptions on the samples.

**Discriminating test:** Start from the trivial bound or
nonvanishing in $\Re s>a$, allowing boundary zeros. Prove or
obstruct an unsmoothed prime-log bound with an arbitrarily
small exponent loss using a finite Perron contour or a
truncated explicit formula. Check sharp endpoints, prime
powers, and constant dependence. Anchor at the left sample
and integrate the slope against the actual log gap. Test
whether the nonnegative envelope-minus-ramp tail gives a
strictly better zero-free half-plane by Landau, verifying
real-axis regularity and noncancellation. Track losses and
constants over finitely many steps, including the final
threshold $1/2$. For the converse, verify that the all-cutoff
result applies without a normalization or cutoff change.

## Adjudication

**The equivalence holds for each fixed $k$.** Write $d=1/k$ and $L=L(s,\chi_4)$. The fourth-power card's chord estimate counts the integers in a cell and multiplies by the log gap. At $n^k$ this gives $O_k(X^{1-2d}\log(2X))$, not a square-root bound for $k>4$. Instead we use the current zero-free half-plane to bound the *signed* slope, and spend the log gap on improving that half-plane. Each round uses the original signs on the same grid.

### Sharp slope under an open zero-free half-plane

Suppose $1/2\le a\le1$ and $L$ is nonvanishing in $\Re s>a$. Fix $a<\sigma<2$. Then $|L'/L(u+iv)|\ll_{a,\sigma}\log(2+|v|)$ uniformly for $\sigma\le u\le2$. Indeed, the disk centered at $2+iv$ of radius $R=2-(a+\sigma)/2$ is zero-free, and the Euler product gives a bounded choice of $\log L$ at its center. Bounded character partial sums and partial summation give $|L(s)|\ll |s|/\Re s$ on the disk. Thus $\Re\log L\ll_{a,\sigma}\log(2+|v|)$ there. Apply Borel–Carathéodory on the concentric disk of radius $(R+2-\sigma)/2$, then Cauchy's derivative estimate through radius $2-\sigma$. No disk touches the old boundary.

For real $x\ge2$ put $y=\lfloor x\rfloor+1/2$ and $T=y^2$. Integrate $-(L'/L)(s)y^s/s$ on the segment $2-iT$ to $2+iT$, with factor $1/(2\pi i)$. Expand the absolutely convergent series there. For each integer $m$, the full vertical Perron kernel at $y/m$ gives $\mathbf1_{m<y}$ by Fourier inversion of $e^{-2v}\mathbf1_{v>0}$ at $v=\log(y/m)\ne0$. Integrating each omitted oscillatory tail by parts bounds the individual kernel error by $O((y/m)^2/(T|\log(y/m)|))$. Outside $[y/2,2y]$ the weighted errors sum to $O(y^2/T)$ by $\sum_m\Lambda(m)m^{-2}<\infty$. Inside, $|\log(y/m)|\ge|y-m|/(2y)$, $\Lambda(m)\le\log(2y)$, and the half-integer distances have reciprocal sum $O(\log(2y))$. These errors total $O(y\log^2(2y)/T)$. This recovers the sum through $x$, including an integer prime power at equality.

Shift the finite segment to $\Re s=\sigma$. No poles are crossed. The two horizontal edges cost $O_{a,\sigma}(y^2\log(2T)/T)$ and the vertical costs $O_{a,\sigma}(y^\sigma\log^2(2T))$ by the log derivative estimate. With this $T$, the result is $\sum_{m\le x}\Lambda(m)\chi_4(m)\ll_{a,\sigma}x^\sigma\log^2(2x)$. The terms $m=p^j$, $j\ge2$, cost at most $O(\sqrt x\log^2(2x))$ absolutely by counting at most $\sqrt x$ bases per exponent and $O(\log(2x))$ exponents. Thus the same bound holds for $|\theta_\chi(x)|$, where $\theta_\chi(x)=\sum_{p\le x}\chi_4(p)\log p$. This is a sharp cutoff argument, neither differentiation of Bob's smoothed estimate nor an explicit formula requiring selected heights.

### Spend the log gap and repeat

Assume the proposed sampled signs; enlarge $N$ to at least two. In a round with $a\ge1/2+d/2$, take $\sigma=a+d/2$ and $b=\sigma-d=a-d/2$. For $A=n^k\le X\le(n+1)^k$ with $n\ge N$, the exact hinge integral and the left sample give

$$P(X)=P(A)+\int_A^X\theta_\chi(t)\,dt/t\le C X^b\log^2(2X)=:E(X).$$

Indeed $\log(X/A)\le k/n\le 2k X^{-d}$, and a prime at a hinge has zero ramp weight at equality. There is no sign assumption on the integral. Constants may depend on $a$ and $k$. We spend only $d/2$ moving the contour off the old boundary; we keep both logarithms rather than spending a further exponent loss.

Set $X_0=N^k$. For $\Re s>1$ the Mellin transform on $[X_0,\infty)$ of the nonnegative function $E-P$ is

$$ CX_0^{-z}\left(\frac{\ell^2}{z}+\frac{2\ell}{z^2}+\frac{2}{z^3}\right)
+\frac{(L'/L)(s)+H(s)}{s^2}+\int_1^{X_0}P(X)X^{-s-1}\,dX,\qquad z=s-b,\quad\ell=\log(2X_0). $$

The first term comes from integrating $(\ell+v)^2e^{-zv}$ for $v=\log(X/X_0)\ge0$. Each prime hinge transforms to $p^{-s}/s^2$; the Euler product then gives the displayed plus sign with $H(s)=\sum_p\sum_{j\ge2}\chi_4(p)^j(\log p)p^{-js}$. The bound $\sum_{j\ge2}p^{-ju}=p^{-2u}/(1-p^{-u})$ gives normal convergence for $\Re s\ge u>1/2$. The compact integral is entire. Thus the expression is meromorphic on $\Re s>b\ge1/2$ and analytic at every real point there since $L(u)\ge1-3^{-u}>0$ by alternation.

Landau now gives convergence throughout $\Re s>b$: If the tail had abscissa $\alpha>b$, the continuation would be regular at $\alpha$. Center its Taylor series at a real $r>\alpha$ close enough to reach a point left of $\alpha$. In powers of $r-s$ its coefficients are the nonnegative logarithmic moments of the defining tail at $r$ divided by factorials, by uniqueness of continuation and differentiation inside convergence. Monotone convergence would give a finite integral at that left point, a contradiction. The transform is therefore holomorphic in the improved half-plane, whereas a zero $\rho$ there would leave the uncanceled residue $\operatorname{ord}_\rho(L)/\rho^2$. This proves nonvanishing strictly right of $b$, without estimating $L'/L$ at $a$ or assuming anything about $H$ at $1/2$.

Start from $a_0=1$ by the Euler product. The recurrence $a_{i+1}=a_i-d/2$ gives $a_i=1-i/(2k)$ through $i=k$. The last shift uses $a_{k-1}=1/2+d/2$, contour $1/2+d$, and output $1/2$. The envelope pole stays on the output boundary. No limiting choice of epsilon, uniformity in $k$, or exclusion of zeros on the input boundary is needed. The functional equation reflects any nontrivial zero left of the line to the excluded half-plane.

Conversely, the [all-cutoff proof](mod-four-prime-ramp-eventual-sign.md#from-zeros-to-sign), lines 59–80 at the pin above, has the same weights and strict cutoff. On the zero-line hypothesis its prime-power ramp has absolute zero contribution at most $C_0\sqrt X$, $C_0=\sum_\rho |\rho|^{-2}<4/3$. Removing the odd prime squares subtracts $2\int_1^{\sqrt X}\vartheta_{\rm odd}(t)\,dt/t=(2+o(1))\sqrt X$, with higher powers and remaining contour terms $o(\sqrt X)$. Thus $P(X)<0$ for every sufficiently large real $X$, including on this grid. Neither the eventual signs nor zero location have been proved unconditionally. Bob uses magnitude in (1), not this equivalence.
