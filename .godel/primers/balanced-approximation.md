# Balanced approximation: Finite residual versus full-span obstruction

**Claim.** A finite Gram residual measures a chosen span on a chosen interval. A nonzero
continuous Mellin evaluation that kills *every* balanced column would obstruct the full
span in $L^2((0,1),dx)$. These are different tests.

**Small example on paper.** Set
$r_a(x)=\{a/x\}-a\{1/x\}=a\lfloor1/x\rfloor-\lfloor a/x\rfloor$, $0<a<1$. On the two
cells $(1/2,1)$ and $(1/3,1/2)$, of lengths $1/2$ and $1/6$, the column $r_{1/2}$ takes
the values $1/2$ and $0$. The squared residual on $(1/3,1)$ is
$$
\min_c\left(\tfrac12|1-c/2|^2+\tfrac16\right)=\tfrac16.
$$
The minimizer $c=2$ leaves an indicator residual on the omitted interval too, since
$r_{1/2}$ is $1/2$ or $0$ according to the parity of $\lfloor1/x\rfloor$. Thus
$1/6\le d_1^2\le1/2$ for the single-column distance on $(0,1)$. Adding $r_{1/3}$, with
values $1/3,2/3$ on the two cells, makes the visible residual zero:
$r_{1/2}+\tfrac32r_{1/3}=1$ there. In general, at cutoff $\delta$, form
$G=\sum_I |I|u_Iu_I^{\mathsf T}$ and $b=\sum_I|I|u_I$ from cell vectors $u_I$. If
$Gc=b$, the visible squared minimum is $L=1-\delta-b^{\mathsf T}c$. The same trial on
$(0,1)$ has squared error at most $L+\delta(1+\|c\|_1)^2$ because $|r_a|\le1$. This
controls missing integration, not missing generators. Only the upper bound transfers to
the full family.

**Checked foundation.** For $0<\Re s<1$, integration gives
$$
F_s(r_a)=(a-a^s)\zeta(s)/s,\qquad F_s(g)=\int_0^1 g(x)x^{s-1}\,dx.
$$
For $\sigma=\Re s>1/2$, $F_s$ is continuous on complex $L^2(0,1)$; its norm is
$(2\sigma-1)^{-1/2}$ by the squared kernel integral, and $F_s(1)=1/s$. A hypothetical
zero $\rho$ with $1/2<\Re\rho<1$ therefore kills the full closed complex span in this
norm, while it does not kill $1$. The distance from $1$ is at least
$\sqrt{2\Re\rho-1}/|\rho|$. At $\Re s=1/2$ the squared kernel integral diverges at zero;
cutting off at $e^{-T}$ only gives a norm of $\sqrt T$, not a bounded full-interval
witness.

**What it does not show.** No interior certificate is exhibited. A finite test to try on
paper is a winding calculation for $F_s(r_{1/2})$ on a rectangle strictly inside
$1/2<\Re s<1$. Truncate at $1/M$ for an integer $M\ge2$ to get
$$
P_M(s)=\frac1{2s}\sum_{1\le k<M,\ k\text{ odd}}(k^{-s}-(k+1)^{-s}).
$$
If $\alpha$ is the rectangle's minimum real part, the tail costs
$M^{-\alpha}/(2\alpha)$, and $|P'_M|\le1/(2\alpha^2)$ by integrating
$x^{\alpha-1}|\log x|/2$. For boundary mesh at most $h$ and vertex errors at most
$\eta$, require each computed polygon **segment** to stay farther from zero than
$\eta+h/(4\alpha^2)+M^{-\alpha}/(2\alpha)$. Then straight-line homotopy preserves the
winding. A nonzero winding certifies an interior zero of the common factor, since
$|2^{-s}|>1/2$ there. A certified zero winding only excludes zeros in that rectangle,
and a failed margin gives neither conclusion.

**Source.** [`BalancedFractMellin.lean`](../../Proofs/Lemmas/BalancedFractMellin.lean),
`Masullo.integral_balancedFract_mul_cpow`;
[`UnitIntervalMellinEval.lean`](../../Proofs/Lemmas/UnitIntervalMellinEval.lean),
`Masullo.exists_unitInterval_mellinEval`; and
[`BalancedFractApproximationObstruction.lean`](../../Proofs/Theorems/BalancedFractApproximationObstruction.lean),
`Masullo.sqrt_div_norm_le_infDist_balancedFractClosedSpan`. The finite Gram and contour
tests here are paper calculations.
