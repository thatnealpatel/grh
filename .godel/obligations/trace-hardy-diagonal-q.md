# Direct diagonal of the rational unit-band Hardy model

**Scope:** $F=\mathbb Q$, trivial compact isotype, band $B=1$, Sobolev degree zero,
and $0<\alpha<1/2$. This computes the positive-log **position** cutoff of the
Hardy compression from the [reverse-lift control](trace-reverse-lift-q.md),
without dividing by zeta. It does not compute the manuscript's global $S$
piece. Lean checks the single-vector sharp overlap. The operator calculation
and its cutoff limit below are independently reviewed mathematics, not Lean
results.

## Operator and source match

Write $c=1/2-\alpha$. In the causal log coordinate of the reverse-lift model,
the isometry $h(x)\mapsto e^{\alpha x}h(x)$ gives $H_+=L^2(0,\infty)$
and the Hardy theta subspace $I H_+$, where $I$ is the inner factor of
$W(z)=((z-1)/(z+1))\zeta(z)/(z+1)^2$ in $\Re z>c$. Here multiplication
by $I$ is understood on the Laplace side. Write $Q$ for the orthogonal
projection in $H_+$ onto $I H_+$, and $P_K=1-Q$. For a smooth $f$ compactly
supported in $(0,\log 2)$ (in particular for the mass-zero subfamily), set
$g(y)=e^{\alpha y}f(y)$ and let $C_g$ denote causal convolution. The
operator whose trace is calculated is $M_\rho C_g Q$ on $H_+$, equivalently
the compressed cutoff operator $Q M_\rho C_g|_{I H_+}$. None of these
formulas changes the designated order of cutoff, convolution, and projection.

**Provisional source comparison from the digest-matched layout extraction:**
Definition 10.1.1.1(1), (10.1.1.3), p. 433, takes the global theta closure
in the full weighted space. Definition 10.4.1.3, p. 457, uses the order
$M_\rho P_a^{\mathrm{geom}}A(\phi)$ for geometrically truncated convolution;
the kernel discussion at (10.4.3.48)–(10.4.3.50), pp. 473–474, also treats
$M_\rho A(\phi)P_a^{\mathrm{geom}}$. The two orders should not be identified
at finite cutoff by cycling bounded factors through an unproved trace.
Theorem 11.2.1.4(2), (11.2.1.8)–(11.2.1.10), p. 489, concerns the
**global** Paley–Wiener level limit with position cutoff fixed, for tests
above norm one. Definition 10.4.3.7 assumes $s\ge3$, unlike this model.
Theorem 12.5.1.1, pp. 519–520, uses the positive Mellin exponent $z-1/2$
and zeros **interior to a strip**. Its proof invokes Theorem 12.4.1.1,
pp. 514–519, to identify the global $S$ piece after two Mellin subtractions.
The local formula (12.4.1.25)–(12.4.1.28) instead yields local integrals and
the norm-one logarithmic term. Neither that local formula nor the global
level limit gives a model-space overlap formula or identifies the global
$S$ piece with the compression here. The calculation below is a project
control for the latter compression, not a replacement for that identification.

## One zero and the fixed-cutoff diagonal

For bounded compactly supported $\rho$, choose $R$ with its half-line
support in $[0,R]$. Causality lets us restrict the input of $M_\rho C_g$ to
$[0,R]$. With $\widehat g(t)=\int e^{-ity}g(y)\,dy$, Fourier inversion
expresses the operator as the trace-norm integral of rank-one operators
$$
\frac1{2\pi}\int \widehat g(t)
  \big[h\mapsto\langle h,\mathbf1_{(0,R)}e^{it\cdot}\rangle\rho e^{it\cdot}\big]dt,
$$
where the inner product is linear in the first variable. Each trace norm
before the scalar coefficient is $\sqrt R\,\|\rho\|_2$ and
$\widehat g\in L^1$. Taking traces gives $g(0)\int\rho=0$. This holds
also with $m\rho$ in place of $\rho$ for every bounded multiplier $m$.
Consequently the trace density of $M_\rho C_g Q$ is the negative of the
trace density of $M_\rho C_g P_K$. Here the density is the $L^1$ function
representing $m\mapsto\operatorname{Tr}(M_m T)$ for a trace-class $T$:
Sum the diagonal products of a trace-norm summable rank-one expansion;
Cauchy–Schwarz gives $\|\mathrm{density}(T)\|_1\le\|T\|_1$.

For a single factor at $z_j$, put $a=z_j-c$ and $r=\Re a>0$. The model
space is spanned by the unit vector $u_a(x)=\sqrt{2r}e^{-\bar a x}$ on
$x\ge0$, extended by zero. Thus the negative rank-one diagonal is
$$
  -\rho(x)\,2r\,e^{-2rx}\int_0^x g(y)e^{\bar a y}\,dy,\qquad x\ge0.
$$
The checked proposition `Masullo.halfLineMellinVector_sharpCutoff_overlap`
in `Props.HalfLineMellinDiagonal` supplies the scalar step: For $y\ge0$,
$$
\int_{[0,R]}u_a(x-y)\overline{u_a(x)}\,dx
=\begin{cases}e^{-ay}(1-e^{-2r(R-y)})&y\le R,\\0&y>R.\end{cases}
$$
The proof restricts to the common causal support $[y,R]$, translates its
lower edge to zero, and integrates the decaying exponential. Setting $y=0$
and letting $R$ increase gives the normalization. Removing the sharp cutoff
on one vector gives the shifted overlap $e^{-ay}$; integrating against $g$
gives $\int f(y)e^{(1/2-z_j)y}\,dy$. The overlap has the reflected exponent;
the separate global minus sign comes from taking the orthogonal complement.

## Blaschke exhaustion and then position exhaustion

The inner factor is a pure Blaschke product at the zeros with $\Re z_j>c$,
with multiplicity. Indeed, on each compact zero-free boundary arc $W$
extends across the boundary with modulus bounded below in a small closed
neighborhood. The outer factor and Blaschke factor are bounded, so the
negative log modulus of the singular inner factor is bounded there.
Its Poisson measure on the open arc must then be absolutely continuous,
hence zero. The remaining finite-boundary support is discrete; a mass at
a boundary zero would force exponential decay in the reciprocal normal
distance, inconsistent with the finite order of that zero. A singular
factor at infinity would give exponential decay on the real ray, whereas
$W(x)\sim x^{-2}$. This excludes the singular part.

The finite initial products in Blaschke product order give increasing model
spaces whose projections tend strongly to $P_K$. For instance their
orthogonal complements intersect in $I H_+$: Divide a function in the
intersection by each finite inner product, take a weak limit of these
quotients of equal norm, and use boundedness of point evaluations and
locally uniform product convergence. For fixed $\rho$, trace-class
composition then converges in trace norm by finite-rank approximation;
the diagonals converge in $L^1$. This statement does not assert that the
series of rank-one densities is absolutely summable in $L^1$.

For position exhaustion, use the orthonormal basis $\phi_j=I_{<j}u_{a_j}$
(on the Laplace side), obtained by the orthogonal decomposition for a product
of inner factors. The full-line Fourier modulus of the causal zero extension
is $\sqrt{2r_j}/\sqrt{r_j^2+(t-\gamma_j)^2}$, where
$\gamma_j=\Im z_j$ and $0<r_j=\Re(z_j-c)\le1-c$. For $T=|\gamma_j|\ge2$,
consider $\langle M_\rho C_g\phi_j,\phi_j\rangle$. The part of
$\widehat{C_g\phi_j}$ with $|t|>T/4$ has $L^2$ norm $O_g(T^{-2})$ by
rapid decay of $\widehat g$; the part with $|t|\le T/4$ has $L^1$ and
$L^2$ norms $O_g(T^{-1})$ by the Lorentzian bound. Split the second vector
at $|s|=T/2$, on the full line. The low-band $L^2$ norm is $O(T^{-1/2})$,
so its contribution is $O_g(\|\rho\|_\infty T^{-3/2})$. For the high band
move $\rho$ to the second slot as $\bar\rho$. Its Fourier convolution on
the output low band is bounded pointwise by $O(\operatorname{Var}(\rho)
T^{-1/2})$: Use $|t-s|\ge|s|/2$, the Fourier bound
$|\widehat{\bar\rho}(t-s)|\le\operatorname{Var}(\rho)/|t-s|$, and
Cauchy–Schwarz against the $L^2$ norm of $\widehat\phi_j$. Variation here
is of the zero extension, including the possible jump at zero. The product
formula follows by Schwartz approximation of the high-band vector in $L^2$:
The physical products converge in $L^1$, and the Fourier convolutions
converge uniformly, both by Cauchy–Schwarz. Pairing with the low-band $L^1$
norm now gives the same $T^{-3/2}$ bound times variation. The constants
are uniform in the inner factors and in $r_j$ down to zero.

The zero count $O(T\log(2+T))$ makes that majorant summable by dyadic
blocks. With uniformly bounded compact cutoffs of uniformly bounded
variation that tend to one almost everywhere, the limit can therefore be
taken term by term in the trace. Uncut causal convolution commutes with the
preceding inner-factor isometry, so the $j$-th limiting term is exactly the
one-vector pairing computed above. Hence
$$
\lim_{\rho\to1}\operatorname{Tr}(M_\rho C_g Q)
=-\sum_{\Re z_j>1/2-\alpha}\int_0^\infty f(y)e^{(1/2-z_j)y}\,dy.
$$
This includes sharp $[0,R]$ cutoffs. It is a scalar limit, not an uncut
operator trace or trace-norm convergence. Definition 9.3.3.1, p. 427,
does not impose a uniform variation bound over its prescribed profiles.
Nevertheless, the same Fourier rank-one integral gives a small-transition
comparison in this model. If $d$ is supported in $[b,b+\ell]$ on the half
line, $|d|\le1$, and $\operatorname{supp}g\subset[0,D]$, restrict the input
in that integral to $[b-D,b+\ell]\cap[0,\infty)$. This replaces the uniform
rank-one norm by at most $\sqrt{(D+\ell)\ell}$. For the p. 427 profiles at
large $\Lambda$, the half-line difference from $\mathbf1_{[0,\log\Lambda]}$
is supported in $[\log(\Lambda-\varepsilon),\log\Lambda]$, of length tending
to zero by $\varepsilon<1/\Lambda$. Its trace contribution thus tends to
zero regardless of oscillation in that interval. This is a deduction from
the trace-norm integral, not an additional Lean result. This position result
still does not implement (11.2.1.8)–(11.2.1.10). The half-plane sum includes
zeros at or beyond $1/2+\alpha$; reflection identifies the exponent with
the manuscript's only on reflection-invariant zero families such as the
open strip, not on the full half-plane. No cancellation of those extra
terms or of the two Mellin corrections is proved here.

**Review evidence:** `hardy-review` (`szKmRqB`) checked the fixed-cutoff
model, singular factor exclusion, and source comparison from layout text.
`hardy-limit-review` (`MeeZPoo`) checked trace-class Fourier inversion,
the full-line frequency estimates, and the exact scalar endpoint. Neither
review establishes a manuscript level comparison; no visual check is
claimed.

**Runnable successor:** In Lean, integrate the checked shifted overlap
against a smooth compact positive-log $g$ and explicitly prove the fixed
sharp-cutoff double-integral identity by Fubini on $[0,R]^2$ (the causal
triangle is measurable and the integrand is bounded there). Then take
$R\to\infty$ on the compact $y$ support. This proves the convolution
pairing with the full reflected Mellin test value, still for one factor.
Separately, a manuscript-facing bridge must compare the actual global
level operators of (11.2.1.8)–(11.2.1.10) with an independently evaluated
localized diagonal in the **same weighted degree and cutoff order**.
In particular, it must account for the extra half-plane zeros and both
Mellin subtractions before the model result can be used in (12.5.1.4).
