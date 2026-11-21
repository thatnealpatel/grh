# Reverse lift of the compressed rational theta operator

**Status:** Project calculation at radius $B=1$, degree $s=0$, and
$0<\alpha<1/2$. The criterion below is exact in this model, but its
arithmetic input has not been discharged unconditionally. Not Lean-checked.

## Source interface and statement

This tests the [closed graph proposal](trace-level-transport-q.md#next-fixed-cutoff-test-lift-the-compressed-global-operator)
on an actual **projected** output in the rational unramified real-band
model. In the digest-matched `pdftotext -layout` reading, (11.2.1.6–8),
pp. 488–489, distinguishes the local and global polynomial-weight level
closures and specifies the orthogonal global projection. Theorem 11.2.1.4,
(11.2.1.9–10), takes the level limit at a fixed position cutoff. It gives
no inverse transport bound. The positive-width norm here comes instead
from (10.1.1.3–5), p. 434, and we set its log-polynomial degree to zero.
The injection and nuclear reverse factor in Lemma C.3.2.2,
(C.3.2.5), pp. 695–696, are hypotheses. Its use on p. 515 is on a
**local** polar-free space, not on this global Hilbert level. The claim
on p. 520 that Theorem 12.4.1.1 evaluates the global $S$-piece with two
Mellin subtractions is not a proof of the factorization tested here.
These source readings are provisional, not visual verification.

Use $H=L^2(e^{2\alpha|x|}dx)$, the local and global closures $L_1,G_1$,
and the closed theta graph $T_1:X_1\to G_1$ from the preceding handoff.
Let $Q_1$ be the ambient orthogonal projection onto $G_1$. For
$A_f h=f*h$, $f=\beta'$ with $0\ne\beta\ge0$ in
$C_c^\infty((0,\log 2))$, set $C_{\rho,1}=Q_1M_\rho A_f|_{G_1}$.
The cutoffs in the assertion are fixed smooth compact position cutoffs,
with no prescribed relation to the band radius. Set

$$c=1/2-\alpha,\qquad \sigma=1-c,\qquad
 J_\alpha=\int_{\mathbb R}\frac{dt}{(1+t^2)|\zeta(\sigma+it)|^2}.$$

* If $J_\alpha<\infty$, every such $C_{\rho,1}$ has a nuclear reverse
  lift into $X_1$. The positive-log, mass-zero restriction keeps the test
  in the above-one control, but is not needed for the lift estimate
  apart from the use of positive support.
* If $J_\alpha=\infty$, some such $\beta$, nonnegative cutoff $\rho$,
  and actual generator $h=V_b$ give a projected output with **no** graph
  preimage. One may place the cutoff in $x>\sup\operatorname{supp} f$.
  This does not assert failure for every choice of cutoff and test.

The exact single-output criterion appears below. In particular, the
positive assertion for *all* these cutoffs and *all* widths would imply
RH, even before any trace evaluation: A zero on any line $\Re z=\sigma$
forces $J_\alpha=\infty$, and the functional equation reflects the strip.
Conversely, RH implies finiteness for each fixed $\alpha$, for example by
[Bui–Florea, first theorem in §1, first case](https://arxiv.org/abs/2302.07226) with
$k=1$, summed over dyadic ordinate intervals. That theorem invokes RH;
it is not an input available to this mission. Excluding boundary-zero
widths removes only the finite-ordinate singularities, not the tail
condition. The remaining estimate at such a width is precisely
$\sum_{n\ge0}2^{-2n}\int_{2^n}^{2^{n+1}}|\zeta(\sigma+it)|^{-2}dt<\infty$.
No unconditional decision of $J_\alpha$ at a specified width is asserted.

## Log coordinates for both graph legs

Write $D=\widehat b|_{(0,1)}$ for the positive ray of the **additive**
Fourier transform of an even band generator, extended by zero on $t>1$.
The band and zero-mode hypotheses are $D(0)=0$ and $\int D=0$. Define
$d(x)=e^{-cx}D(e^{-x})$ and $F(z)=\mathcal Ld(z)$, where
$\mathcal Ld(z)=\int_0^\infty e^{-(z-c)x}d(x)dx$. Use the ordinary
negative-sign log Fourier convention in this chart, with no $2\pi$ in
the exponent. By the [Poisson edge](trace-level-transport-q.md#the-poisson-edge-separates-the-cutoff-traces),
$V_b$ is causal (zero for $x<0$). Let $v_+=e^{\alpha x}V_b$. Then
$\mathcal L v_+=\zeta F$ in the Hardy space $H^2$ on $\Re z>c$:
The dual sum of (2.2.3.2), p. 82, gives
$e^{x/2}V_b(x)=\sum_n D(ne^{-x})$ with $n\ge1$. On $\Re z>1$
its Mellin transform is the absolutely unfolded Dirichlet series
$\zeta(z)\int_0^1D(t)t^{z-1}dt$. Both sides continue to $\Re z>c$,
with the pole canceled by $F(1)=0$. Paley–Wiener for the half-line
identifies the causal $L^2(dx)$ norm with the Hardy boundary norm.

The local norm of $U_b$ is equivalent to $\|d\|_{H^\alpha(\mathbb R)}$,
with the latter space the ordinary fractional Sobolev space in **log
position**, not in the original multiplicative coordinate. Indeed the
local norm squared is $\int_0^\infty |b(t)|^2\max(t^{2\alpha},t^{-2\alpha})dt$.
By Fourier Plancherel this is equivalent to the additive $H^\alpha$ norm
of the even extension of $D$: For the extra term at $0<t<1$, use
$\|b\|_\infty\le C\|D\|_2$ by the fixed band and $2\alpha<1$.
The same-positive-ray part of the Gagliardo seminorm of $D$, up to a
factor of two, becomes

$$\int_0^\infty \frac{e^{-h}}{(1-e^{-h})^{1+2\alpha}}
                  \|d-e^{ch}d(\cdot+h)\|_2^2\,dh.$$

This follows by putting $t=e^{-x}$ and the second variable $e^{-x-h}$;
$2c=1-2\alpha$ cancels the common scale. Cross-sign terms of the even
extension are at most the same-sign terms since $t+s\ge |t-s|$ on the
positive ray. On $1<h<2$, the reverse triangle inequality bounds the
integral below by a positive constant times $\|d\|_2^2$. Replacing
$e^{ch}$ in the difference by one costs at most a constant times
$\|d\|_2^2$ in the corresponding norm estimate: The squared error has
an integrable $O(h^{1-2\alpha})$ kernel near zero and
$O(e^{-(1-2c)h})$ at infinity. The remaining small-$h$ kernel is
comparable to the log Gagliardo kernel, and the large-$h$ part of the
log seminorm is bounded by $\|d\|_2^2$. Finally
$\|D\|_2^2=\int_0^\infty e^{-2\alpha x}|d(x)|^2dx$. Together these
give the two-sided norm equivalence.

**Graph domain, not just a boundary multiplier.** In these coordinates
the graph is exactly the set of causal $d\in H^\alpha(\mathbb R)$ with
$F(1)=0$ and $\zeta F\in H^2$. Necessity follows by continuity of
interior Hardy evaluations on both legs and the norm equivalence.
For sufficiency, convolve $d$ and the causal inverse Laplace transform of
$\zeta F$ by the same smooth causal approximate identity supported in
$(\epsilon,2\epsilon)$. The resulting pairs converge in the two leg
norms and still satisfy the transform identity and the moment condition.
The first leg is now smooth in every $H^m$ and vanishes near $0$.
Truncate it far to the right in $H^1$, then correct $F(1)$ by a fixed
compact smooth causal bump with nonzero $F(1)$; the correction tends to
zero in $H^1$. This gives convergence also in the output norm, by
$|\zeta(c+it)|\le C_c(1+|t|)$, from elementary summation by parts.
The compact smooth log inputs with corrected moment correspond to
$D\in C_c^\infty((0,1))$ of integral zero; their even additive inverse
Fourier transforms are admissible generators. Diagonal approximation
therefore gives a limit of paired fixed-band generators, not just a
formal division by $\zeta$.

## Project before dividing

Put $R(z)=(z-1)/(z+1)$ and $W(z)=R(z)\zeta(z)/(z+1)^2$. This is bounded
analytic on $\Re z>c$ by summation by parts with the pole removed
(and the absolutely convergent Dirichlet series at $\Re z\ge2$).
Factor $W=IO$ into its inner and outer factors. In the exponential
chart, $G_1$ identifies with $I H^2$. For containment, on a generator
$(z+1)^2F/R\in H^2$: The factor $(z-1)/(z+1-2c)$ is the simple
half-plane Blaschke factor at $1$, $F(1)=0$, and log derivatives of the
core profile give $(z+1)^2F\in H^2$. The quotient of $R$ by that
Blaschke factor has bounded inverse. For density, $W\mathcal L\varphi$
for any $\varphi\in C_c^\infty((0,\infty))$ comes from the graph: Its
preimage transform is $R\mathcal L\varphi/(z+1)^2$, giving causal
$H^\alpha$ boundary data and vanishing at $1$. The closure of these
outputs is $I H^2$ by the cyclicity of the outer factor.

Write $S$ for the full-line log Fourier multiplier by $I(c+it)$ in
unweighted $L^2(dx)$. It is unitary and causal, meaning that it preserves
support in any right half-line. Identify $G_1$ with its image under the
isometry $h\mapsto e^{\alpha x}h$ on $x\ge0$. For an actual input
$h\in G_1$, let $\psi=e^{\alpha x}\rho A_f h$, extended by zero for
$x<0$. It is compact smooth and vanishes near zero by the positive
support of $f$ and the Poisson edge. The global projected output has
transform $I\mathcal Lk$, where

$$ k=\mathbf 1_{[0,\infty)} S^*\psi.$$

The restriction here is crucial: $S^*$ need not be causal. It preserves
support in left half-lines by duality, commutes with differentiation, and
is an isometry on ordinary $H^m$. Thus if $\psi$ is supported in
$[0,M]$, $k$ is supported in $[0,M]$ and smooth **up to** $0$ from the
right, but may have a jump there when extended by zero.

**Single-output criterion.** The projected output belongs to $T_1(X_1)$
if and only if

$$ \int_{\mathbb R} \frac{|\widehat k(t)|^2}{|\zeta(\sigma+it)|^2}\,dt<\infty. $$

In fact its only possible preimage transform is
$F=R\mathcal Lk/((z+1)^2O)$. This is analytic of Smirnov class (division
by a bounded outer factor), with $F(1)=0$. On the boundary the necessary
$H^\alpha$ condition for $d$ is square integrability of
$(1+t^2)^{\alpha/2}\widehat k(t)/\zeta(c+it)$. By the zeta functional
equation and Stirling on the fixed line, the gamma factor between the
two zeta lines has modulus comparable to $(1+t^2)^{\alpha/2}$, including
bounded ordinates; use conjugation to reflect the ordinate. This gives
the displayed criterion. For sufficiency, $(z+1)^\alpha F$ is also Smirnov: $(z+1)^{-\alpha}$
is bounded outer on the half-plane. The displayed criterion gives
$L^2$ boundary values for this weighted quotient, so the Smirnov boundary
theorem gives $(z+1)^\alpha F\in H^2$. In particular $F\in H^2$ and its
causal inverse $d$ is in $H^\alpha$. Now the graph-domain argument applies. This
proves band and paired closure membership, which the earlier finite
Möbius inverse test alone could not infer.

If $J_\alpha<\infty$, integration by parts and the trace at $0$ give
$|\widehat k(t)|\le C_M(1+t^2)^{-1/2}\|\psi\|_{H^1}$, also for
$\psi\in H^1$ supported in $[0,M]$. By the criterion and both leg bounds,
this gives a bounded lift from such $\psi$ to $X_1$. The map
$h\mapsto\psi$ is nuclear into that compact-support $H^1$ space: Smooth
convolution and the fixed cutoff give a bounded $H^3$ map on a circle
containing the position support in its interior; inclusion into $H^1$
is nuclear by the summable Fourier singular values. Multiply by a
second smooth cutoff equal to one on the support and extend by zero
into the interval space (use the gap at zero from $f$). Composing with
the bounded graph lift gives the stated nuclear reverse factor. No
bounds uniform in a moving cutoff are given.

## Detect divergence on actual projected outputs

Let $K$ be the distributional impulse response of $S$. It is supported
in $[0,\infty)$. If the divergence of $J_\alpha$ is at infinity, it
suffices to arrange $k(0+)=(S^*\psi)(0)\ne0$, since
$\widehat k(t)=k(0+)/(it)+O(|t|^{-2})$ for smooth compact $\psi$.
The functional at $0$ pairs $\psi$ with the conjugate of $K$. It is
nonzero on some interval in $x>0$: Otherwise $K$ is supported at $0$,
so its bounded multiplier is a polynomial and hence constant. But $I$
has an interior zero, by the classical existence of a critical-line
zeta zero and the outerness of $O$.

If $\zeta(\sigma+it_0)=0$ for some finite $t_0$, it suffices to arrange
$\widehat k(t_0)\ne0$. As a functional of $\psi$ supported in $(0,M)$,
this is pairing against $q=S(\mathbf 1_{[0,M]}e^{it_0 x})$ on $(0,M)$.
By causality these functions agree on overlaps and give a causal
$L^2_{\rm loc}$ function on the full line. In distributions,
$(\partial_x-it_0)q=K$ (the derivative at the upper cutoff cannot affect
any earlier position). Hence $q$ cannot vanish identically on $x>0$.
In both cases the nonzero functional is thus available locally in the
open positive half-line, not just at the edge.

To realize either functional by the required input, take a point $x_0>0$
in its support. Pick $0<z_0<\min(x_0,\log 2)$ and a generator with
$V_b'(x_0-z_0)\ne0$. Such a generator exists by the checked first-pair
formula: In $(0,\log 2)$ vary $D$ near the sample $e^{-x}$ and restore
the zero integral by a disjoint bump, then translate the resulting
profile to the right by dilating the generator, staying in the band.
Take $\beta\ge0$ in a sufficiently small interval about $z_0$.
$A_{\beta'}V_b=\beta*V_b'$ is nonvanishing near $x_0$, and the interval
can be chosen with $x_0>\sup\operatorname{supp}\beta$. Multiplication
by $e^{\alpha x}A_{\beta'}V_b$ is invertible on the local smooth test
space there. Nonnegative smooth cutoffs span that test space over
$\mathbb C$, so some such $\rho$ supported in this overlapping window
gives a nonzero pairing. Scaling $\rho$ to have sup norm one does not
change the obstruction. This constructs an actual projected output,
not an arbitrary test vector in $G_1^\perp$ or an unprojected cutoff.

## Consequence for the frontier

This calculation relies on the pure exponential weight at $B=1$:
Restriction to the supported half-line turns the global norm into a
Hardy norm. It does not identify the global space for $s>0$ or for the
literal polynomial-weight levels of (11.2.1.8), and does not compute
any diagonal or Mellin subtraction. For a future Lean port,
`leandoc` finds `MeasureTheory.Lp.norm_fourier_eq` and
`riemannZeta_one_sub` in the pinned Mathlib, but not a half-plane
Smirnov or inner–outer factorization interface; no formal proof is
claimed. The classical Hardy, fractional norm, and gamma estimates
above are part of the project argument, not results imported from the
manuscript's trace transfer.

**Independent review:** Yah reviewed the two-sided criterion, paired core
approximation, outer division, nuclearity in graph norm, and actual-output
witnesses against base `012ee7ac7e0da0a19ec9f5b2363c33d2f2e6d4fc`
(`reverse-review`, agent `lkRAiCF`). In particular the review requires
applying Smirnov to the Sobolev-weighted quotient and distinguishes failure
for some cutoffs from failure for a prescribed one. It also independently
compared the operator and topology with (11.2.1.6–8) and C.3.2.2 in
extracted text. This is mathematical and text review, not Lean checking.

**Runnable successor avoiding inverse transport:** In this same
fixed-cutoff model work directly with the model-space projection
$P_{K_I}=P_+-SP_+S^*$, where $P_+$ is causal support restriction. The
causal identity contribution has trace zero: The fixed compact cutoff
bounds output position above, and every application of the convolution
moves support right by at least $\inf\operatorname{supp} f>0$. This
trace-class operator is nilpotent. The global trace can therefore be
computed with $-P_{K_I}$ instead, without division by $\zeta$. Start
with a single Blaschke factor on the half-plane, compute its actual
rank-one Haar diagonal at a fixed $\rho$, and compare the resulting
Mellin test value and sign with p. 520. Separately justify each extension
from this control to the full projection and to the prescribed cutoff
order before using it as a source comparison. The $+1/2$ subtraction,
orbital contribution, and end-to-end Lean GRH proof remain open.
