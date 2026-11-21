# Rational theta inversion at the unramified tensor

**Status:** The [real-lattice inversion module](../../Proofs/Theorems/RationalThetaInversion.lean)
proves continuity, inversion, and uniform two-tail estimates. The
[weighted integrability module](../../Proofs/Theorems/RationalThetaIntegrability.lean)
proves finiteness of the compact-strip squared-norm integral in log
coordinates. The [Mellin unfolding theorem](../../Proofs/Theorems/RationalThetaMellin.lean)
proves absolute convergence and the zeta factorization in $\Re z>1$. The
[entireness theorem](../../Proofs/Theorems/RationalThetaMellinEntire.lean)
proves complex differentiability with both zero modes removed. The local
two-ray factor is holomorphic on $\Re z>0$ without moment conditions.
Independent Yah statement reviews used text extracted from the
digest-matched [pinned edition](../sources/masullo/README.md). The readings
are provisional, not visual. The adelic reduction itself is not formalized.

## Manuscript statement and rational reduction

Definition 2.2.3.1, (2.2.3.1), pp. 81–82, omits zero from the global
adelic theta sum. Theorem 2.2.3.2, (2.2.3.2)–(2.2.3.3), p. 82,
relates the theta function at an idele class to the Fourier-side theta
function at its inverse, with two zero-mode corrections. Remark 2.2.3.3
sets the additive quotient volume to one. Example A.3.1.5, p. 557, uses
Lebesgue measure and the real Fourier kernel $e^{-2\pi ixy}$; Examples
A.3.1.6–8, pp. 557–558, give self-duality of $\mathbf1_{\mathbb Z_p}$
with unit additive volume and the rational global normalization.

Take $F=\mathbb Q$, the tensor $b\otimes\prod_p\mathbf1_{\mathbb Z_p}$
for $b\in\mathcal S(\mathbb R,\mathbb C)$, and the real section
$(t,1,1,\ldots)$ of norm $t>0$. The finite support condition reduces the
nonzero rational indices to nonzero integers. The finite Fourier
factors are unchanged, so the Fourier-side sum has the same reduction
at $t^{-1}$. With
$\theta_b(t)=\sum_{n\in\mathbb Z\setminus\{0\}}b(tn)$, the resulting
real-lattice statement is

$$
\theta_b(t)=t^{-1}\theta_{\widehat b}(t^{-1})
           +t^{-1}\widehat b(0)-b(0).
$$

Retain both zero modes for arbitrary complex Schwartz $b$. Neither
evenness nor a Gaussian hypothesis is needed. The two-moment case
$b(0)=\widehat b(0)=0$ is a corollary, not the inversion statement.
The identification of the finite factors, tensor Fourier transform,
and norm section above explains why the checked real statement models
this passage. It gives no theorem for other finite inputs or number
fields.

## Checked real-lattice inversion

The [scaled Poisson lemmas](../../Proofs/Lemmas/ScaledPoisson.lean)
specialize `SchwartzMap.tsum_eq_tsum_fourier` at zero to $x\mapsto b(tx)$.
The Fourier dilation uses the Lebesgue change of variables and $t>0$, so
the transform is $t^{-1}\widehat b(t^{-1}u)$. Schwartz decay at exponent
$-2$ and `Int.tendsto_coe_cofinite` give absolute summability of the
integer samples. The theorem applies `Summable.sum_add_tsum_compl`
with $\{0\}$ to each side before rearranging. This proof uses Mathlib's
real Poisson summation; the manuscript invokes adelic Poisson summation.

## Checked uniform two-tail estimates

Theorem 2.2.3.4(1)–(3), (2.2.3.4)–(2.2.3.7), pp. 82–83,
uses inversion to reduce the small-norm estimate to large-norm decay
on the Fourier side. Parts (4)–(5), pp. 83–85, make the estimates
uniform on bounded sets and bring both scale thresholds to one.

`Masullo.rationalTheta_uniform_tail_bounds` proves the real-lattice
counterpart: Given a bounded set $B$ in the complex Schwartz space and
$N\in\mathbb N$, one $C>0$ works for every $b\in B$:

- At $t\ge1$, $|\theta_b(t)|\le C/t^N$.
- At $0<t\le1$, $|\theta_b(t)-t^{-1}\widehat b(0)+b(0)|\le C t^N$.

At large scales the order-$(N+2,0)$ Schwartz seminorm bounds the
lattice samples by a constant times $t^{-N}|n|^{-2}$. Mathlib's
seminorm characterization of von Neumann boundedness makes this uniform
on $B$. Its continuous complex-linear Fourier map takes $B$ to a bounded
set. Apply the large-scale estimate there with exponent $N+1$ to absorb
the prefactor $t^{-1}$ in inversion. This yields bounds all the way to
$t=1$ without a separate middle-range argument in this lattice model.

`Masullo.rationalTheta_uniform_log_bound` then gives
$|\theta_b(e^x)|\le C e^{-N|x|}$ on $\mathbb R$ for members of $B$ whose
two zero modes vanish. Neither the corrected tail bounds nor inversion
assume those vanish. Independent statement review checked both signs,
the absorbed inverse scale, the uniform quantifiers, and the moment
hypotheses against the digest-matched extraction. The real lattice proof
does not handle arbitrary finite test factors, bounded adelic families,
or the archimedean fundamental-domain estimate used in the manuscript.

## Checked continuity and compact-strip integrability

Definition 2.2.3.1, pp. 81–82, uses continuity from Lemma 2.2.2.1(2),
p. 77. In the real-lattice model, `Masullo.rationalTheta_continuousOn`
proves continuity on positive scales for every complex Schwartz $b$.
On $t\ge c>0$, the Schwartz seminorm $p_{2,0}(b)$ gives the summable
majorant $p_{2,0}(b)c^{-2}|n|^{-2}$ on nonzero integers.
`continuousOn_tsum` proves continuity on $[c,\infty)$; taking $c<t$
then gives continuity locally at every positive $t$. Neither zero mode
needs to vanish for this step, and no continuity at $t=0$ is asserted.

In the provisional reading of (9.2.2.4), p. 412, the real compact-strip
norm uses $dt/t$, the maximum of the two endpoint powers, and polynomial
weight $(1+|\log t|^2)^{s/2}$ for $s\ge0$. The global norm (10.1.1.6),
p. 435, shifts both exponents by $2a$. For the rational radial model use
$x=\log t$ and Lebesgue measure $dx$, the log-coordinate form of $dt/t$.
The manuscript's compact-factor decomposition ((9.2.1.19), p. 408, and
Appendix A.3.3.1, p. 561) motivates this model; Lean does not identify the
compact factor, adelic tensor, or quotient measure.

`Masullo.integrable_rationalTheta_hardySobolev` proves integrability of

$$
  |\theta_b(e^x)|^2\max(e^{2(a+\alpha)x},e^{2(a+\beta)x})(1+x^2)^{s/2}
$$

when $b(0)=\widehat b(0)=0$, for any $a,\alpha,\beta\in\mathbb R$ and
$s\ge0$. The strip interpretation uses $\alpha\le\beta$, including a
singleton; the symmetric weight does not need that ordering. The proof
uses continuity for measurability and the two-tail estimate with
$N\ge \max(|a+\alpha|,|a+\beta|)+s/2+1$. The auxiliary bound
$(1+x^2)^{s/2}\le e^{s|x|}$ leaves an integrable majorant $C^2e^{-|x|}$.
Independent review confirmed both statements against the digest-matched
extraction, in particular the moment hypotheses and both endpoint
powers. This supplies finite weighted norms for the real profiles used
in the [rational orbital lifts](trace-orbital-q.md#genuine-global-theta-lifts).
It does not supply the theta-to-Hilbert map's continuity in the source
topology, the identification with the partitioned diagonal, or a trace
formula.

## Checked rational theta Mellin unfolding

Theorem 3.2.2.1(2)–(3), pp. 124–125, and (3.2.2.11), p. 127, unfold
the absolutely convergent theta integral in $\Re z>1$. In the rational
unramified model the integrand is constant on the norm-one fibers:
One can represent those classes with real component one and finite unit
components, which do not change the finite tensor factors. The norm-one
volume is one by (A.3.2.1), p. 560, and the real section has measure
$dt/t=dx$ for $t=e^x$. The archimedean factor integrates both signs,
using the local measure $dt/|t|$ from Definition A.3.2.2(1), p. 560.
No extra factor of two is inserted. The example on p. 127 uses a modified
$2$-adic input, unlike the unramified tensor here.

For any complex Schwartz $b$, put $B(x)=b(e^x)+b(-e^x)$ and
$F_z(x)=B(x)e^{zx}$. `Masullo.integrable_rationalMellinIntegrand` proves
$F_z\in L^1(dx)$ for $\Re z>0$: The order-zero Schwartz seminorm bounds
the negative tail, and an order $N>\Re z$ bounds the positive tail.
`Masullo.rationalTheta_mellin_eq_zeta_mul` proves both integrability of
the weighted theta profile and

$$
  \int_{\mathbb R}\theta_b(e^x)e^{zx}\,dx
   =\zeta(z)\int_{\mathbb R}F_z(x)\,dx,\qquad \Re z>1.
$$

This does not require evenness or either zero mode to vanish. The Lean
proof reindexes the already absolutely summable signed lattice samples
into pairs $k,-k$, with $k=n+1$. The $k$th weighted pair is
$k^{-z}F_z(x+\log k)$. Its integrated norm is exactly
$k^{-\Re z}\int|F_z|$ by translation invariance. The real $p$-series test
makes these norms summable, justifying Tonelli for the norm majorant and
termwise Bochner integration. The resulting positive-index series is
Mathlib's `zeta_eq_tsum_one_div_nat_add_one_cpow`. This proves the lattice
factorization, not an adelic quotient integral or locally uniform
convergence in the parameter. Independent Yah review checked the two
signs, both half-planes, and all measure factors against the digest-matched
extraction, not the rendered pages.

The wording of Theorem 3.2.2.1(2)(b), p. 125, provisionally refers to the
*unprojected* integral (3.2.2.3). Multiplying by a unitary angular
character does not affect its absolute integrability at a fixed real
part. Cancellation for a nontrivial compact isotype happens in the
compact average **before** the norm-section integral in (3). The
trivial-isotype calculation above does not depend on that wording.

## Checked holomorphy of the theta transform and real local factor

`Masullo.hasDerivAt_rationalTheta_mellin` proves integrability of the
weighted theta profile and its parameter derivative for all $z\in\mathbb C$
when $b(0)=\widehat b(0)=0$. It computes the derivative of the integral by
inserting the log-norm factor $x$ in the integrand. The corollary
`Masullo.differentiable_rationalTheta_mellin` states entireness. This most
directly models the trivial-character norm-section assertion of Theorem
3.2.2.1(3)(a), (3.2.2.4), p. 125, and models (2)(a), p. 124, after the
rational unramified reduction above. The extraction gives a proof by
uniform convergence of holomorphic truncations: See Remark 3.2.2.2,
p. 125, and (3.2.2.7)–(3.2.2.10), pp. 126–127. The Lean proof instead
differentiates directly and does not state uniform convergence of the
truncations.

`Masullo.hasDerivAt_rationalMellin` proves the analogous derivative and
its absolute integrability for the two-ray factor $M_b(z)$ at each
$\Re z>0$, with neither zero mode assumed. This is the real trivial-sign
case of the local convergence and holomorphy used in Theorem 3.3.1.1(1),
p. 129, and (3.3.1.7), p. 130, not a larger domain for the uncorrected
global theta integral. Order-zero and higher Schwartz seminorms control
the negative and positive log tails respectively. With $\sigma=\Re z>0$,
an order $n>2\sigma$ gives decay at least $e^{-\sigma|x|}$ at the center
parameter $z$ on the positive tail as well as on the negative tail.

Both proofs use the same local domination lemma. If the weighted
profile at $z$ is bounded by $C e^{-3r|x|}$, on $|w-z|<r$ the weight
changes by at most $e^{r|x|}$, and $|x|\le e^{r|x|}/r$ absorbs the
parameter derivative. The remaining majorant $(C/r)e^{-r|x|}$ is
integrable, so Mathlib's `hasDerivAt_integral_of_dominated_loc_of_deriv_le`
applies at the complex parameter $z$. The theta proof takes $r=1$ and
uses the two-tail estimate of order $N\ge |\Re z|+3$. Independent Yah
statement review checked both domains, both real rays, the two zero
modes, and the normalization against digest-matched text extraction,
not the rendered pages.

## Next runnable step: Continue the factorization into the open strip

For two-moment input, prove that the entire theta Mellin transform agrees
with $\zeta(z)M_b(z)$ on $\Re z>0$ away from $z=1$. It should then vanish
at every zeta zero in the open strip. The source uses an identity theorem
immediately after (3.2.2.11), p. 127. Do not try to extend the absolute
unfolding: If the two-ray profile is not identically zero, the sum of
integrated norms of the paired samples diverges for $0<\Re z\le1$.

A route that also handles the pole uses the whole connected right
half-plane. First show $M_b(1)=\int b=0$ by the two exponential
changes of variables and Fourier evaluation at zero. Let $G$ equal
$\zeta M_b$ off $1$ and $M_b'(1)$ at $1$. The derivative of $M_b$ at $1$
and `riemannZeta_residue_one` give continuity of $G$ at $1$ via
$(z-1)\zeta(z)\cdot(M_b(z)-M_b(1))/(z-1)$. Apply
`Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt`
at $1$, and `analyticOn_riemannZeta` with the local derivative elsewhere.
Use `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq` on the convex
right half-plane, with agreement near $2$ from the checked unfolding.
Evaluating the totalized `riemannZeta 1` in the unmodified product is not
the removable value. The continuation, adelic reduction, and trace's
Mellin subtractions are not supplied by the current holomorphy proofs.
