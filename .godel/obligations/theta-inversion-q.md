# Rational theta inversion at the unramified tensor

**Status:** The [finite support theorem](../../Proofs/Theorems/RationalThetaUnramified.lean)
now identifies the explicit nonzero rational sum for the unramified
input on the real section with the integer lattice, with absolute
summability. The [norm-fiber theorem](../../Proofs/Theorems/RationalThetaNormFiber.lean)
extends this to an arbitrary rational idele, with the idelic norm as
scale. The [real-lattice inversion module](../../Proofs/Theorems/RationalThetaInversion.lean)
proves continuity, inversion, and uniform two-tail estimates. The
[weighted integrability module](../../Proofs/Theorems/RationalThetaIntegrability.lean)
proves finiteness of the compact-strip squared-norm integral in log
coordinates. The [Mellin unfolding theorem](../../Proofs/Theorems/RationalThetaMellin.lean)
proves absolute convergence and the zeta factorization in $\Re z>1$. The
[entireness theorem](../../Proofs/Theorems/RationalThetaMellinEntire.lean)
proves complex differentiability with both zero modes removed. The local
two-ray factor is holomorphic on $\Re z>0$ without moment conditions.
The [continuation theorem](../../Proofs/Theorems/RationalThetaMellinContinuation.lean)
now identifies the two-moment theta transform with the zeta product on
$\Re z>0$ off $1$, computes the removable value at $1$, and gives
vanishing at every zeta zero in the open critical strip. The
[finite-unit representative theorem](../../Proofs/Theorems/RationalIdeleNormalization.lean)
now gives the algebraic normalization needed to leave the real section.
The [log-norm section and splitting](../../Proofs/Theorems/RationalIdeleLogSection.lean)
construct the canonical continuous section and separate log norm from
the norm-one class as a topological product. Neither this product nor
the pointwise sum reduction identifies the quotient Haar measure.
Independent Yah statement reviews used text extracted from the
digest-matched [pinned edition](../sources/masullo/README.md). The readings
are provisional, not visual. Finite Fourier self-duality and measure
comparison are not formalized.

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
The reduction of the sum now applies to arbitrary representatives. The
identification of the tensor Fourier transform remains open. This model
gives no theorem for other finite inputs or number fields.

## Checked finite support on the real section

`Masullo.rationalTheta_eq_unramified_sum` specializes (2.2.3.1),
pp. 81–82, at $s_{\mathbb Q}(t)=(t,1,\ldots)$ from (A.2.2.4), p. 546.
For $t>0$ and complex Schwartz $b$, the summand at $q\in\mathbb Q^\times$
is $b(tq)$ if the image of $q$ lies in every finite completion-integer
ring, and zero otherwise. Lean proves absolute summability and identifies
the sum with `rationalTheta b t`. This evaluates the characteristic
function on diagonal inputs without constructing a global
Schwartz–Bruhat space.

At each finite place the completion valuation agrees with the field
valuation on the image of $q$. Mathlib's
`HeightOneSpectrum.mem_integers_of_valuation_le_one` puts a rational
number integral at all finite places in the image of $\mathcal O_{\mathbb Q}$;
`Rat.ringOfIntegersEquiv` identifies that image with $\mathbb Z$.
Conversely, each integer lies in every completion-integer ring. Thus
nonzero integer indices inject into the nonzero rational indices with
the same summands, and all terms outside the range vanish. Existing
Schwartz lattice summability transfers along this inclusion. This is
not a claim that every integer gives a nonzero term or that the
surviving indices are required to be local units. Independent Yah
statement review checked the finite factors, both signs, and the
exclusion of zero against the digest-matched text of (2.2.3.1),
(A.2.2.1)–(A.2.2.4), and the context on pp. 77–78. No visual reading
or adelic Haar equality is claimed.

## Checked finite-unit normalization of rational ideles

`Masullo.exists_rational_principal_mul_finite_valued_eq_one` proves:
For each $a\in\mathbb A_{\mathbb Q}^{\times}$ there is an
$r\in\mathbb Q^{\times}$ such that every finite coordinate of
$\operatorname{diag}(r)a$ has valuation one. By Mathlib's
`HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one`,
this is exactly membership in the local integral units for those
coordinates, not equality of the coordinates to one.

The proof uses `Rat.ringOfIntegersEquiv` to choose a generator $p_v$
of each height-one prime. Its value is $\exp(-1)$ at $v$ and $1$
at the other places, since distinct nonzero prime ideals are maximal.
`AdeleRing.isUnit_iff` restricts the primes where
$a_v$ has value different from one to a finite set. If $a_v$ has value
$\exp(k_v)$, use the factor $p_v^{k_v}$ in $r$ to cancel it. These
exponents can be negative. The proof works directly in Mathlib's idele
group and uses neither the manuscript's splitting nor a global Fourier
transform.

Independent Yah review of the SHA-256-matched extraction checked that
this is the existence part of the finite factor in (A.2.2.1), p. 546,
used in (A.2.2.2)–(A.2.2.4). It does not prove the topological
isomorphism, uniqueness, or a continuous choice of representatives.

## Checked norm-fiber reduction

`Masullo.rationalTheta_eq_unramified_idele_sum` proves absolute
summability and identifies (2.2.3.1), pp. 81–82, for the unramified
tensor, evaluated at **any** rational idele $a$, with
$\theta_b(\operatorname{ideleNorm}(a))$. The summand for
$q\in\mathbb Q^\times$ samples the real coordinate of
$\operatorname{diag}(q)a$ if every finite coordinate of that product
is integral, and is zero otherwise.

The proof rescales $a$ by one principal rational $r$, using
`Masullo.exists_rational_principal_mul_norm_section`. The product
formula preserves the norm, the finite valuations of the new
representative equal one, and the real coordinate is the positive
idelic norm after changing the sign of $r$ if necessary. This changes
the summation indices by the bijection $q\mapsto qr$. In the new
representative, the local integrality tests agree with those on the
section because the finite factors are units, not because they are
literally one. The checked positive-section theorem supplies
summability and the sum equality. No parity or moment assumptions
are needed, and no equality of idele classes in one fiber is asserted.

Independent Yah review checked the proposed statement against
(2.2.2.4), p. 78, (2.2.3.1), pp. 81–82, and
(A.2.2.1)–(A.2.2.4), p. 546, in digest-matched text extraction.
This is a specialized pointwise evaluation of the manuscript's series,
not a construction of the global Schwartz–Bruhat tensor space or the
manuscript's general compact-uniform convergence theorem.

## Checked continuous log-norm section and class splitting

In [RationalIdeleLogSection.lean](../../Proofs/Theorems/RationalIdeleLogSection.lean),
`Masullo.rationalIdeleLogSection` is the continuous homomorphism
$x\mapsto(e^x,1,\ldots)$ into rational ideles. Its domain
`Multiplicative ℝ` is the *additive* real line in multiplicative notation.
`Masullo.rationalIdeleReal_logSection`, `Masullo.rationalIdeleLogSection_finite`,
and `Masullo.ideleNorm_logSection` give the two coordinate formulas and
the norm $e^x$. This models Lemma A.2.2.1, (A.2.2.4), p. 546, after the
exp/log coordinate change. In contrast to principal normalization of an
arbitrary idele, the section has finite coordinates literally one.
Continuity is for the idele topology on units: Both the adele value and
its inverse are continuous, with real coordinates $e^x$ and $e^{-x}$.

The section on classes is right inverse to the descended log norm.
`Masullo.rationalIdeleClassLogSplit` gives a continuous multiplicative
equivalence $\mathbb R\times C_{\mathbb Q}^1\simeq C_{\mathbb Q}$,
with forward map $(x,k)\mapsto[s_{\mathbb Q}(e^x)]k$ and inverse first
coordinate $\log|g|_{\mathbb Q}$. The inverse removes the section from
$g$ to give the norm-one component. The class product is a project
corollary: (A.2.2.12), p. 547, states the analogous splitting on ideles,
and p. 546 explicitly notes passage of a section to classes. The proof
uses the norm-one subgroup directly and does not identify it with the
product of finite units as in (A.2.2.3). Independent Yah review checked
these distinctions against the digest-matched layout extraction, not
rendered pages.

## Checked compactness of the rational norm-one classes

[The compactness theorem](../../Proofs/Theorems/RationalIdeleClassCompact.lean),
`Masullo.compactSpace_rationalIdeleClassNormOne`, proves the compactness
part of Theorem A.1.4.3(1), pp. 542–543, for $F=\mathbb Q$. It uses
the finite units in (A.2.2.3), p. 546, without claiming that the two
factors in that equation have been identified as topological groups.

The [supporting map](../../Proofs/Lemmas/RationalFiniteUnits.lean),
`Masullo.rationalFiniteUnitClass`, inserts a family of local integral
units with infinite coordinate one and takes its class. Checked
principal normalization makes that map surjective: On a norm-one
class it gives real coordinate exactly one and finite valuations one,
not finite coordinates one. Continuity in the idele units topology is
checked on both values and inverses by inclusion of the all-integral
stage into the cofinite restricted product. Mathlib's `padicIntEquiv`
and compactness of units of a compact Hausdorff topological ring give
compactness of the domain, a product of compact spaces. Independent
Yah review checked the endpoint and this argument against the
digest-matched layout extraction, not rendered pages. Compactness by
continuous image does not prove that the quotient is Hausdorff.

## Independent next Haar step: Show the rational principal subgroup is closed

Formalize the discreteness argument of Lemma A.1.3.4(1)–(2), p. 542,
for $\mathbb Q$. Take the identity neighborhood with positive real
coordinate and both the finite value and its inverse in the
all-integral stage. `RestrictedProduct.isOpen_forall_mem` gives the
finite open condition since each completion's valuation ring is open.
On a principal idele, the two finite conditions force all valuations
to be one. Its idelic norm is one by the product formula, so the checked
`ideleNorm_eq_abs_rationalIdeleReal` makes its real absolute value one.
Positivity and the injective rational embedding into the real field
then force the principal idele to be one. Use
`discreteTopology_iff_isOpen_singleton_one`,
`Subgroup.isClosed_of_discreteTopology`, and the quotient topology's
separation instance from a closed normal subgroup. Local compactness
of the class group can then use the checked log-section splitting with
the compact norm-one factor. The strict boundary-jet test below is
independent of this step.

The later measure target is the pushforward of the manuscript's quotient
Haar measure by log norm, namely $dx$. Definition A.3.2.1, pp. 559–560,
specifies quotient Haar with counting measure on $\mathbb Q^\times$ and
$dt/t$ on the norm quotient; (A.3.2.1) gives mass one for the norm-one
factor over $\mathbb Q$. A.3.3.1, p. 561, describes the product upstairs
and the measure of a strip over a norm-one fundamental domain. The
checked topological splitting makes log norm the first projection but
does not construct the quotient measure or identify its normalization.

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

## Checked continuation of the zeta factorization

`Masullo.rationalTheta_mellin_eq_zeta_mul_of_pos` proves
$T_b(z)=\zeta(z)M_b(z)$ for $\Re z>0$, $z\ne1$, with both zero modes
$b(0)=\widehat b(0)=0$. Here $T_b$ is the theta Mellin integral and
$M_b(z)=\int_{\mathbb R}(b(e^x)+b(-e^x))e^{zx}\,dx$. The identity
continues the absolutely unfolded formula, not the unfolding argument:
If the two-ray profile is not identically zero, the sum of integrated
norms of the paired samples diverges for $0<\Re z\le1$.

At $1$, substituting $t=e^x$ on both rays gives
$M_b(1)=\int_{\mathbb R}b(t)\,dt=\widehat b(0)$. The quotient
$M_b(z)/(z-1)$ tends to $M_b'(1)$, and `riemannZeta_residue_one`
gives limit one for $(z-1)\zeta(z)$. The proof fills the product at
$1$ with $M_b'(1)$, applies the removable singularity theorem, and uses
the identity theorem on the entire convex right half-plane from agreement
near $2$. `Masullo.rationalTheta_mellin_one` gives the separate equality

$$
T_b(1)=M_b'(1)=\int_{\mathbb R}x(b(e^x)+b(-e^x))e^x\,dx.
$$

In particular, the value is not obtained by multiplying by the totalized
`riemannZeta 1`. `Masullo.rationalTheta_mellin_eq_zero_of_zeta_zero`
then proves point vanishing at every zero with $0<\Re z<1$.

The source invokes the identity theorem immediately after (3.2.2.11),
p. 127, to identify the global idelic transform with the analytically
continued zeta integral. The Lean theorem applies that mechanism to a
rational lattice model; it does not assert a new adelic identification.
The explicit derivative value at $1$ and the zeta-zero corollary are
project consequences, not literal statements of Theorem 3.2.2.1.
Independent Yah review checked the domains, both rays, the pole
cancellation, and the interpretation of pp. 124–127 against the
digest-matched layout extraction, not rendered pages.

## Checked vanishing through the zeta order

In [RationalThetaMellinOrder.lean](../../Proofs/Theorems/RationalThetaMellinOrder.lean),
`Masullo.analyticOrderAt_rationalTheta_mellin_ge_zeta` proves that
$\operatorname{ord}_\rho T_b\ge\operatorname{ord}_\rho\zeta$ for
$0<\Re\rho<1$ with both zero modes of $b$ zero. In a neighborhood of
$\rho$ the checked continuation is the product of the holomorphic germs
$\zeta$ and $M_b$. Mathlib adds their analytic orders in
$\mathbb N\cup\{\infty\}$, so the lower bound also handles an identically
zero theta transform. There is no exact-order conclusion, since $M_b$
can contribute additional vanishing.
`Masullo.iteratedDeriv_rationalTheta_mellin_eq_zero` extracts
$T_b^{(m)}(\rho)=0$ for each natural $m<\operatorname{ord}_\rho\zeta$.

This is a project consequence of the continuation mechanism after
(3.2.2.11), p. 127. In the digest-matched layout extraction, the
consuming interface is (10.2.2.4) and (10.2.2.6), p. 446: Interior
jets retain all orders below the multiplicity. The theta image is
already twisted by $|\cdot|^a$ before taking the closure in
(10.1.1.3), p. 434. Neither the integral formula for these weighted
pairings nor their continuity on the Hilbert space is supplied by
these Lean declarations. The cited Theorem 9.3.2.6, p. 426, concerns
projections onto common kernels, not this local order inequality;
its [reversed nesting](trace-spectral-strip-q.md#source-interface-a-missing-totality-step)
remains a separate source issue. Independent Yah review checked the two
statements, the multiplicity convention, and the single twist against
the digest-matched extraction, not the rendered pages.

## Checked log-moment integrals and twisted jet vanishing

In [RationalThetaMellinLogMoments.lean](../../Proofs/Theorems/RationalThetaMellinLogMoments.lean),
`Masullo.iteratedDeriv_rationalTheta_mellin_eq_logMoment` proves, for each
$m\in\mathbb N$, both zero modes of $b$ zero, and every $z\in\mathbb C$,
absolute integrability and the identity

$$
T_b^{(m)}(z)=\int_{\mathbb R} x^m \theta_b(e^x)e^{zx}\,dx.
$$

The supporting declaration `Masullo.hasDerivAt_rationalTheta_mellin_logMoment`
uses the uniform two-tail bound with $N\ge |\Re z|+4$ and absorbs the
polynomial cost by $|x|^m\le m!e^{|x|}$. It differentiates the moment to
the next one by local domination. The original first-derivative theorem
now uses the same argument at orders zero and one. The derivative formula
agrees with the log factor and positive exponent in (9.2.1.25), p. 409.
That formula concerns a specified one-sided Sobolev domain, whereas this
all-parameter result uses the two-moment theta input and its two tails.

`Masullo.rationalTheta_twisted_logMoment_eq_zero` gives, for
$0<\Re\rho<1$ and $m<\operatorname{ord}_\rho\zeta$, absolute
integrability of the displayed product and

$$
\int_{\mathbb R} \big(e^{ax}\theta_b(e^x)\big)
  \big(x^m e^{(\rho-a)x}\big)\,dx=0\qquad(a\in\mathbb R).
$$

This matches the rational log-line input pairing for (10.2.2.3)–(10.2.2.4),
pp. 445–446, in the digest-matched layout extraction: The pairing is
bilinear, and for $\rho=a+\beta+it$ its kernel is $x^m e^{(\beta+it)x}$.
Equation (10.1.1.3), p. 434, already puts the factor $e^{ax}$ on the
input. In the positive-sign Fourier coordinate $w$ with $\rho=1/2+iw$,
$w$-derivatives would carry the additional factor $i^m$; the checked
identity differentiates in the Mellin parameter, not in $w$. These are
project results on the unramified rational input, not a proof of
Theorem 10.2.2.1 or an identification of adelic Haar measure.
Independent Yah review checked the hypotheses, the exponent sign, the
absence of conjugation, and the single twist against the digest-matched
extraction, not rendered pages.

## Checked interior jet continuity and annihilation of the theta closure

For $s\ge0$ and $|\Re z|<\alpha$, `Masullo.interiorLogJet` is a
complex continuous linear functional in the log-Lebesgue $L^2$
coordinate $U=Wu$, with

$$
W(x)=e^{\alpha|x|}(1+x^2)^{s/4}.
$$

This is the square root of the symmetric strip weight in (9.2.2.4),
p. 412. The representing vector is the $L^2$ class of the **conjugate**
of $k=x^m e^{zx}/W(x)$, so `Masullo.interiorLogJet_toLp` gives the
absolutely convergent bilinear integral $\int u(x)x^m e^{zx}\,dx$
for every $u$ with $Wu\in L^2$. The strict distance to the strip
boundary gives $r=(\alpha-|\Re z|)/2>0$; the factorial estimate
bounds $|k|$ by $(m!/r^m)e^{-r|x|}$. Conjugating the representing
vector changes neither the bound nor the exponent in the integral.
This implements the reciprocal-weight Cauchy–Schwarz estimate of
(9.2.1.33)–(9.2.1.34), pp. 409–410, not the same-weight wording of
(9.2.1.32).

In [RationalThetaJetClosure.lean](../../Proofs/Theorems/RationalThetaJetClosure.lean),
`Masullo.rationalThetaWeightedLog_closure_subset_ker` now puts the
closure of the two-moment rational lattice inputs twisted by $e^{ax}$
in the kernel of each jet for $z=\rho-a$, $0<\Re\rho<1$,
$|\Re(\rho-a)|<\alpha$, and $m<\operatorname{ord}_\rho\zeta$.
Membership in the weighted space uses the checked two-tail squared
norm estimate with the shifted endpoint powers. Vanishing on the
inputs is the log-moment theorem, and continuity gives vanishing on
the closure. This is the rational log-line annihilator inclusion in
(10.2.2.3)–(10.2.2.6), pp. 445–446, after the single twist from
(10.1.1.3), p. 434. It uses neither the cited finite-projector
convergence nor the converse inclusion. The existing
[totality audit](trace-spectral-strip-q.md#source-interface-a-missing-totality-step)
explains the reversed nesting in Theorem 9.3.2.6, p. 426. There is no
adelic Haar identification in this theorem.

## Next runnable analytic step: Check the strict boundary threshold

Keep the same log-Lebesgue coordinate and allow $|\Re z|=\alpha$,
including $\alpha=0$. The square of the divided kernel has no
exponential decay on at least one half-line. There it is
$|x|^{2m}(1+x^2)^{-s/2}$, comparable on $|x|>1$ to
$|x|^{2m-s}$ by $x^2\le 1+x^2\le2x^2$. On the other half-line
its square is bounded above by the same polynomial expression, and
it is continuous on compact intervals. Formalize the resulting
$L^2$ criterion **$2m+1<s$** for $s\ge0$, and then reuse the
bilinear integral and closed-kernel proof for the allowed orders.
`integrableOn_Ioi_rpow_iff` gives both directions of the power test
on $(1,\infty)$ in pinned Mathlib; reflection treats the negative
half-line. The same criterion should give failure of bounded
extension for the excluded jets by testing on truncations of the
conjugate divided kernel in the $L^2$ coordinate.

In the digest-matched layout extraction, (10.2.2.5), p. 446, uses
$\lfloor(s-1)/2\rfloor+1$ as the boundary cap before taking the
minimum with multiplicity. For the analogous singleton cap
(10.3.1.4), p. 448, the text explicitly defines the bracket by
$N\le x$, not $N<x$. At $s=2m+1$ the literal bound would include
order $m$ if the multiplicity exceeds $m$, but the endpoint power is
$x^{-1}$ and the dual norm diverges. In particular, $s=1$ fails for
a boundary point evaluation. This reading is provisional and the
strict criterion is a log-line repair, not an assertion about the
rendered glyphs or a failure at the separate $s=2$ cap.
