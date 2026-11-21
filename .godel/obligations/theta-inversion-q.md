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
the norm-one class as a topological product. The separate Haar branch
now identifies the [normalized quotient measure](#checked-product-of-local-haar-probabilities-on-the-rational-quotient)
and the [upstairs restricted product](#checked-global-restricted-product-characterization).
Independent Yah statement reviews used text extracted from the
digest-matched [pinned edition](../sources/masullo/README.md). The readings
are provisional, not visual. See the later sections for the checked
additive Fourier theory on the box span and its scope.

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

## Checked discreteness and quotient topology over the rationals

[RationalIdeleClassTopology.lean](../../Proofs/Theorems/RationalIdeleClassTopology.lean)
proves the rational case of Lemma A.1.3.4(1)–(2), p. 542. The principal
subgroup is discrete in the induced topology (`discreteTopology_rationalPrincipalIdeles`)
and closed (`isClosed_rationalPrincipalIdeles`). The actual idele class
quotient is Hausdorff (`t2Space_rationalIdeleClassGroup`) and locally
compact (`locallyCompactSpace_rationalIdeleClassGroup`). The latter uses
our checked split over the real log-norm line and compact norm-one
classes, not a claim about the order of the manuscript's argument.

The [finite-unit window](../../Proofs/Lemmas/RationalIdeleUnitWindow.lean)
has positive real coordinate and both the finite value and its inverse
in the all-integral stage. Its openness uses the two projections of the
units topology of Definition A.1.3.1, p. 541, and
`RestrictedProduct.isOpen_forall_mem`. The two finite conditions force
valuation one everywhere. On a principal idele the product formula
then gives real absolute value one, and positivity and injectivity of
the rational cast force the identity. The proof takes the preimage in
the principal subgroup, not in the abstract discrete source group.
Independent Yah statement review checked the source scope and the two
units-topology projections against the digest-matched layout extraction,
not rendered pages. This does not treat arbitrary number fields or
functoriality, or identify or normalize Haar measure.

## Checked positive-real finite-unit fundamental domain

[RationalIdeleFundamentalDomain.lean](../../Proofs/Theorems/RationalIdeleFundamentalDomain.lean)
constructs `Masullo.rationalIdeleUnitWindowHomeomorph`. Its forward map
is the actual idele-class quotient restricted to the open window of
positive real coordinate and integral units at all finite places. The
positive principal normalization gives surjectivity. The quotient of
any two representatives of the same class in this window is itself in
the window and principal, hence is the identity. The quotient map is
open, so the continuous bijection on the open window is a homeomorphism.
`Masullo.rationalIdeleUnitWindow_isFundamentalDomain` then supplies
Mathlib's `IsFundamentalDomain` for any measure on the Borel ideles,
with the opposite principal subgroup acting by right translation.
This is a pointwise orbit statement, not an assumption about null sets
or invariance of the measure. An independent Yah review checked the
transversal, the right-action convention, and the measure interface.

The digest-matched layout extraction of (A.2.2.3), p. 546, describes
$C_{\mathbb Q}$ by the positive real factor and finite integral units.
In (A.2.3.13)–(A.2.3.14), p. 549, the rational norm-one domain has
positive real coordinate (therefore one) and finite integral units:
The rational class number is one, and the unit lattice has rank zero.
Taking its positive radial extension gives our window. The reading is
extraction-based, not verified against rendered pages. The Lean
statements neither formalize the general number-field domain nor
identify a specific Haar measure.

## Checked log-norm Haar normalization on the rational quotient

Definition A.3.2.1 and (A.3.2.1), pp. 559–560, pair counting
measure on the principal ideles with the radial measure $dt/t$. The
norm-one mass in the displayed formula specializes to one over $\mathbb Q$:
$r_1=1$, $r_2=0$, $h=d=R=1$ (the rank-zero regulator is the empty
determinant), and $w=2$. A.3.3.1, p. 561, gives strip mass
$\log(T)\mu_1(C^1_F)$. These locators and normalizations are from
layout extraction of the digest-matched PDF, not a rendered-page check.

[RationalIdeleClassHaar.lean](../../Proofs/Theorems/RationalIdeleClassHaar.lean)
constructs Haar probability on the compact norm-one subgroup by
normalizing Mathlib's Haar measure on the whole group. It transports the
product with Lebesgue measure in log coordinates via the checked
`rationalIdeleClassLogSplit`. `isHaarMeasure_rationalIdeleClassHaar`
checks Haar invariance, finiteness on compact sets, and positivity on
nonempty open sets. `measurePreserving_rationalIdeleClass_logNorm`
identifies the log-norm pushforward with Lebesgue measure: In the split
coordinates the map is just the first projection, and the other factor
has mass one. `rationalIdeleClassHaar_normStrip` gives the mass of
$1\le |c|\le T$ for $1\le T$, including the degenerate strip. The
log-norm integrability equivalence and integral formula apply to complex
functions of log norm; no extra compact volume factor appears.

This constructs the normalization specified on the quotient. It does
not construct the upstairs restricted-product measure or prove that its
quotient measure is the one just constructed.

## Checked Haar comparison for a normalized upstairs window

In [RationalIdeleHaarComparison.lean](../../Proofs/Theorems/RationalIdeleHaarComparison.lean),
`Masullo.map_restrict_rationalIdeleUnitWindow_eq_rationalIdeleClassHaar`
proves $\pi_*(\nu|_W)=\mu$ for a Borel Haar measure $\nu$ upstairs
with $\nu(W\cap\{a:1\le |a|\le e\})=1$. Here $W$ is the checked
positive-real, finite-unit window, $\pi$ is the actual class quotient,
and $\mu$ is `rationalIdeleClassHaar`. The measure is restricted to the
whole window, not to the strip. The strip only fixes the scalar.

The inverse of the window homeomorphism followed by inclusion is an
open group embedding. The pushforward of the restricted measure is the
comap along this embedding, so it is Haar. On the quotient the strip
$[1,e]$ is compact by the log split and has mass one under $\mu$.
Haar uniqueness on sets with compact closure fixes the scalar there.
The log split also yields a countable compact cover, extending equality
to all Borel sets without a second-countability premise.

Independent Yah statement review checked Definition A.3.2.1,
(A.3.2.1)–(A.3.2.2) and (A.3.2.5), pp. 559–560, and A.3.3.1, p. 561,
against the SHA-256-matched layout extraction. The quoted formula in
A.3.3.1 places the strip on the upstairs radial extension of the
norm-one fundamental domain. The rational norm-one mass is one, and
the positive real density $dt/t$ gives strip mass one, with no factor
from the negative real coordinate. This reading is provisional, not a
rendered-page check. This comparison theorem assumes that strip mass
for $\nu$; the [constructed upstairs Haar](#checked-upstairs-haar-and-window-strip-mass)
now supplies it for a particular measure. Neither result identifies the
manuscript's restricted product.

## Checked finite-unit identification of the norm-one classes

In [RationalIdeleFiniteUnitFactor.lean](../../Proofs/Theorems/RationalIdeleFiniteUnitFactor.lean),
`Masullo.rationalFiniteUnitClassEquiv` identifies the product of the
local integral unit groups with the actual norm-one subgroup of the
rational idele class quotient, as topological groups. The apply lemma
specifies the map $u\mapsto [(1,u)]$. Multiplicativity is coordinatewise.
The representatives lie in the positive-real finite-unit window, whose
quotient map is injective. Equality of representatives gives equality
of the local units at each place. The existing continuous surjection is
therefore a homeomorphism by `Continuous.homeoOfEquivCompactToT2`.

Independent Yah statement review checked the full finite product,
the fixed real coordinate, and the actual quotient and subgroup
topologies against the SHA-256-matched layout extraction of
(A.2.2.1)–(A.2.2.4), p. 546. The positive real coordinate in the class
splitting equals the norm, so norm one means real coordinate $1$; there
is no remaining quotient of the finite units by the signs.
The same representatives specialize (A.2.3.14), p. 549, to $\mathbb Q$.
Together with `rationalIdeleClassLogSplit`, this identifies the two
factors of (A.2.2.3) in logarithmic coordinates. This is the group
identification, not a measure comparison or a rendered-page reading.

## Checked product of local Haar probabilities on the rational quotient

In [RationalIdeleFiniteUnitHaar.lean](../../Proofs/Theorems/RationalIdeleFiniteUnitHaar.lean),
`Masullo.measurePreserving_rationalFiniteUnitClassEquiv` sends
`rationalFiniteUnitHaar`, the `Measure.infinitePi` of the local
integral-unit Haar probabilities, to `rationalNormOneHaar` via
$u\mapsto [(1,u)]$. This is Haar probability *on* the compact subgroup,
not restriction of full quotient Haar to the norm-one fiber.
`Masullo.rationalIdeleClassHaar_eq_logVolume_prod_finiteUnitHaar` then
expresses the full quotient Haar measure as the pushforward of Lebesgue
log measure times that compact product by the canonical class splitting,
$(x,u)\mapsto[(e^x,u)]$. There is no extra factor of two.

[RationalLocalUnitHaar.lean](../../Proofs/Lemmas/RationalLocalUnitHaar.lean)
identifies the countable product sigma-algebra with the Borel one,
using the primes index and the second countable $p$-adic unit groups.
It proves the finite-cylinder formula and invariance of the product by
coordinatewise translations. Haar uniqueness and probability
normalization then identify the transported measure.

Independent Yah statement review checked the SHA-256-matched layout
extraction of (A.2.2.3), p. 546, (A.3.2.1)–(A.3.2.5), pp. 559–560,
and A.3.3.1, p. 561. The rational unit mass prescribed in (A.3.2.2)
is one, and the radial factor $dt/t$ becomes $dx$ for $x=\log t$.
The extracted A.3.3.1 decomposition is **upstairs**; the compact
factor here comes from the induced splitting **on classes**. This
is not a rendered-page check, a formal calculation of discriminants,
or a construction of (A.3.2.5) on the upstairs restricted product.

## Checked local multiplicative Haar and its restriction to integral units

In [RationalLocalMultiplicativeHaar.lean](../../Proofs/Theorems/RationalLocalMultiplicativeHaar.lean),
`Masullo.rationalLocalMultiplicativeHaar v` is Haar on the field unit group
$\mathbb Q_v^\times$ with its Borel sigma-algebra. The map
`Masullo.rationalLocalUnitInclusion v` sends integral units to field units
via the ring inclusion. Its image is compact and open: In the field unit
group it consists of elements whose values and inverses both lie in the
open valuation subring. The inclusion is an open embedding.

`Masullo.rationalLocalMultiplicativeHaar_unitMass` and
`Masullo.rationalLocalMultiplicativeHaar_eq` give existence and uniqueness
at unit mass one. `Masullo.comap_rationalLocalMultiplicativeHaar` shows
that restriction, expressed in integral-unit coordinates by comap, is
exactly `rationalLocalUnitHaar v`, the probability used in the quotient
product. Haar pulls back under the open embedding, and its mass on the
whole source is the ambient measure of the image. Compact Haar uniqueness
then identifies the result. The same conclusion holds for any ambient
Haar measure with the stated unit mass, by the uniqueness theorem.

Independent Yah statement review checked the SHA-256-matched layout
extraction of Definition A.3.2.2 and (A.3.2.2)–(A.3.2.5), p. 560.
For $\mathbb Q$, the extension of the completed integer ring over
$\mathbb Z_p$ is trivial, so its discriminant is one. This is the
normalization used in Lean, not a formal discriminant calculation.
The additive-density identity (A.3.2.3), the global restricted product
(A.3.2.5), and the resulting upstairs strip mass are not proved here.
There has been no rendered-page review of these passages.

## Checked positive real multiplicative measure

`Masullo.map_volume_exp_eq_restrict_realMultiplicative` in
[RealMultiplicativeMeasure.lean](../../Proofs/Theorems/RealMultiplicativeMeasure.lean)
proves $\exp_*dx=\mu_\infty|_{(0,\infty)}$ as measures on $\mathbb R$.
Here $\mu_\infty$ is Lebesgue measure restricted to $\mathbb R\setminus\{0\}$
and weighted by $|t|^{-1}$. On a Borel set $s$, the proof applies
Mathlib's one-variable Jacobian theorem to $\log$ on $s\cap(0,\infty)$;
its image is precisely $\exp^{-1}(s)$. The corollary
`Masullo.restrict_realMultiplicative_Icc_one` gives mass $\log T$ on
$[1,T]$ for $T\ge1$, so the real strip $[1,e]$ has mass one.

The source is Definition A.3.1.2(1), p. 556, for real additive Lebesgue
measure, and A.3.2.2(1), p. 560, for the density on the field units.
The real-place domain in (A.2.3.14), p. 549, is positive, so the strip
in A.3.3.1, p. 561, uses just this component. Pushing forward the
whole real multiplicative measure by absolute value instead would add
the negative ray. This is a local measure identity, not an upstairs
Tamagawa measure construction. Source evidence is the digest-matched
layout extraction, not the rendered pages.

## Checked upstairs Haar and window strip mass

In [RationalIdeleHaarComparison.lean](../../Proofs/Theorems/RationalIdeleHaarComparison.lean),
`Masullo.rationalIdeleHaar` is Haar on the **actual** rational idele
group with its Borel sigma-algebra. The calibration set is
$K=W\cap\{a:1\le |a|\le e\}$ upstairs. It is compact as the image of
the compact quotient strip under the inverse window homeomorphism
followed by inclusion. It has nonempty interior: The open window
intersected with $1<|a|<e$ contains the canonical log section at $1/2$.
Thus `Measure.haarMeasure` gives $K$ mass one without assuming the
restricted-product measure formula.

`Masullo.map_restrict_rationalIdeleHaar` identifies the pushforward of
the **whole** window restriction with `rationalIdeleClassHaar`.
`Masullo.rationalIdeleHaar_normStrip` consequently gives the constructed
upstairs Haar mass $\log T$ on $W\cap\{a:1\le |a|\le T\}$ for all
$T\ge1$, without a normalization premise. This is the rational strip
formula of A.3.3.1, p. 561, for the canonical section and the positive
window from (A.2.3.14), p. 549, using unit norm-one mass from
(A.3.2.1), p. 560. The identification of those source sets and the
scale uses the SHA-256-matched layout extraction, not rendered pages.
This does not prove the counting-measure integration formula on
arbitrary upstairs tests or the product characterization (A.3.2.5).

## Checked open embedding of every rational idele stage

[The finite-stage theorem](../../Proofs/Theorems/RationalIdeleFiniteStage.lean)
uses an arbitrary `Finset` $S$ of finite places. The stage is the product
$\mathbb R^\times\times\prod_{v\in S}F_v^\times\times
\prod_{v\notin S}\mathcal O_v^\times$ with its product topology. The
homomorphism `Masullo.rationalIdeleFiniteStageEmbedding` inserts these
coordinates into Mathlib's `IdeleGroup (𝓞 ℚ) ℚ`. The coordinate equations
identify them with the real coordinate and the full and integral finite
coordinates, respectively. `Masullo.range_rationalIdeleFiniteStageEmbedding`
identifies its image as the ideles whose value **and inverse** are
integral off $S$. `Masullo.isOpenEmbedding_rationalIdeleFiniteStageEmbedding`
proves that the map is a homeomorphism onto that open image. No sign
restriction is imposed, even for $S=\varnothing$.

The supporting [adele stage](../../Proofs/Lemmas/RationalAdeleFiniteStage.lean)
embeds by first taking the restricted product along the principal filter
on the complement of $S$, then including it into the cofinite restricted
product. The topology at the principal stage is induced by coordinate
evaluation. Passing to units preserves the embedding in the inverse-pair
topology. The range condition is open since the two integrality conditions
are preimages of an open finite adele stage under the value and inverse maps.

Independent Yah statement review matched the interface against the pinned
layout extraction: The open boxes in Lemma A.1.1.2(4)–(5), p. 540; the
inverse-pair topology and restricted product in Definition A.1.3.1 and
Lemma A.1.3.3, p. 541; and the signed factor upstairs versus the positive
quotient coordinate in (A.2.2.1)–(A.2.2.3), p. 546. The manuscript set of
places is $\{\infty\}\cup S$. This is the full restricted-product stage,
not the smaller $S$-idele group in (A.1.5.2), p. 543. The restricted-product
prescription on p. 556 uses these stages in Lemma A.3.2.4, equation
(A.3.2.5), p. 560. The readings are from a SHA-256-matched extraction, not
rendered pages. The Lean result is topological, not a measure comparison.

## Checked full real local multiplicative Haar measure

[RealMultiplicativeHaar.lean](../../Proofs/Theorems/RealMultiplicativeHaar.lean)
constructs `Masullo.realMultiplicativeHaar` on all of $\mathbb R^\times$
with Mathlib's measurable structure, proved Borel by `realUnitsBorelSpace`.
`map_realMultiplicativeHaar_val` says that pushing it forward by the value
map gives Lebesgue measure restricted off zero and weighted by $|t|^{-1}$.
The Haar instance uses the signed scaling $t\mapsto at$: The absolute
Jacobian $|a|$ cancels the density change even when $a<0$. No sign
probability or folding is used. `realMultiplicativeHaar_unitStrip` gives
mass one on the inverse image of $[1,e]$ under the value map, not under
the absolute value. It reuses the checked positive-ray identity.

Independent Yah statement review matched the full signed density with
Definition A.3.1.2(1), p. 556, and Definition A.3.2.2(1), p. 560, in the
SHA-256-matched text extraction. The positive-strip mass is a project
calibration for the comparison below, not a normalization prescribed by
that definition. The source reading is provisional, with no rendered-page
inspection. This verifies the real local factor only, not (A.3.2.5).

## Checked finite-stage product of local Haar measures

[The finite-stage Haar theorem](../../Proofs/Theorems/RationalIdeleFiniteStageHaar.lean)
`Masullo.comap_rationalIdeleHaar_finiteStage` identifies the restriction of
`rationalIdeleHaar` to the open image of `rationalIdeleFiniteStageEmbedding S`,
expressed by comap in stage coordinates. For every finite set $S$ of
rational finite places, the result is exactly

$$
\mu_\infty\otimes\left(\bigotimes_{v\in S}\mu_v\right)
\otimes\left(\bigotimes_{v\notin S}h_v\right),
$$

where $\mu_\infty=dt/|t|$ on all of $\mathbb R^\times$, $\mu_v$ is
Haar on the full local field units with integral-unit mass one, and
$h_v$ is the integral-unit Haar probability. The off-$S$ product uses
`Measure.infinitePi`, not the finite `Measure.pi` used in $S$. The
ambient measurable space is assumed Borel; in the stage coordinates,
the product measurable space is proved Borel. The result holds for
$S=\varnothing$ and still retains both real signs.

The [supporting lemmas](../../Proofs/Lemmas/RationalIdeleFiniteStageMeasure.lean)
prove coordinatewise invariance of the probability product off $S$.
The stage product is Haar, as is the comap along the open embedding.
The preimage of the upstairs positive finite-unit strip is the product
of the signed-coordinate set $[1,e]$, the ranges of the local unit
inclusions in $S$, and the whole off-$S$ factor. Finite unit valuations
are one there, so the idelic norm equals the positive real value.
Both measures give this compact set with interior mass one, and Haar
uniqueness gives equality on the whole stage.

Independent Yah statement review matched the stage restriction on p. 556
with Lemma A.3.2.4, (A.3.2.5), p. 560, in the SHA-256-matched layout
extraction. Definition A.1.3.1 and Lemma A.1.3.3, p. 541, specify the
ideles and their norm. Definition A.3.2.2, p. 560, specifies the full
signed real factor and the finite unit mass, which is one over $\mathbb Q$.
The positive strip fixes the scalar by (A.3.2.1) and A.3.3.1, pp. 560–561;
it does not cut down the real factor in (A.3.2.5). This is a rational
result, with provisional extracted-text readings, not rendered-page review.

## Checked global restricted-product characterization

`Masullo.iUnion_range_rationalIdeleFiniteStageEmbedding` in
[the stage module](../../Proofs/Theorems/RationalIdeleFiniteStage.lean)
shows that the open stage images cover the full rational idele group.
For a given idele, its value and inverse are both adeles, so their
exceptional places have finite union. Taking that union as $S$ puts
it in the image, without a restriction on its real sign.

`Masullo.rationalIdeleHaar_eq_iff_finiteStage` in
[the Haar module](../../Proofs/Theorems/RationalIdeleFiniteStageHaar.lean)
characterizes `rationalIdeleHaar` among Borel measures on the actual
idele group. The characterization is agreement of the comaps along
all stage embeddings with the local product measures above. The
finite places inject into the primes, so the finite sets of places form
a countable index. Mapping each stage comap back upstairs recovers the
restriction to its image. Countable restriction extensionality then
gives global equality, with no Haar or finiteness assumption on the
competing measure. The previous finite-stage theorem shows that
`rationalIdeleHaar` realizes the prescription. This proves (A.3.2.5)
over $\mathbb Q$ in the sense of the prescribed restrictions on p. 556.
Independent Yah review checked pp. 556 and 560 against the SHA-256-matched
layout extraction. The source prescribes uniqueness among Haar measures;
uniqueness among all Borel measures is the checked strengthening. The
review confirmed the signed real factor and the off-$S$ compact factors,
not a comparison with the smaller $S$-idele group alone. Rendered-page
verification remains open.

For verification, build `Proofs` with warnings as errors, run
`leanchecker` on `Theorems.RationalIdeleFiniteStage` and
`Theorems.RationalIdeleFiniteStageHaar`, and audit the types and axioms
of both new declarations. The claim is multiplicative, and establishes
neither the additive Haar formula nor the general number-field formula.

## Checked standard additive character over Qp

The accepted base `261011e98206057abb5b7f1885d669b5ca1c7d8a` already
closes the preceding handoff's global multiplicative Haar obligation.
The independent additive branch now has
[`Masullo.padicStdAddChar`](../../Proofs/Theorems/PadicStandardCharacter.lean)
for every prime $p$. Example A.3.1.6, p. 557, defines the positive
character via the inclusion of $\mathbb Q_p/\mathbb Z_p$ as the
$p$-primary subgroup of $\mathbb Q/\mathbb Z$ followed by $e^{2\pi i t}$.
The Lean realization clears denominators: If $a=p^n x\in\mathbb Z_p$,
`padicStdAddChar_apply_of_scaled_integral` gives the standard cyclic
character at $a\bmod p^n$, with no minimality assumption on $n$.
This includes $n=0$, when the modulus is one.

The [denominator lemmas](../../Proofs/Lemmas/PadicCharacterDenominators.lean)
use the $p$-adic valuation to find an integral numerator. The transition
from $n$ to $n+k$ multiplies both the residue representative and the
modulus by $p^k$, so the positive cyclic exponential is unchanged. A
common denominator proves additivity. `padicStdAddChar_eq_one_iff`
identifies the kernel with $\|x\|\le1$ via the kernel of `toZModPow`;
`norm_padicStdAddChar` gives unit modulus, and `continuous_padicStdAddChar`
uses constancy near each point. These are checked details of the source
construction, not a classification of continuous characters or a proof
of Plancherel or adelic Poisson summation.

Independent Yah review verified the SHA-256-matched extraction of
pp. 557–558 and checked the scaled formula, denominator independence,
and exact kernel against the quotient description. Rendered-page
verification remains open. The extracted noncentered formula (A.3.1.5)
prints the positive character phase, whereas the negative-exponent
Fourier convention would give the phase $\psi_p(-ay)$ at frequency $y$
for a translate by $a$. The checked character keeps the positive sign
from the definition and does not use that translated formula. Also
reconcile finite and real signs before the global product in Example
A.3.1.8: Taking both positive as extracted yields $e^{4\pi i/p}$ on
diagonal $1/p$ for odd $p$, not a character trivial on $\mathbb Q$.
Neither sign issue changes the centered indicator transform.

The candidate checks are `lake --wfail build Proofs`,
`lake env leanchecker Theorems.PadicStandardCharacter`, and `#check` and
`#print axioms` on the character and its four public theorems.

<a id="next-fourier-step-the-local-integral-indicator-over-qp"></a>

## Checked Fourier transform of the integral indicator over Qp

[`Masullo.padicAddHaar`](../../Proofs/Theorems/PadicIntegralBallFourier.lean)
is additive Haar on the Borel sets of $\mathbb Q_p$, normalized using
its compact open closed unit ball $B=\mathbb Z_p$. The separate theorem
`padicAddHaar_integralBall` gives $\nu_p(B)=1$.
`padicIntegralBall_fourier` proves, pointwise for every $y\in\mathbb Q_p$,

$$
\int_B \overline{\psi_p(xy)}\,d\nu_p(x)=\mathbf 1_B(y).
$$

For $y\in B$ the integrand is one by the exact kernel theorem. Otherwise,
translation by $1$ preserves both the ambient Haar measure and the ball.
Apply translation invariance to the indicator times the integrand: The
integral is multiplied by $\overline{\psi_p(y)}\ne1$, so it vanishes.
The measure used in the set integral is the restriction of ambient Haar,
not an additive Haar measure on $\mathbb Q_p$ in its own right.

Independent Yah review checked the statement and this proof route against
the SHA-256-matched layout extraction: Definition A.3.1.2(3), (A.3.1.2),
p. 556, and Examples A.3.1.6–7, pp. 557–558. We use the conjugated kernel
following the real negative-exponent convention of Example A.3.1.5,
p. 557; the centered unit-ball identity is the same for either sign.
This does not establish the topological dual parametrization or the
Plancherel identification inferred in Example A.3.1.7. Example A.3.1.10,
p. 558, concerns the inverse different and a different volume in general.
Rendered-page verification remains open.

Exact-candidate checks: `lake --wfail build Proofs`,
`lake env leanchecker Theorems.PadicIntegralBallFourier`, and an external
Lean import checking the Haar instance, both statements, and their axioms.

<a id="next-fourier-step-dilated-and-translated-integral-balls"></a>

## Checked Fourier transform of dilated and translated integral balls

In [PadicIntegralBallFourier.lean](../../Proofs/Theorems/PadicIntegralBallFourier.lean),
`Masullo.padicTranslatedBall_fourier` gives, for every prime $p$,
$N\in\mathbb N$, and $a,y\in\mathbb Q_p$,

$$
\int_{a+p^N B}\overline{\psi_p(xy)}\,d\nu_p(x)
=p^{-N}\overline{\psi_p(ay)}\,\mathbf 1_{p^{-N}B}(y),\qquad B=\mathbb Z_p.
$$

The position set in Lean is the preimage of $B$ under
$x\mapsto p^{-N}(x-a)$. The frequency indicator is evaluated at $p^Ny$
in $B$, so translation changes the phase but does not shift the support.
[PadicBallPartition.lean](../../Proofs/Lemmas/PadicBallPartition.lean)
identifies the $p^N$ residue fibers in $B$ with translates of $p^N B$
and computes their common mass $p^{-N}$ by disjoint additivity. This
includes $N=0$. `Masullo.padicAddHaar_map_inv_pow` then uses uniqueness
of additive Haar: The pushforward by **inverse** dilation has mass
$\nu_p(p^N B)$ on $B$, so it is $p^{-N}\nu_p$. The affine change of
variables reduces the transform to the checked centered identity at
$p^N y$.

Independent Yah review checked both statement interfaces against the
SHA-256-matched extraction of pp. 556–558. Equation (A.3.1.4) is an
adelic image-set formula, not a pushforward formula for the same map.
The calculation is a **repair under the negative-exponent convention**
of Example A.3.1.5, p. 557, not a literal transcription of (A.3.1.5).
The extracted phase is positive and its intermediate expression shifts
the frequency. At $p=3$, $N=1$, $a=1$, and $y=1/3$, the checked
formula gives $e^{-2\pi i/3}/3$, distinguishing the signs. At $N=0$,
$a=1/p$, and $y=0$, the checked value is one, unlike the extracted
shifted-frequency expression. These source observations are provisional
until rendered-page review. This result is pointwise for natural $N$;
it does not prove dual parametrization, Plancherel, or adelic Poisson
summation.

Candidate checks: Full `lake --wfail build Proofs`, `leanchecker` on the
Fourier and residue-partition modules, and an external import checking
the declaration types and axioms.

<a id="next-fourier-step-cancel-the-rational-diagonal-phases"></a>

## Checked cancellation of the rational diagonal phases

[The diagonal phase theorems](../../Proofs/Theorems/RationalDiagonalPhases.lean)
prove, for every $r\in\mathbb Q$ and finite set $S$ of primes containing
all prime divisors of its reduced denominator,

$$
\prod_{p\in S}\psi_p(r)=e^{2\pi i r},\qquad
 e^{2\pi i r}\prod_{p\in S}\overline{\psi_p(r)}=1.
$$

`Masullo.rationalPadicPhase` is the positive `padicStdAddChar` composed
with the canonical rational cast. The local [support and residue lemmas](../../Proofs/Lemmas/RationalPadicPhase.lean)
show the phase is one exactly off the denominator primes. For each $p$,
take a natural residue representative $b_p$ of an integral numerator
$p^{n_p}r$. The rational turns $b_p/p^{n_p}$ have the same phase as
$r$ at $p$, give its positive exponential there, and are integral at
all other primes. The sum over $S$ therefore agrees with $r$ modulo the
local character kernel at every prime. The difference is an integer:
Otherwise its reduced denominator has a prime divisor, where it cannot
be integral. This proves the product identity by real exponential
periodicity without a separate CRT lemma. Empty $S$, negative numerators,
and repeated prime powers need no additional premises.

Independent Yah statement review used the digest-matched layout
extraction of Examples A.3.1.5–6, p. 557, A.3.1.8, p. 558, and
A.3.1.11, pp. 558–559. As extracted, the real and finite standard
characters are both positive and A.3.1.8 multiplies them. At $r=1/3$
that gives $e^{4\pi i/3}\ne1$, so the literal product cannot serve as
the diagonal-trivial character needed for the rational lattice pairing.
A.3.1.11 gives the dual-lattice setting, not the missing arithmetic
cancellation. Keep the positive real character and conjugate the finite
ones in the global pairing. This is a project repair for that use, not a
claim against ambient self-duality or a rendered-page reading. The
centered ball cannot detect the sign. With a conjugated global character
in the Fourier integral, the finite local factor has the *positive*
exponent; the checked translated-ball theorem for the negative exponent
then has to be conjugated for real-valued indicators.

The checked public endpoints are `Masullo.prod_rationalPadicPhase` and
`Masullo.rationalDiagonal_phase_eq_one`. The local endpoint is
`Masullo.rationalPadicPhase_eq_one_iff`.

## Checked rational adelic character

[The rational adelic character](../../Proofs/Theorems/RationalAdeleCharacter.lean)
is an `AddChar` on the actual additive group of `AdeleRing (𝓞 ℚ) ℚ`.
For the signed real coordinate $a_\infty$ and any finite set $S$
containing the nonintegral finite coordinates,

$$
\psi(a)=e^{2\pi i a_\infty}\prod_{v\in S}\overline{\psi_{p(v)}(a_v)}.
$$

Here $a_v$ is transported to $\mathbb Q_{p(v)}$ via Mathlib's continuous
rational algebra equivalence. The [finite factor](../../Proofs/Lemmas/RationalAdeleFiniteCharacter.lean)
is one at a place exactly when that coordinate is integral. Cofinite
integrality gives finite multiplicative support, so `finprod` is a
finite product, including for the character law. For continuity, use the
final topology on the finite restricted product: On each cofinite
principal stage the exceptional set is fixed, so the product is
continuous there, and combining it with the real factor gives
continuity upstairs. Each factor has norm one.

The public endpoints are `Masullo.rationalAdeleAddChar_eq_prod`,
`Masullo.continuous_rationalAdeleAddChar`, `Masullo.norm_rationalAdeleAddChar`,
and `Masullo.rationalAdeleAddChar_algebraMap`. The last proves
$\psi(\iota(r))=1$ for every $r\in\mathbb Q$. The algebra maps identify
the real and finite inputs with the canonical rational casts; the
finite set is reindexed by `Rat.HeightOneSpectrum.primesEquiv`, and
the checked diagonal phase identity gives the cancellation.

Independent Yah statement review used the digest-matched layout
extraction of Examples A.3.1.5–6, A.3.1.8, and A.3.1.11, pp. 557–559.
The finite conjugation repairs the extracted same-sign product for
the lattice pairing. This does not establish a defect in ambient
self-duality. In particular, writing the Fourier kernel as
$\overline{\psi(xy)}$ gives the **positive** sign at the finite places;
conjugate the checked negative-sign ball formula for real indicators.
For the pairing $(a,b)\mapsto\psi(ab)$ the diagonal identity supplies
only inclusion of the rational diagonal in its annihilator. The
annihilator tests against **all** diagonal rationals and is not the
kernel of the single character. The review did not inspect rendered
pages. Additive Haar, Plancherel, and adelic Poisson summation are still
open.

## Checked clearing of finite adelic denominators

[`Masullo.exists_rational_sub_mem_integral`](../../Proofs/Theorems/RationalAdeleDenominators.lean)
proves that for every $a\in\mathbb A_{\mathbb Q}$ there is one
$q\in\mathbb Q$ such that $a_v-q\in\mathcal O_v$ at **every** finite
place $v$. There is no restriction on the real coordinate.

[`Masullo.exists_padicPhase_turns`](../../Proofs/Lemmas/RationalPadicPhase.lean)
now works for arbitrary $x\in\mathbb Q_p$, not just rational input.
Scale $x$ by $p^n$ into $\mathbb Z_p$, choose its nonnegative residue
$b$ modulo $p^n$, and take $t=b/p^n$. Its positive local character
matches $x$ at $p$, equals $e^{2\pi i t}$ there, and is one at every
other prime. Transport to the finite completions and conjugate as in
our adelic character. Sum the rational representatives over the finite
set of nonintegral coordinates. At each place, at most its own summand
contributes to the character of $q$. Outside that set both characters
are one. The exact local kernel then puts $a_v-q$ in $\mathcal O_v$.

Independent Yah statement review checked the argument, including the
empty exceptional set, against the SHA-256-matched layout extraction.
This proves the representative/surjectivity part of (A.1.2.2), p. 541,
over $\mathbb Q$, not the whole quotient isomorphism. The proof is a
direct arithmetic construction, not an appeal to the manuscript's
quotient or duality claims. Example A.3.1.11, pp. 558–559, concerns an
$S$-local lattice and invokes a quotient and finite-index argument.
Neither its $S$-local annihilator nor the global rational annihilator
is a conclusion here. Rendered-page verification remains open.

## Checked rational diagonal annihilator

[`Masullo.rationalAdele_orthogonal_iff`](../../Proofs/Theorems/RationalAdeleAnnihilator.lean)
proves, for every $a$ in Mathlib's rational adele ring,

$$
  (\forall r\in\mathbb Q,\ \psi(a\iota(r))=1)
  \quad\Longleftrightarrow\quad a\in\iota(\mathbb Q).
$$

Here $\iota$ is the diagonal algebra map and $\psi$ is the repaired character
with positive real and conjugated positive finite factors. Diagonal
membership implies the tests by diagonal triviality and multiplicativity of
$\iota$. Conversely, subtract a diagonal rational to clear the finite
denominators, without changing any test value. The test at $1$ now sees
only the real exponential, so the real coordinate is an integer.
Subtract that diagonal integer; the finite coordinates stay integral.

For the resulting adele with real coordinate zero, the test at
$\iota(p^{-n})$ is the singleton finite factor at $p$: The inverse prime
power is integral at all other finite places. The exact local kernel
implies $p^{-n}a_p\in\mathbb Z_p$ for all $n$. If $a_p\ne0$, this would
require $v_p(a_p)-n\ge0$ for every $n$; taking $n=|v_p(a_p)|+1$ gives a
contradiction. The [prime tests lemma](../../Proofs/Lemmas/RationalAdelePrimeTests.lean)
uses Mathlib's completion equivalence and valuation identities for this step.
Thus the normalized adele is zero and the original is diagonal.

This is a direct global rational calculation for the pairing in Example
A.3.1.8, p. 558, with the sign repair recorded above. The statement is
not the ambient Pontryagin-dual isomorphism asserted there. Example
A.3.1.11, (A.3.1.9)–(A.3.1.12), pp. 558–559, pairs a finite product
$\mathbb A_{F,S}$ with itself and asserts self-annihilation for
$\mathcal O_{F,S}$; that assertion is not the statement checked here.
The proof uses neither the manuscript's finite-index argument nor the
full quotient isomorphism (A.1.2.2).

Independent Yah review checked the elaborated statement and both proof
directions against the digest-matched layout extraction, including the
zero case and the arbitrary-prime singleton test. Example A.3.1.6,
p. 557, describes the finite phase through the quotient identification
with $(\mathbb Q/\mathbb Z)[p^\infty]$, not an explicit residue formula.
The theorem uses the project's explicit sign convention; whether it
coincides with the manuscript as printed also needs the convention
bridge for that identification. Rendered-page verification remains open.

<a name="next-additive-step-identify-the-quotient-topology"></a>

## Checked additive quotient topology over the rationals

In [RationalAdeleClassTopology.lean](../../Proofs/Theorems/RationalAdeleClassTopology.lean),
`Masullo.rationalAdeleQuotientEquiv` identifies $W/\mathbb Z$ with
$\mathbb A_{\mathbb Q}/\mathbb Q$ by a continuous additive equivalence, with
`Masullo.rationalAdeleQuotientEquiv_mk` specifying the map on representatives.
Here $W$ is the open additive subgroup with every finite coordinate integral,
and both groups are the actual Mathlib topological quotients. Finite denominator
clearing gives surjectivity, the local integral kernels identify the kernel
with the integer diagonal, and openness of $W$ makes the restricted quotient
map open. The inverse continuity follows from the two quotient topologies,
not merely from continuity and bijectivity.

`Masullo.discreteTopology_rationalDiagonal` isolates zero by intersecting $W$
with the real interval $(-1,1)$. `Masullo.isClosed_rationalDiagonal` then uses
the closedness of a discrete subgroup in a Hausdorff topological group, and
`Masullo.t2Space_rationalAdeleClasses` gives Hausdorffness of the quotient.
`Masullo.compactSpace_rationalAdeleClasses` uses the closed strip $[0,1]$
in the real coordinate and the compact product of local integral rings,
transported via [the empty-stage homeomorphism](../../Proofs/Lemmas/RationalIntegralAdeles.lean).
Subtracting the floor from a representative in $W$ puts it in this compact
window. The proof does not use the global pairing or self-duality.

Independent Yah statement review checked (A.1.2.1) and (A.1.2.2),
pp. 540–541, in the digest-matched layout extraction. This handles the rational
quotient isomorphism and discrete, closed diagonal and compact Hausdorff quotient
claims, in local product coordinates. The comparison of the product of local
integral rings with the manuscript's abstract ideal-adic completion is not
formalized here, and neither are unique divisibility, functoriality, or the
general number field. Rendered-page verification remains open.

## Checked half-open additive fundamental domain

In [RationalAdeleFundamentalDomain.lean](../../Proofs/Theorems/RationalAdeleFundamentalDomain.lean),
`Masullo.rationalAdeleUnitStrip` is the set of adeles with real coordinate in
$[0,1)$ and every finite coordinate integral. The accepted
`rationalIntegralAdelesHomeomorph` identifies it in local product coordinates
with $[0,1)\times\prod_p\mathbb Z_p$. This is the window in Example A.2.1.3,
(A.2.1.5)–(A.2.1.6), pp. 545–546, in the digest-matched layout extraction;
the identification of the abstract ideal-adic completion with the product
is not a separate Lean result here.

`Masullo.existsUnique_rational_sub_mem_adeleUnitStrip` gives the pointwise
disjoint cover: For each $a\in\mathbb A_{\mathbb Q}$, exactly one $q\in\mathbb Q$
has $a-q$ in the strip. Clear the finite denominators and subtract the floor
of the resulting real coordinate. Two such representatives differ by a
diagonal rational with integral finite coordinates, hence by an integer;
its real coordinate belongs to $(-1,1)$, so it is zero.
`Masullo.measurableSet_rationalAdeleUnitStrip` proves Borel measurability
using the open integral-finite stage and the continuous real coordinate.
`Masullo.rationalAdeleUnitStrip_isAddFundamentalDomain` packages the exact
cover for any Borel measure and the diagonal subgroup's additive translation.
The minus sign in the exact statement corresponds to negating the translating
subgroup element in the `+ᵥ` action. This is not a continuous section or a
choice of Haar measure. Independent Yah review matched the pointwise claim
and half-open endpoint to the pinned extraction and checked the sign and
Borel hypotheses of the Mathlib wrapper. It did not inspect rendered pages.
The source also states precompactness, which is not a new endpoint of this
module.

<a name="next-additive-step-normalize-haar-on-the-half-open-strip"></a>

## Checked additive Haar normalization over the rationals

In [RationalAdeleAddHaar.lean](../../Proofs/Theorems/RationalAdeleAddHaar.lean),
`Masullo.rationalAdeleAddHaar` is regular additive Haar on the actual rational
adele ring with its Borel sigma-algebra. Use the open additive embedding
`Masullo.rationalAdeleIntegralEmbedding` of $\mathbb R\times\prod_v O_v$ to
transport the closed window $[0,1]\times\prod_v O_v$ as a compact set with
nonempty interior. The Haar construction gives this closed set mass one.
The comap along this embedding is Haar on the open stage, and
`Masullo.comap_rationalAdeleAddHaar_integral` identifies it with Lebesgue
measure times the Haar probability of the compact additive group $\prod_v O_v$:
Both have the same mass on the closed window, so Haar uniqueness applies.
`Masullo.rationalAdeleAddHaar_unitStrip` then computes mass one for the
**half-open** fundamental domain using Lebesgue measure of $[0,1)$.

The specific conclusion is the last sentence of Example A.3.1.8, p. 558,
in the digest-matched text extraction. Definition A.3.1.2 and Lemma A.3.1.3,
p. 556, use the real and finite local measures on every stage. The checked
comparison only splits off the real measure on the integral-finite stage;
it does not yet identify the compact Haar probability with the product of
local restrictions, or compare all stages. Definition A.3.1.1, (A.3.1.1),
p. 555, requires an induced measure on $\mathbb A_{\mathbb Q}/\mathbb Q$
with counting measure on the diagonal. The checked result computes the
upstairs mass that fixes its scale, not the induced-measure theorem. No
ambient Pontryagin duality, Plancherel, or Poisson summation is used.

## Checked probability Haar on the additive rational quotient

In [RationalAdeleClassHaar.lean](../../Proofs/Theorems/RationalAdeleClassHaar.lean),
`Masullo.rationalAdeleClassHaar` is the pushforward of `rationalAdeleAddHaar`
restricted to the half-open strip, along the actual quotient map
$\pi:\mathbb A_{\mathbb Q}\to\mathbb A_{\mathbb Q}/\mathbb Q$. Both
measurable spaces are assumed Borel for their given topologies.
`Masullo.measurePreserving_rationalAdeleClass_mk` gives the corresponding
measure-preserving map. The pushforward has total mass one by the checked
strip mass. To prove invariance, lift a translating class to an adele $a$.
Its translate of the strip is another fundamental domain by
`IsAddFundamentalDomain.vadd_of_comm`. The preimage of a Borel quotient
set is invariant under the countable rational diagonal, so Mathlib's
`IsAddFundamentalDomain.measure_set_eq` compares its intersection masses
on the two domains. This and upstairs translation invariance prove the
quotient invariance. On the compact Hausdorff quotient, proportionality
of Haar measures and total mass one give `Masullo.eq_rationalAdeleClassHaar`:
Every additive Haar probability is this measure. Comparison with Haar
normalized on the whole compact group also gives regularity.

Independent Yah statement review checked the rational specialization
against the digest-matched extraction of Example A.2.1.3, pp. 545–546,
Definition A.3.1.1, (A.3.1.1), p. 555, and Example A.3.1.8, p. 558. The
source normalizes the quotient from upstairs Haar and counting measure
on the diagonal, using Theorem C.4.4.3, (C.4.4.5), p. 718, in the proof of
Lemma A.3.1.3, p. 556. The direct pushforward argument proves probability
Haar on the quotient, not yet its characterization by that counting
integral. It does not prove the all-stage local product formula, or use
adelic self-duality. The source reading is provisional, not visual.

## Checked nonnegative Weil formula over the additive rational quotient

In [RationalAdeleWeil.lean](../../Proofs/Theorems/RationalAdeleWeil.lean),
`Masullo.lintegral_eq_lintegral_rationalAdelePeriodization` proves for all
Borel $f:\mathbb A_{\mathbb Q}\to[0,\infty]$ that
$$
\int_{\mathbb A_{\mathbb Q}} f\,d\mu
  = \int_{\mathbb A_{\mathbb Q}/\mathbb Q}
      \sum_{d\in\mathbb Q} f(s(c)+d)\,d\lambda(c).
$$
Here $\mu$ is the checked additive Haar, $\lambda$ is the checked quotient
probability, and the inner sum is counting on the diagonal subgroup
(the injective image of $\mathbb Q$). Neither side is required to be finite.
`Masullo.rationalAdelePeriodization_mk` proves that replacing $s(c)$ by
any lift of $c$ leaves the sum unchanged, pointwise, by reindexing a
translation of the diagonal. `Masullo.measurable_rationalAdelePeriodization`
then supplies Borel measurability for Borel $f$ by countable summation.

[RationalAdeleStripSection.lean](../../Proofs/Lemmas/RationalAdeleStripSection.lean)
constructs $s(c)$ as the unique representative in the half-open strip.
The compact windows $[0,t]\times\prod_p\mathbb Z_p$, indexed by rational
$t<1$, cover it. Their projections are continuous injections into a
Hausdorff quotient, hence closed embeddings. For each Borel set upstairs,
the preimage under $s$ is a countable union of the images of its
intersections with these windows. The integral proof applies Mathlib's
`IsAddFundamentalDomain.lintegral_eq_tsum''` on the strip, exchanges the
countable nonnegative sum with the strip integral, and uses the checked
measure-preserving projection to obtain the quotient integral.

Independent Yah statement review checked the digest-matched extraction
of (C.4.4.5), p. 718, and (D.1.2.1), p. 747, for the quotient integral;
Proposition D.1.2.4(1)–(2), p. 748, identifies the discrete counting measure
and the bijective fundamental-domain projection. The half-open strip is
from Example A.2.1.3, pp. 545–546. With Definition A.3.1.1, p. 555, this checks
the counting-measure compatibility of the rational additive normalization.
The $[0,\infty]$ formulation is a project extension for Borel functions,
not a proof of the complex $L^1$ or Pettis claims in the manuscript. The
source reading is provisional, not visual.

## Checked complex Weil formula and absolute summability

In [RationalAdeleWeil.lean](../../Proofs/Theorems/RationalAdeleWeil.lean),
`Masullo.integral_eq_integral_rationalAdeleComplexPeriodization` proves
for Borel $f:\mathbb A_{\mathbb Q}\to\mathbb C$ integrable for $\mu$ that
$$
\int_{\mathbb A_{\mathbb Q}} f\,d\mu
  = \int_{\mathbb A_{\mathbb Q}/\mathbb Q} P f\,d\lambda,
\qquad P f(c)=\sum_{d\in\mathbb Q} f(s(c)+d).
$$
The nonnegative formula for the extended norm makes the norm sum
integrable. `Masullo.ae_summable_norm_rationalAdeleComplexPeriodization`
proves absolute summability for $\lambda$-almost all classes, and
`Masullo.integrable_rationalAdeleComplexPeriodization` uses the norm sum
to dominate $P f$. The Borel representative uses a totalized complex
sum. `Masullo.rationalAdeleComplexPeriodization_mk` reindexes it at every
lift without asserting everywhere convergence. The integral equality
splits upstairs over translated strips, exchanges the sum with the
Bochner integral on the strip using summability of the norm integrals,
and pushes forward to the quotient.

Independent Yah statement review checked the digest-matched layout
extraction of (D.1.2.1), p. 747, Proposition D.1.2.4, p. 748, and
Theorem D.1.2.7, p. 749. This is the rational diagonal, complex Borel
$L^1$ case of D.1.2.1 and the parallel (C.4.4.5), p. 718. The review
confirmed counting measure, the unit-strip quotient probability in
(A.3.1.1), and the distinction between absolute convergence almost
everywhere and invariance of the totalized sum everywhere. This does
not prove the general locally compact group result, a Pettis formula,
or any Fourier inversion statement. The reading is provisional, not visual.

## Checked unfolding of the quotient Fourier coefficients

In [RationalAdeleClassFourier.lean](../../Proofs/Theorems/RationalAdeleClassFourier.lean),
`Masullo.rationalAdeleClassChar` descends $a\mapsto\psi(a\,\iota r)$ for
$r\in\mathbb Q$ to a continuous unit-modulus additive character
$\chi_r$ on $C=\mathbb A_{\mathbb Q}/\mathbb Q$. The lift formula
`rationalAdeleClassChar_mk` uses triviality of $\psi$ on the diagonal:
Multiplication by $r$ preserves that diagonal. Moreover,
`Masullo.rationalAdeleClassChar_separates` proves that distinct classes
are distinguished by some $\chi_r$. Equality for all $r$ puts the
difference of the two lifts in the checked diagonal annihilator.

For Borel $f:\mathbb A_{\mathbb Q}\to\mathbb C$ integrable for $\mu$,
`Masullo.integral_rationalAdeleComplexPeriodization_mul_conj_char` proves
$$
\int_C P f(c)\overline{\chi_r(c)}\,d\lambda(c)
  = \int_{\mathbb A_{\mathbb Q}} f(a)\overline{\psi(a\,\iota r)}\,d\mu(a).
$$
The conjugated phase is bounded by one, so complex Weil applies to the
twisted function. The phase is constant on each fiber and factors out
of the totalized sum. Absolute convergence is still only guaranteed
$\lambda$-almost everywhere. The measures are the checked upstairs Haar
and induced quotient probability of (A.3.1.1), p. 555, with counting
measure on the rational diagonal.

Independent Yah review of the digest-matched layout extraction confirmed
that Theorem D.1.2.7(1), p. 749, is the coefficient restriction. It
checked the quotient measure, the twist, and point separation against
the accepted dependencies. The negative sign agrees with Example
A.3.1.5, p. 557. The overbar in (D.1.1.4), p. 746, is ambiguous in the
layout extraction, but the proof on p. 773 explicitly says the
convention in (D.1.1.4) conjugates the character. The discussion on
p. 813 likewise attributes evaluation at the inverse character to this
conjugation. This is textual corroboration, not a rendered-page check.
It concerns the Fourier kernel, not the separate [repair of the global
character](#checked-cancellation-of-the-rational-diagonal-phases).
Using $-r$ gives the opposite convention. The Lean theorem is only at
the displayed characters; it does not identify the full dual or invoke
Plancherel.

Verification: Build `Proofs` with `lake --wfail`, run `lake env
leanchecker Theorems.RationalAdeleClassFourier`, and `#print axioms`
for the coefficient comparison and quotient separation endpoints.

## Checked density and orthogonality of the rational quotient characters

In [RationalAdeleClassFourierBasis.lean](../../Proofs/Theorems/RationalAdeleClassFourierBasis.lean),
`Masullo.closure_span_rationalAdeleClassCharMap` proves that the **finite
complex span** of the bundled characters $\chi_r$, $r\in\mathbb Q$, is dense
in $C(C,\mathbb C)$ for the sup norm, with $C=\mathbb A_{\mathbb Q}/\mathbb Q$.
The span itself is a unital star subalgebra: $\chi_0=1$,
$\chi_r\chi_s=\chi_{r+s}$, and $\overline{\chi_r}=\chi_{-r}$. Apply complex
Stone–Weierstrass using the checked separation of quotient points.

`Masullo.integral_rationalAdeleClassChar_mul_conj` proves
$\int_C \chi_r\overline{\chi_s}\,d\lambda=\mathbf1_{r=s}$ for the checked
quotient Haar probability. When $u=r-s\ne0$, the adele with real coordinate
$1/(2u)$ and finite coordinates zero has $\chi_u=-1$ on its class. Translating
the integral by that class negates it, so it vanishes. For $r=s$, the
integrand is one and the mass is one.

Independent Yah statement review at `89334848` checked the digest-matched
layout extraction of Theorem D.1.2.7, p. 749, and the accepted character,
quotient topology, and Haar declarations. These are **project-derived**
steps toward part (3), not separate assertions of Masullo's theorem.
Situation D.1.2.6, pp. 748–749, invokes the topological identification of
$H^\perp$ with the quotient dual (Lemma D.1.4.6(2), p. 758). The already
checked pairing annihilator quantifies over adeles, not all continuous
characters of the ambient group. The new proofs use neither that
identification nor Plancherel. The source reading is provisional (text
extraction, not rendered-page verification).

Verification commands: `lake --wfail build Proofs`, `lake env leanchecker
Theorems.RationalAdeleClassFourierBasis`, and `#check` / `#print axioms` for
both endpoints above.

## Checked pointwise Poisson summation with explicit convergence hypotheses

In [RationalAdelePoisson.lean](../../Proofs/Theorems/RationalAdelePoisson.lean),
`Masullo.hasSum_rationalAdeleClassFourier` proves that if the coefficients
$b_r=\int_C g\overline{\chi_r}\,d\lambda$ of a continuous quotient function
are absolutely summable, the series $\sum_r b_r\chi_r$ converges to $g$ in
the sup norm. Norm-one characters give absolute summability in the
continuous-map norm. Pair the sum with each character in $L^2(C,\lambda)$;
orthogonality identifies its coefficients with those of $g$. The difference
annihilates the dense span, so pairing it with itself gives zero $L^2$ norm.
Haar is positive on nonempty open sets, so the continuous-map embedding
into $L^2$ is injective. There is no use of adelic Plancherel.

`Masullo.hasSum_rationalAdele_poisson` gives the rational counting-series
formula at **every** $x\in\mathbb A_{\mathbb Q}$. It assumes Borel
measurability and $L^1$ integrability upstairs, everywhere absolute
summability of the diagonal fibers, continuity of their periodization on
$C$, and absolute summability of the upstairs Fourier integrals sampled at
rational frequencies. The checked coefficient comparison identifies those
samples with the quotient coefficients, and evaluation on the class of $x$
gives the formula. The Fourier series is absolutely convergent since the
reconstruction phases have modulus one. The sum uses $x+d$ rather than
$x-d$; negation reindexes the diagonal. No volume factor is inserted.

Independent Yah statement review checked the digest-matched layout
extraction of Situation D.1.2.6 and Theorem D.1.2.7(3), pp. 748–749.
This is a project proof of the rational counting-series version, not an
application of the manuscript's general dual-measure setup. That setup
requires a dual identification and the transported Plancherel measure;
the quotient proof uses neither. The reading is provisional, not a visual
check. No claim about arbitrary Schwartz–Bruhat inputs or part (2) follows.

Checks: `lake --wfail build Proofs`, `lake env leanchecker` on
`Theorems.RationalAdeleClassFourierBasis` and `Theorems.RationalAdelePoisson`,
and external `#check` and `#print axioms` on the changed public API.

## Checked periodization of the rational unramified tensor

In [RationalAdeleUnramifiedPeriodization.lean](../../Proofs/Theorems/RationalAdeleUnramifiedPeriodization.lean),
`Masullo.rationalAdeleUnramified b` is the actual adelic test
$f(a)=b(a_\infty)\mathbf 1_{\prod_p\mathbb Z_p}(a_f)$ for complex real
Schwartz $b$. It is continuous because the integral-finite stage is an
open and closed additive subgroup. It is integrable for the normalized
additive Haar: Pull back the measure restricted to the stage to Lebesgue
measure times compact Haar probability, then use the real Schwartz $L^1$
bound. Thus it is also Borel measurable.

For $a$ in the integral-finite stage,
`Masullo.rationalAdeleComplexPeriodization_unramified_mk` identifies the
quotient periodization at $[a]$ with $\sum_{n\in\mathbb Z} b(a_\infty+n)$,
including the zero index. The support condition on $a+d$ is exactly
$d\in\mathbb Z$ among diagonal $d$. This sum is absolutely convergent:
[SchwartzLatticeTranslates.lean](../../Proofs/Lemmas/SchwartzLatticeTranslates.lean)
uses inverse-square decay of the real translates in the sup norm on
compact intervals, via Mathlib's `isBigO_norm_restrict_cocompact`. It does
not use real Poisson summation. For any adele, clear finite denominators
by a diagonal rational shift, and reindex by translation of the diagonal.
This gives `Masullo.summable_norm_rationalAdeleUnramified_add` at every
lift, not just almost everywhere. The real translated sum is continuous,
so the checked integral-stage quotient map gives
`Masullo.continuous_rationalAdeleComplexPeriodization_unramified` without
requiring continuity of the half-open strip representative.

Independent Yah statement review used the digest-matched layout
extraction of Lemma 2.2.2.1(1), (2.2.2.1), p. 77, the tensors in
(2.2.2.4), p. 78, and Theorem D.1.2.7(3), p. 749. The manuscript sums
nonzero indices in (2.2.2.1) before restoring the zero term for additive
invariance. The Lean result specializes to $g=1$ with that term included;
it does not assert the compact-uniform two-variable lemma. The support
estimate (2.2.2.3) at $x=0$ is not used as an estimate for general $x$.
This is a provisional extracted-text comparison, not a rendered-page
reading. This step supplies the input, integrability, and periodization
hypotheses of `Masullo.hasSum_rationalAdele_poisson`. The Fourier-side
hypothesis is discharged separately below.

Validation: `lake --wfail build Proofs`, `lake env leanchecker` on
`Lemmas.SchwartzLatticeTranslates` and
`Theorems.RationalAdeleUnramifiedPeriodization`, and external `#check`
and `#print axioms` on the new public declarations.

## Checked Fourier transform and pointwise Poisson for the unramified tensor

For every real Schwartz function $b:\mathbb R\to\mathbb C$, put
$f_b(a)=b(a_\infty)\mathbf 1_{\prod_p\mathbb Z_p}(a_f)$. The theorem
`Masullo.integral_rationalAdeleUnramified_mul_conj_char` in
[RationalAdeleUnramifiedFourier.lean](../../Proofs/Theorems/RationalAdeleUnramifiedFourier.lean)
computes the normalized integral at **every** adelic frequency $y$:

$$
\int_{\mathbb A_{\mathbb Q}} f_b(x)\overline{\psi(xy)}\,dx
  = f_{\widehat b}(y).
$$

On the integral-finite stage, the finite phases on the support are
trivial and `comap_rationalAdeleAddHaar_integral` gives real Lebesgue
measure times a compact probability. The real sign is $-2\pi ixy$.
Off the stage, choose an adele with real coordinate zero, coordinate
$1$ at a nonintegral place of $y$, and zero at every other place.
Translation by this adele preserves the tensor and the measure but
multiplies the integral by a nontrivial scalar, forcing it to vanish.
The pairing lemmas are in
[RationalAdeleIntegralPairing.lean](../../Proofs/Lemmas/RationalAdeleIntegralPairing.lean).
The proof does not need an all-stage product formula, ambient duality,
or Plancherel.

In [RationalAdeleUnramifiedPoisson.lean](../../Proofs/Theorems/RationalAdeleUnramifiedPoisson.lean),
`Masullo.hasSum_rationalAdeleUnramified_poisson` applies the rational
pointwise Poisson theorem, with Schwartz decay giving absolute
summability of the integer samples of $\widehat b$. The diagonal
rational frequencies outside $\mathbb Z$ vanish by finite integrality.
For every adelic translate $a$, the diagonal periodization of $f_b$
is the sum of $\widehat b(n)\psi(an)$ over $n\in\mathbb Z$, with the zero
index included on both sides. There are no extra convergence premises.
This adelic proof does not invoke real Poisson summation.

Independent Yah statement review confirmed the measure, signs, and
zero terms against the digest-matched PDF text. Example A.3.1.5, p. 557,
fixes the negative real Fourier sign. Example A.3.1.6, p. 557,
gives the centered local integral-ball calculation. Example A.3.1.8,
p. 558, states the Gaussian tensor calculation and the mass-one
normalization on $[0,1)\times\prod_p\mathbb Z_p$. The general real
Schwartz factor here is a project calculation with the repaired
standard character, not the manuscript's proof of self-duality. In the
extracted A.3.1.8 the literal product of positive local characters is not
trivial on the rational diagonal; our finite factors are conjugated.
Theorem D.1.2.7(3), p. 749, gives the pointwise identity under
continuity and Fourier-side $L^1$ in its general setting. The Lean
application discharges those hypotheses in this tensor case using
its checked rational counting normalization. This is text-based,
not rendered-page verification.

Validation: Full `lake --wfail build Proofs`, `leanchecker` on the new
pairing, Fourier, and Poisson modules, and external `#check` and
`#print axioms` on the changed public declarations.

## Checked adelic theta inversion for the unramified tensor

For $f_b(x)=b(x_\infty)\mathbf 1_{\prod_p\mathbb Z_p}(x_f)$, the theorem
`Masullo.rationalAdeleUnramified_theta_inversion` in
[RationalAdeleThetaInversion.lean](../../Proofs/Theorems/RationalAdeleThetaInversion.lean)
proves at **every** rational idele $g$ that

$$
\sum_{q\in\mathbb Q^\times} f_b(qg)
 = |g|^{-1}\sum_{q\in\mathbb Q^\times} f_{\widehat b}(qg^{-1})
   + |g|^{-1} f_{\widehat b}(0) - f_b(0).
$$

The checked additive Fourier integral identifies $f_{\widehat b}$
with $\widehat{f_b}$ at every adele, including zero.
`Masullo.summable_norm_rationalAdeleUnramified_idele` gives absolute
summability of the actual tensor evaluations, also for the Fourier
sum. Neither theorem requires either zero mode to vanish.

The proof first identifies the adelic evaluations with the terms of
`rationalTheta_eq_unramified_idele_sum`. That theorem accounts for all
finite coordinates and for the real sign by principal rescaling and
reindexing. It gives scales $t=|g|>0$ and $t^{-1}=|g^{-1}|$ on the
respective sides, so the remaining dilation is only on the real
Schwartz factor: Apply the checked pointwise **adelic** Poisson theorem
at the zero translate to the tensor with real factor $b(t\,\cdot)$.
The real Fourier change of variables contributes the Jacobian $t^{-1}$.
Removing the zero summands gives the two displayed corrections. This
proof does not invoke real Poisson summation or assume that an arbitrary
idele multiplication preserves the finite support of the tensor.
The two sums depend only on the idelic norm by the norm-fiber theorem;
the endpoint is stated on representatives, not as a new bundled map on
the class group.

Independent Yah statement review checked (2.2.3.1) and (2.2.3.2),
pp. 81–82, Remark 2.2.3.3, p. 82, and Examples A.3.1.5 and A.3.1.8,
pp. 557–558, against the SHA-256-matched layout extraction. The
positive sign of the Fourier zero-mode correction, the inverse idele,
and the mass-one quotient normalization match the source. The proof
uses the full Poisson sum and explicitly removes the zero terms;
it does not use the intermediate (2.2.3.3), which in the extraction
uses $\Psi_F$ even though (2.2.2.1), p. 77, defines that sum on
$F^\times$. This is a provisional text audit, not rendered verification.
It formalizes (2.2.3.2) only for the rational unramified tensor, not
arbitrary Schwartz–Bruhat functions, number fields, or general
idelic Fourier scaling.

Validation: Full `lake --wfail build Proofs`, `leanchecker` for the new
and touched modules, and external `#check` and `#print axioms` for
the two endpoints and the exposed supporting declarations.

## Checked local product on the integral-finite additive stage

In [RationalAdeleIntegralStageHaar.lean](../../Proofs/Theorems/RationalAdeleIntegralStageHaar.lean),
`Masullo.rationalLocalIntegersAddHaar v` is the comap of the normalized
`padicAddHaar` along the open additive embedding
$O_v\hookrightarrow\mathbb Q_v\simeq\mathbb Q_{p(v)}$. The checked
compatibility of Mathlib's integer and field identifications sends its
range exactly to $\mathbb Z_{p(v)}$. Thus the comap is additive Haar of
total mass one, not a measure on the full local field or on its unit group.

`Masullo.rationalFiniteIntegersHaar_eq_infinitePi` identifies the compact
Haar probability on $\prod_v O_v$ with the countable product of those
local probabilities. The Borel structure is the product sigma-algebra;
translation invariance follows by mapping the local translations in
`Measure.infinitePi_map_pi`, and Haar uniqueness at total mass one gives
the equality. `Masullo.comap_rationalAdeleAddHaar_integral_eq_prod` then
identifies the comap along the integral-stage embedding with Lebesgue
times this product. This equality holds on the entire real coordinate,
not just on the interval used to normalize it.

In the digest-matched layout extraction, Definition A.3.1.2(1), (3),
p. 556, gives the real and finite local measures; Example A.3.1.7, p. 558,
identifies the mass-one measure over $\mathbb Q_p$ with that local
normalization. The proof of Lemma A.3.1.3, p. 556, uses the local product
on the integral-finite stage to calibrate the global measure. Example
A.3.1.8, p. 558, specifies the mass-one strip $[0,1)\times\widehat{\mathbb Z}$.
Our argument checks exactly the restriction of the global formula
in (A.3.1.3) to this stage over $\mathbb Q$. It does not invoke
self-duality or prove the separate $S$-local formula on $A_{F,S}$.
These locators are provisional readings of text, not rendered pages.

Validation route: `lake --wfail build Proofs`, `lake env leanchecker
Theorems.RationalAdeleIntegralStageHaar`, and an external `#check` and
`#print axioms` audit of the two equality theorems, the local measure,
and its Haar and probability instances.

## Checked restricted-product formula for rational additive Haar

In [RationalAdeleFiniteStageHaar.lean](../../Proofs/Theorems/RationalAdeleFiniteStageHaar.lean),
`Masullo.comap_rationalAdeleAddHaar_finiteStage` identifies the comap of
normalized rational additive Haar on every open finite stage with
Lebesgue measure times the finite product of full local field measures
in $S$ and the probability product of the local integer-ring measures
off $S$. Here $S$ indexes finite places only; the real place is always
present. The full local measure is transported from `padicAddHaar` under
Mathlib's $\mathbb Q_v\simeq\mathbb Q_{p(v)}$ and gives $O_v$ mass one.
The local integer-ring probability is its comap along the inclusion.

The stage inclusion is an open additive embedding with the product
Borel structure on its domain. Both measures are Haar, and both assign
mass one to $[0,1]\times\prod_v O_v$ in stage coordinates, so Haar
uniqueness identifies them. This compact calibration does not change
the manuscript's half-open normalization: The extra real endpoint has
Lebesgue measure zero, and `rationalAdeleAddHaar_unitStrip` already gives
the half-open strip mass one. `Masullo.rationalAdeleAddHaar_eq_iff_finiteStage`
then uses the countable open cover by stages to show that the restrictions
determine the global measure among **all Borel measures**, without a Haar
hypothesis on the comparison measure.

Independent Yah statement review checked the digest-matched layout
extraction of the restricted-product prescription preceding Definition
A.3.1.2, p. 556, the local normalizations in A.3.1.2(1), (3), p. 556,
and Examples A.3.1.7–A.3.1.8, pp. 557–558. The checked endpoint realizes
the global part of (A.3.1.3) over $\mathbb Q$, not the separate product
on $A_{F,S}$ or the quotient by the $S$-integer lattice. It does not
use self-duality. The locators are provisional readings of text, not
rendered pages.

## Checked local calibration for rational additive dilation

[PadicAddHaar.lean](../../Proofs/Lemmas/PadicAddHaar.lean) proves
`Masullo.padicAddHaar_dilate_integralBall`: For $a\ne0$ in $\mathbb Q_p$,
$\mu_p(a\mathbb Z_p)=\operatorname{ofReal}(\lVert a\rVert_p)$ for the
unit-ball-normalized additive Haar measure. The image is the ball of
radius $\lVert a\rVert_p$, so it suffices to take $a=p^k$ for an
integer $k$. For $k\ge0$ the mass is the reciprocal of the residue
index. For $k=-n$, apply the checked pushforward by $p^{-n}$ to the
expanded ball: Its preimage has mass one, and the pushforward equals
$p^{-n}\mu_p$, giving expanded-ball mass $p^n$.

[RationalLocalAdditiveModulus.lean](../../Proofs/Lemmas/RationalLocalAdditiveModulus.lean)
proves `Masullo.norm_rationalLocal_padicEquiv` and
`Masullo.rationalLocalFieldAddHaar_dilate_integers`. In Mathlib's actual
finite completion $F_v$ of $\mathbb Q$, the transported measure gives
$aO_v$ mass $\operatorname{ofReal}(\lVert a\rVert)$ for all $a\ne0$.
To identify the norm with the one used by `ideleNorm`, the proof
identifies the residue field with $\mathbb Z/p(v)\mathbb Z$, checks
that $p(v)$ has norm $1/p(v)$ on both sides, and uses the integer-ring
transport on both an element and its inverse to detect norm-one units.
Transport of the integer rings alone would not fix the norm scale.

The source basis is the digest-matched text extraction of Definition
A.3.1.2(3), p. 556, and Example A.3.1.7, pp. 557–558: In the rational
case the integer ball has mass one. The general local ball-dilation
formula is a project deduction, not a displayed statement there.
Independent Yah statement review checked the norm normalization,
the direction of transport, and the distinction from the source claim.
Lemma A.3.1.4 is an adelic image-set identity for arbitrary additive
Haar, not a pushforward identity with the same scalar. Source locators
are provisional text readings, not visual verification.

Validation route: `lake --wfail build Proofs`, `lake env leanchecker`
on `Lemmas.PadicAddHaar`, `Lemmas.RationalLocalAdditiveModulus`, and
`Theorems.PadicIntegralBallFourier`, and external `#check` and
`#print axioms` on the local endpoints and Fourier statements.

## Checked rational additive Haar scaling under idele dilation

In [RationalAdeleAdditiveDilation.lean](../../Proofs/Theorems/RationalAdeleAdditiveDilation.lean),
`Masullo.rationalAdeleHaar_image_idele_mul` proves
$\mu(gB)=|g|_{\mathbb Q}\mu(B)$ for every rational idele $g$,
Borel set $B$, and additive Haar measure $\mu$ on the actual adeles.
`Masullo.comap_rationalAdeleAddHaar_dilate` gives the measure identity
for the normalized choice. The comap is by $x\mapsto gx$ and gives the
image mass on $B$, not its preimage mass. A pushforward by that same
map would have the reciprocal factor.

Every idele is a unit of some finite-stage ring: Choose the stage to
contain the nonintegral coordinates of both $g$ and $g^{-1}$. The stage
embedding commutes with multiplication, so the closed unit strip can be
dilated within this one stage. In coordinates, the real interval is the
unordered closed interval with endpoints $0$ and $g_\infty$. The
inside factors are $g_vO_v$, and the outside factors are still the whole
integer rings by invertibility there. The checked stage product formula
computes the image mass as the real absolute value times the product of
the local norms on the stage, with norm one outside. Haar uniqueness on
the second-countable, locally compact adeles extends this calibration to
the comap, and comparing Haar normalizations gives the Borel-set result
without a separate regularity hypothesis on $\mu$.

Independent Yah statement review matched the direction, quantifiers, and
norm with Lemma A.3.1.4, p. 556, and the rational norm in (A.2.2.2),
p. 546, in the digest-matched layout extraction. The manuscript cites
[CF, Ch. XV, Lemma 4.1.2]; the checked proof over $\mathbb Q$ is a
project derivation from the finite-stage product. It does not prove the
general number-field case or use additive self-duality. Source readings
are provisional text readings, not rendered-page verification.

## Checked Fourier transform of translated finite boxes

For $b\in\mathcal S(\mathbb R,\mathbb C)$ write $U_b$ for
`rationalAdeleUnramified b`. In
[RationalAdeleBoxFourier.lean](../../Proofs/Theorems/RationalAdeleBoxFourier.lean),
`Masullo.rationalAdeleBox b a g` is $F(x)=U_b(g^{-1}(x-a))$ for an
adele $a$ and an idele $g$. Lean proves continuity and $L^1$ integrability
for this box, and $L^1$ integrability after multiplying by the Fourier
kernel at each $y$.
`Masullo.integral_rationalAdeleBox_mul_conj_char` proves, for every
adelic frequency,

$$
\int F(x)\overline{\psi(xy)}\,d\mu(x)
= |g|_{\mathbb Q}\,\overline{\psi(ay)}\,U_{\mathcal F b}(gy).
$$

The [affine substitution lemmas](../../Proofs/Lemmas/RationalAdeleAffineIntegral.lean)
use translation invariance and the checked comap law to substitute
$x=a+gz$. The character takes sums to products. Translation gives a phase,
not a shift of the frequency support, and the dilation factor is the
**direct** idelic norm. The last integral is the checked unramified one.

Independent Yah statement review checked these conventions against the
SHA-256-matched layout extraction of Examples A.3.1.5–A.3.1.8,
pp. 557–558, and the accepted unramified transform and dilation declarations.
This is a project extension of the tensor calculation in A.3.1.8, with the
negative real sign from A.3.1.5 and the corrected conjugated translation
phase from the local ball theorem. It does not assume or prove ambient
self-duality or Plancherel. The source reading is provisional, not visual.

## Checked pointwise Poisson summation for finite boxes

[Masullo.hasSum_rationalAdeleBox_poisson](../../Proofs/Theorems/RationalAdeleBoxPoisson.lean)
proves the counting-series formula of Theorem D.1.2.7(3),
(D.1.2.8), p. 749, for $F(x)=U_b(g^{-1}(x-a))$. At every adele $x$,

$$
\sum_{q\in\mathbb Q} F(x+\iota(q))
= \sum_{r\in\mathbb Q}
  |g|_{\mathbb Q}\,\overline{\psi(a\iota(r))}\,
  U_{\mathcal F b}(g\iota(r))\,\psi(x\iota(r)).
$$

Both series converge absolutely and include their zero terms. The
[Lemmas module](../../Proofs/Lemmas/RationalAdeleBoxPeriodization.lean)
uses principal normalization for any idele $k$: If $h=\iota^\times(s)k$
is normalized, its finite units preserve the integral support, and the
Schwartz factor absorbs the real scale $|k|_{\mathbb Q}$. This writes
$U_b(kz)=U_c(\iota(s^{-1})z)$ with $c(u)=b(|k|_{\mathbb Q}u)$.
With $k=g^{-1}$, rational scaling permutes the diagonal, so absolute
summability and continuity of the periodization come from the existing
unramified result. With $k=g$, the same argument at zero gives absolute
summability of $U_{\mathcal F b}(g\iota(r))$; the character factors have
unit modulus. This supplies both pointwise hypotheses in D.1.2.7(3) via
`hasSum_rationalAdele_poisson`, whose measure is normalized by the unit
strip and counting measure on the diagonal. In the digest-matched
layout extraction, (D.1.2.8) sums $f(h^{-1}x)$ in multiplicative
notation; for the additive diagonal, changing $q$ to $-q$ gives the
plus sign on the left. This is a provisional text reading. The Lean
proof uses the quotient character series, not ambient self-duality or
Plancherel.

## Checked Poisson summation on the translated generator span

[Masullo.exists_rationalAdeleBox_eq_localTensor](../../Proofs/Props/RationalAdeleBoxGenerators.lean)
realizes the generators in Example 2.1.3.1, (2.1.3.1), pp. 67–68,
over $\mathbb Q$: The real factor is Schwartz and each finite factor
is the indicator of $a_v+u_vO_v$, with center zero and scale one off a
finite set. The proof assembles the centers and both the scales and their
inverses in a finite stage. The resulting adele has real coordinate zero
and the idele has real coordinate one, so the real factor is unchanged.

[Masullo.hasSum_rationalAdeleBoxSum_poisson](../../Proofs/Theorems/RationalAdeleBoxSumPoisson.lean)
proves (D.1.2.8), p. 749, at every adele for any finite complex linear
combination of these boxes, including boxes with a real translation and
an arbitrary nonzero real dilation. `rationalAdeleBoxSum_periodization`
gives absolute convergence on every spatial fiber and continuity on the
quotient. `integral_rationalAdeleBoxSum_mul_conj_char` gives the finite sum
of the single-box transforms at every adelic frequency, using the direct
idele norm and conjugated translation phase for each term.
`summable_norm_rationalAdeleBoxSum_fourier` gives absolute summability on
the rational frequency diagonal; the evaluation character has modulus
one. Both sides include the zero index. This uses normalized additive
Haar and counting measure as in the single-box formula.

In the digest-matched layout extraction, Lemma 2.1.3.2(3), p. 68,
says *compact subgroup*, but the proof on p. 69 uses spaces of functions
on $K'_v/K_v$, where indicators of cosets, not just centered subgroups,
are needed. A linear combination of centered subgroup indicators is even
in the finite variables, whereas $1/3+\mathbb Z_3$ differs from its
negative. The Lean result follows Example 2.1.3.1's translated generators,
not the centered-only wording. This reading remains provisional pending
rendered-page inspection. The checked result concerns the algebraic
span of explicit functions, not an independently constructed full
Schwartz–Bruhat space, its LF topology, or Fourier stability of that span.

## Checked pointwise theta inversion on the generator span

[RationalAdeleBoxThetaInversion.lean](../../Proofs/Theorems/RationalAdeleBoxThetaInversion.lean)
proves the pointwise identity of Theorem 2.2.3.2, (2.2.3.2), p. 82,
over $\mathbb Q$ for a finite complex linear combination $F$ of boxes.
Writing $\Theta(F)(k)=\sum_{q\in\mathbb Q^\times} F(\iota^\times(q) k)$
and $\widehat F$ for the negative-sign integral against the normalized
additive Haar, `Masullo.rationalAdeleBoxSum_theta_inversion` gives
$$
\Theta(F)(k)=|k|_{\mathbb Q}^{-1}\Theta(\widehat F)(k^{-1})
 + |k|_{\mathbb Q}^{-1}\widehat F(0)-F(0)
$$
for every idele $k$. `Masullo.summable_norm_rationalAdeleBoxSum_theta`
proves absolute convergence of both nonzero sums without extra premises.
Here $\Theta$ denotes the nonzero sum that the manuscript calls $\Phi_F$;
the Lean definition `rationalAdeleTheta` also omits zero.

The manuscript cites Tate and Lemma 2.2.2.1. In Lean, dilating by $k$
replaces each center $a_i$ and scale $g_i$ by $k^{-1}a_i$ and
$k^{-1}g_i$. The checked affine integral gives
$\widehat{F(k\,\cdot)}(y)=|k|_{\mathbb Q}^{-1}\widehat F(k^{-1}y)$.
Apply the checked box-sum Poisson formula at zero and parametrize the
additive diagonal by $\mathbb Q$. Split off zero on each side before
reindexing the remaining terms by $\mathbb Q^\times$. This proof uses
neither an ambient duality or Plancherel theorem nor the printed
continuity assertion in Lemma 2.2.2.1. As noted in Remark 2.2.3.3,
quotient Haar has mass one for the chosen counting measure and upstairs
normalization, so no quotient volume factor occurs.

This module alone proves a pointwise identity. Continuity in the varying
idele and descent are separate and are checked below. Neither module
identifies the manuscript's LF space. Source references are to the
digest-matched layout extraction, not to rendered pages.

An independent Yah statement review against base
`a0610272274b6dd1600cc0afd0e1d67f48bcaa30` confirmed the negative-sign
integral convention, the inverse scale, the quotient mass factor of one,
the signs of the zero modes, and pointwise absolute convergence.

## Checked joint orbit convergence and theta inversion on idele classes

[Orbit convergence](../../Proofs/Props/RationalAdeleBoxOrbits.lean)
formalizes the two-variable convergence and continuity in Lemma
2.2.2.1(1)–(2), (2.2.2.1), pp. 77–81, for the rational finite box span.
For each compact subset of the actual `IdeleGroup × AdeleRing`, the
nonzero orbit series and the series of its term norms converge uniformly
as the finite set of rational unit indices increases.
`continuous_rationalAdeleBoxSum_orbit` proves joint continuity.
`rationalAdeleBoxSum_orbit_add_zero_shift` proves additive principal
invariance **after** adding back the zero sample $F(kx)$.

The [majorant proof](../../Proofs/Lemmas/RationalAdeleBoxMajorant.lean)
normalizes $g^{-1}k$ by a principal unit $r$ chosen at the neighborhood
center, where $g$ is the scale of the box. The normalized idele
$h=\iota^\times(r)g^{-1}k$ stays in the open positive finite-unit window.
For the shift $z=\iota(r^{-1})x-h^{-1}g^{-1}a$, choose $q_0\in\mathbb Q$
so that $w=z-\iota(q_0)$ is integral at the neighborhood center, and
shrink the neighborhood so the same translate works everywhere. The
finite support then forces $q/r+q_0=n\in\mathbb Z$. The real argument is
$h_\infty(n+w_\infty)$, with $h_\infty$ bounded away from zero and
$w_\infty$ bounded. The Schwartz seminorms of orders $(0,0)$ and $(2,0)$
give a majorant $C/(1+|n|^2)$, pushed through $n\mapsto r(n-q_0)$ and
extended by zero. Add bounds for the finitely many boxes and use
compactness to combine neighborhood bounds. This is a local-lattice
proof, not the literal uniform fractional-ideal assertion in part (3).

[Class theta inversion](../../Proofs/Theorems/RationalAdeleClassThetaInversion.lean)
reindexes by multiplication on $\mathbb Q^\times$. This invariance holds
for Lean's `tsum` for any function, but is not a convergence claim for
arbitrary functions. For finite box sums, restricting the joint
continuity to $x=0$ yields continuity of the spatial theta on classes.
The class theta of the Fourier integral is continuous by solving the
pointwise equality at $k^{-1}$, not by assuming Fourier stability of
this span. `rationalAdeleBoxSum_theta_inversion_class` proves (2.2.3.2)
for every rational idele class with the descended idelic norm and both
zero modes. Both sides are continuous by the preceding continuity
theorems and the continuous positive class norm. This does not assert
joint compact-uniform convergence for the Fourier input or identify the
full Schwartz–Bruhat LF space.

Independent Yah statement and source review against
`7a44fc8487b30f1eee4c79cea159f69347561ad1` checked the local-lattice
argument, additive zero restoration, the quotient interface, and the
Fourier formula against the digest-matched extraction. It also isolated
the following source issue; the visual reading remains open.

### Source interface: The finite part of the representative matters

In the layout extraction of Lemma 2.2.2.1(3), (2.2.2.2)–(2.2.2.3),
pp. 77–78, and Remark 2.2.2.2, the restriction on $g_\infty$ alone
cannot give a single fractional-ideal bound for the actual projection
of arbitrary lifts. Over $\mathbb Q$, take the unramified tensor with
real bump equal to one on $[-1,1]$ and let $g_N$ have real component
one, finite component $p^N$ at a fixed prime $p$, and one elsewhere.
The surviving rationals are in $p^{-N}\mathbb Z$, and at least $2p^N$
nonzero terms equal one. At real component one the proposed right side
for any fixed fractional ideal is finite and independent of $N$.
This is a mathematical counterexample to the literal extracted scope,
not a Lean declaration or a confirmed reading of the printed layout.

The proof's representative windows in (2.2.2.8)–(2.2.2.11), pp. 79–80,
restrict the finite components as well. Reindexing preserves the left
side, but the real component on the right must be that of the **chosen
representative**. In this example it is $p^{-N}$ after normalization.
Remark 2.2.2.3, p. 81, and the principal translation before (2.2.3.8),
p. 83, support this repaired application. The extracted tail comparison
to Proposition 2.2.1.3 must also exclude small shifted arguments: For
$\Gamma=\mathbb Z$, $K=[0,1]$, and $x=1$, excluding only $K\cap\Gamma$
still leaves a singular term at $\xi=-1$. The bounded Schwartz majorant
above does not require that comparison.

## Checked fixed-test tails on rational idele classes

[The class estimates](../../Proofs/Theorems/RationalAdeleThetaTails.lean)
prove Theorem 2.2.3.4(1)–(2), (2.2.3.4)–(2.2.3.5), pp. 82–84, over
$\mathbb Q$ for each fixed finite translated box sum $f$. For every
$m\in\mathbb N$ there are positive constants and thresholds (which
may depend on the test and on $m$) bounding $|\theta_f(d)|$ by
$C|d|^{-m}$ at large norm and bounding
$|\theta_f(d)-|d|^{-1}\widehat f(0)+f(0)|$ by $C'|d|^m$ at small norm.
The estimate is uniform in the class, not in the test.

The [absolute-sample bounds](../../Proofs/Lemmas/RationalAdeleBoxTail.lean)
apply before descent. For a single box of scale $g$, reindex by a
principal rational unit so that $g^{-1}k$ is represented by an idele
with finite-unit components and positive real component $|k|/|g|$.
Clear the finite denominators of the fixed box-coordinate center $g^{-1}a$
by one integer $D>0$. Each surviving nonzero index in the reindexed orbit
then lies in $(1/D)\mathbb Z$, with real argument $|k|n/(|g|D)-(g^{-1}a)_\infty$.
For $|k|/(|g|D)\ge\max(1,2|(g^{-1}a)_\infty|)$ its magnitude is at
least $|k||n|/(2|g|D)$. A Schwartz seminorm of order $(m+2,0)$ gives a
summable inverse-square majorant times $|k|^{-m}$. This uses the finite
restriction of the chosen representative in (2.2.3.8), not the actual
real projection of an arbitrary lift. The proof controls the total
absolute sum after reindexing, not a common majorant on the original
indices for all lifts.

On the Fourier side the integral formula gives a pointwise norm envelope
by centered boxes with scales $g_i^{-1}$, weighting each by
$|c_i||g_i|$. The conjugated translation phase has norm one. The
absolute Fourier tail at order $m+1$ offsets the factor $|d|^{-1}$
in the class inversion formula, with both zero-mode signs as in
(2.2.3.5). No Fourier-stability premise is needed.

Independent Yah statement review against
`1101354ae42f9bb3b277b5e46363a7ea71225000` matched the thresholds,
nonzero indices, chosen representative, Fourier envelope, and exponent
loss to the accepted hypotheses and digest-matched source extraction.
This is not a rendered-page reading. The extraction also warrants
care with the general-field diagonal-section scaling in (2.2.3.10)
and (2.2.3.12): The linear dependence on idelic norm used here is specific
to $\mathbb Q$.

The proofs of these endpoints now specialize the [uniform threshold-one
estimates](#checked-uniform-tails-for-fixed-finite-box-families) to
singleton Schwartz sets. Their original statements are unchanged.

Validation endpoints: `rationalAdeleBoxSum_theta_large_norm`,
`rationalAdeleBoxSum_theta_small_norm`,
`rationalAdeleBoxSum_absolute_theta_tail`, and
`rationalAdeleBoxSum_absolute_fourier_theta_tail`. Use
`lake --wfail build Proofs`, `leanchecker` on both linked modules, and
`#print axioms` on the four endpoints.

## Checked global log-norm decay for fixed box sums

[Closed positive norm bands](../../Proofs/Theorems/RationalIdeleClassCompact.lean)
are compact in the actual rational idele class topology.
`Masullo.isCompact_rationalIdeleClass_normStrip` assumes only $0<u$:
For $u\le v$, the band $[u,v]$ is the image of $[\log u,\log v]$
times the compact norm-one subgroup under `rationalIdeleClassLogSplit`.
When $v<u$ the band is empty. The Haar construction now uses the
$[1,e]$ specialization of this theorem rather than a separate proof.

`Masullo.rationalAdeleBoxSum_theta_log_bound` in
[RationalAdeleThetaTails.lean](../../Proofs/Theorems/RationalAdeleThetaTails.lean)
proves, for fixed $f$ in the finite translated rational box span with
$f(0)=\widehat f(0)=0$ and every $m\in\mathbb N$, that one $K>0$ satisfies

$$
|\theta_f(d)|\le K\exp(-m|\log|d||)
$$

for **every** rational idele class $d$. In the original fixed-test proof, the vanishing assumptions remove
the corrections in the small-norm estimate; neither tail changes its
exponent. Between the two thresholds, bound the continuous function
$|\theta_f(d)|/\exp(-m|\log|d||)$ on the compact norm band. Taking the
maximum of that bound and the two tail constants gives the result.

Independent Yah statement review in `dispatch-JtYJzWQ` checked both
interfaces against the accepted dependencies and the digest-matched
layout extraction. Theorem 2.2.3.4(3), (2.2.3.6), p. 83, gives the
two-tail version. The all-class extension follows the middle-range
strategy of (5), pp. 85–86, for one test only. In the extraction,
(2.2.3.14) bounds the *unweighted* theta on the band; that bound must
be rescaled by the maximum of the reciprocal decay weight before
taking the maximum with the tail constants. The Lean proof bounds the
weighted quantity directly. This is not a visual reading or a proof
of the LF bounded-family assertion. The fixed-test theorem now specializes
[the stronger uniform theorem](#checked-uniform-tails-for-fixed-finite-box-families),
which eliminates the middle band by moving both thresholds to one.
Compactness of norm bands remains an independent result.

Validation endpoints: `isCompact_rationalIdeleClass_normStrip` and
`rationalAdeleBoxSum_theta_log_bound`. Use `lake --wfail build Proofs`,
`leanchecker` on both linked modules and `Lemmas.RationalIdeleWindowMeasure`,
and `#print axioms` on both endpoints.

## Checked uniform tails for fixed finite box families

[The uniform tail theorem](../../Proofs/Theorems/RationalAdeleThetaTails.lean)
fixes finitely many coefficients, adelic centers, and idelic scales.
For each active box, its real Schwartz factor ranges over a specified
complex von Neumann bounded set. `rationalAdeleBoxSum_uniform_theta_tails`
chooses one $K>0$ for each order $m$, **before** choosing the real factors.
For every resulting box sum $f$ and rational idele class $d$, it gives

$$
\begin{aligned}
|\theta_f(d)| &\le K |d|^{-m} && (|d|\ge 1),\\
|\theta_f(d)-|d|^{-1}\widehat f(0)+f(0)| &\le K |d|^m && (|d|\le 1).
\end{aligned}
$$

`rationalAdeleBoxSum_uniform_theta_log_bound` gives the global
$K\exp(-m|\log|d||)$ bound, uniformly on the subfamily for which both
zero modes of the **sum** vanish. Neither statement requires each box
separately to have vanishing zero modes. Both cover order zero and norm
one. The estimates implement (2.2.3.4)–(2.2.3.6) and the threshold in
Theorem 2.2.3.4(4)–(5), pp. 83–86, on the stated family only.

[The absolute spatial and Fourier estimates](../../Proofs/Lemmas/RationalAdeleBoxTail.lean)
use the same normalization and denominator clearing as the fixed-test
proof. For the normalized real argument $y=tn-x$, with $n\ne0$ and
$t=|d|/(|g|D)$, use $t|n|\le(1+|x|)\max(1,|y|)$ rather than requiring
$t$ to dominate the translation. Orders $(0,0)$ and $(m+2,0)$ bound
$\max(1,|y|)^{m+2}|b(y)|$ on the given bounded set. Since $|d|,|n|\ge1$,
the resulting sample bound is at most a fixed multiple of
$|d|^{-m}|n|^{-2}$. This argument includes samples at $y=0$ and avoids
an unweighted middle-band estimate. The continuous linear real Fourier
transform preserves each bounded factor set; the centered dual-box
norm envelope and order $m+1$ give the corrected small-norm estimate.
Neither the adelic Fourier topology nor the LF bounded-set theorem is
used.

Independent Yah statement review (`statement-review`, agent `UJYUrAc`)
checked the normalization, exponent loss, both zero-mode signs, and
quantifier order at base `19b12d5d1c9b09a9e6f39deeca903528ff49557e`.
The SHA-256-matched layout extraction of pp. 82–86 is provisional, not
a rendered-page reading. The corrected difference is (2.2.3.7), p. 83.
The bound uses the real component of the finite-unit representative,
not the real component of an arbitrary lift as a literal reading of
(2.2.2.3) could suggest. The separate bornology step on p. 84 cites
Schaefer II §6.5 for the full tensor space, beyond the finite-adelic
bounded-set result of Proposition C.2.5.1(4). That external citation
was not verified here.

Validation endpoints: `rationalAdeleBoxSum_uniform_theta_tails`,
`rationalAdeleBoxSum_uniform_theta_log_bound`,
`rationalAdeleBoxSum_uniform_absolute_theta_tail`, and
`rationalAdeleBoxSum_uniform_absolute_fourier_theta_tail`. Use
`lake --wfail build Proofs`, `leanchecker` on both linked modules, and
`#print axioms` on the four endpoints and the fixed-test specializations.

## Checked rational finite quotient stage in box coordinates

In the digest-matched layout extraction of the proof of Proposition
2.1.3.2, pp. 69–70, the finite-dimensional stages are functions on
$K/H$ for compact open subgroups $H\subset K$ of the finite adeles.
They extend by zero outside $K$ and are constant on $H$-cosets inside
$K$. This extraction is not a visual reading. The topology and
bornology of the resulting inductive limit are separate from the
finite-stage coordinate calculation. The extraction labels the statement
“Lemma” on p. 68 and the proof “Proposition” on p. 69. The explicit
$M^2$ representatives below are our rational specialization, not
a formula attributed to the manuscript.

[The rational box stage](../../Proofs/Props/RationalAdeleBoxStage.lean)
takes $H=M\widehat{\mathbb Z}$ and $K=M^{-1}\widehat{\mathbb Z}$ for a
positive integer $M$. The Lean sets are cylinders in the full adeles,
with unrestricted real coordinate. The cell over $j/M+H$ is defined
by $x/M-j/M^2$ having integral finite coordinates.
`rationalAdeleStageCell_subset_support` puts each cell in the support
cylinder, and `mem_rationalAdeleStageSupport_iff_existsUnique_cell`
gives exactly one cell for each point there, indexed by $0\le j<M^2$.
[The residue proof](../../Proofs/Lemmas/RationalAdeleResidues.lean)
clears the finite coordinates of $z=x/M$ by a diagonal rational $q$.
Then $M^2q$ is an integral diagonal, hence an integer. Euclidean
reduction modulo $M^2$ gives the representative; for uniqueness, the
difference of two representatives divided by $M^2$ must be an integer.

`rationalAdeleBox_stageCell` uses the finite parts of
$j/M$ and $M$ as the center and dilation, with real coordinates zero
and one. For every real Schwartz profile, the resulting box is that
profile times the cell indicator. `exists_rationalAdeleBoxSum_stage_coordinates`
uses all $M^2$ boxes with coefficient one and reconstructs the
arbitrary tuple of profiles on their cells, extending by zero off the
support cylinder. The geometry is chosen before the profiles, as
required by the checked uniform tails. This is an algebraic
realization for one prescribed stage, not a topological identification
of the rational adelic Schwartz–Bruhat space. A stage identification
with the product of real Schwartz spaces also needs the converse:
Extract each profile by restriction to one representative, prove the
slices are Schwartz in the intended test class, and use invariance to
recover the original function.

Independent Yah statement review (`stage-review`, agent `uExkgFZ`)
at base `97e4b2091a1661a0b3f54f559428aeeaadb33b0c` checked the
$M^2$ partition, including $M=1$, the mixed real/finite parameters,
the quantifier order in the assembly, and the distinction from an LF
identification. The new residue lemmas are checked in this change,
not assumed from the base.

Validation endpoints: The four declarations above and the three
`rationalAdele_residue_*` lemmas. Use `lake --wfail build Proofs`,
`leanchecker` on `Lemmas.RationalAdeleResidues` and
`Props.RationalAdeleBoxStage`, and `#check` and `#print axioms` on all
seven declarations.

## Checked cofinality of the rational box stages

In the digest-matched layout extraction of Proposition 2.1.3.2's
proof, pp. 69–70, the transition extends support and shrinks the
subgroup of translations fixing the test. Thus a new pair dominates
$(H,K)$ when $H_{\rm new}\subset H\subset K\subset K_{\rm new}$.
The use of rational integer dilations is a project specialization,
not a formula attributed to the manuscript. This is a provisional
text reading, not rendered-page verification.

`Masullo.exists_rationalAdeleBoxStage_cofinal` in
[RationalAdeleBoxStage.lean](../../Proofs/Props/RationalAdeleBoxStage.lean)
proves there is one $M>0$ for which $M\widehat{\mathbb Z}\subset H$
and $K\subset M^{-1}\widehat{\mathbb Z}$, assuming only that $H$
is an open additive subgroup and $K$ is a compact additive subgroup
of the rational finite adeles. Inserting $H\subset K$ gives the
required cofinality. `rationalAdeleBoxStage_isCompact_isOpen` proves
that both scaled stages are compact and open, and that the invariance
stage lies in the support stage. They are the image and preimage of
an additive subgroup under the same additive homeomorphism, namely
multiplication by $M$. `rationalAdeleStageSupport_eq_preimage` ties
the finite support subgroup to the earlier box coordinates: Its
inverse image under the finite projection is the support cylinder
with no condition on the real coordinate.

The [two bounds](../../Proofs/Lemmas/RationalAdeleBoxCofinality.lean)
are independent. Compact $K$ is covered by the open sets where a
positive integer clears denominators; take a finite subcover and
multiply its levels. This reuses the denominator-clearing lemma
already proved in the box-tail argument, now shared with that argument.
For $H$, pull the zero neighborhood back to the product of the local
integer rings and refine it by an open box with finitely many
restricted coordinates. At each restricted place, multiplication by
a sufficiently large power of the prime maps the whole local integer
ring into the coordinate neighborhood. Their product $N$ works
simultaneously: Additional integer factors preserve integrality.
Taking $M=ND$ with $D$ the common denominator of $K$ combines the
bounds without identifying the support and invariance subgroups.

Independent Yah review (`cofinality-review`, agent `NpmwsOR`) matched
the inclusion directions and the distinction between finite stages
and full-adele cylinders, using pp. 69–70 and 84–85 of the pinned
text. Validation: `lake --wfail build Proofs`, `leanchecker` on
`Lemmas.RationalIntegralAdeles`, `Lemmas.RationalAdeleBoxCofinality`,
`Props.RationalAdeleBoxStage`, and `Lemmas.RationalAdeleBoxTail`, and
`#check` and `#print axioms` on the cofinality and stage endpoints
and their new public dependencies.

## Checked sampling equivalence for the rational Schwartz stage

For $M>0$ the [stage equivalence](../../Proofs/Props/RationalAdeleStageCoordinates.lean)
identifies the submodule of full-adele functions vanishing off the
cylinder over $K_M=M^{-1}\widehat{\mathbb Z}$, invariant under the
finite translations $H_M=M\widehat{\mathbb Z}$, and Schwartz on
each fixed-finite real slice, with $\mathcal S(\mathbb R,\mathbb C)^{M^2}$.
`rationalAdeleStageCoordinates_apply` samples the real line above
$(j/M)_f$, with no shift of the real coordinate.
`exists_rationalAdeleStageCoordinates_symm_eq_boxSum` recovers the
original function everywhere by fixed boxes with coefficient one.
The centers and scales are chosen once per level, not per profile.

The [sampling lemmas](../../Proofs/Lemmas/RationalAdeleStageSampling.lean)
identify the cell over $j$ with the finite coset $(j/M)_f+H_M$.
At fixed real coordinate, a point in that cell differs from the
sample point by a finite-only translation. This gives injectivity by
invariance and zero extension. For surjectivity, box assembly has the
prescribed Schwartz slice in each cell, zero slice off the cylinder,
and the same invariance, so sampling returns the original tuple.
The equivalence does not use a topology on the stage submodule.

Independent Yah statement review (`coordinates-review`, agent
`gviZQhZ`) compared the actual stage and the hypotheses of the
bounded-family step with the digest-matched text extraction at
pp. 68–70 and 84–85. The equivalence specializes the quotient-stage
construction on pp. 69–70 and uses the translated indicators of
Example 2.1.3.1, not the [centered-only wording](#checked-poisson-summation-on-the-translated-generator-span)
in the extracted 2.1.3.2(3). The level, labels, and sampling maps
are project choices. No rendered-page review was used.

Validation endpoints: `rationalAdeleSchwartzStage`,
`mem_rationalAdeleStageCell_iff`, `rationalAdeleStageCoordinates`,
`rationalAdeleStageCoordinates_apply`, and
`exists_rationalAdeleStageCoordinates_symm_eq_boxSum`. Audit the
public declarations in the two linked modules with `#check` and
`#print axioms`; run `lake --wfail build Proofs` and `leanchecker`
on both modules.

## Checked split inclusions of the rational Schwartz stages

For positive levels $M\mid N$, [RationalAdeleStageTransition.lean](../../Proofs/Props/RationalAdeleStageTransition.lean)
proves the inclusion of Schwartz stages as submodules of functions on
full adeles. Support grows from $M^{-1}\widehat{\mathbb Z}$ to
$N^{-1}\widehat{\mathbb Z}$ and the required group of finite
translations shrinks from $M\widehat{\mathbb Z}$ to
$N\widehat{\mathbb Z}$. `rationalAdeleStageTransition` expresses
that same-function inclusion in the product Schwartz coordinates;
`rationalAdeleStageTransition_assemble` checks the agreement after
assembly on all adeles.

A fine representative outside coarse support gives the zero component.
If the representative belongs to coarse cell $j$, the component is
the projection onto the entire Schwartz profile $b_j$. These are
checked geometric tests, not a numerical formula for coarse indices.
Every fine subcell of a coarse cell copies its profile, not just the
selected old line. Writing $d=N/M$, the continuous linear
`rationalAdeleStageRetract` selects the fine component $dj$ for each
old index $j$; its finite coordinate is exactly the old $j/M$. The
checked left-inverse identity makes the transition a topological
embedding for the product Schwartz topologies, independently of any
topology on a union of stages.

Independent Yah statement review (`stage-inclusion-review`, agent
`DTWDAxN`) checked the inclusion directions, the subcell repetition,
and the selected representative against the accepted stage definitions
and the digest-matched layout extraction. The proof of Proposition
2.1.3.2, pp. 69–70 (especially (2.1.3.3)), splits an injection on finite
adelic factors by a continuous linear section on the tensor stages.
The maps here specialize that splitting to rational box coordinates;
the representative choices and coordinate formulas are ours. The
review used extracted text, not rendered-page verification. Validation
targets: The full `lake --wfail build Proofs`, `leanchecker` on the
transition, coordinates, and sampling modules, and `#check` and
`#print axioms` for their new public endpoints.

## Checked factorial-stage residual maps

Set $M_n=(n+1)!$. [The algebraic union](../../Proofs/Lemmas/RationalAdeleStageUnion.lean)
consists exactly of the functions belonging to some factorial stage and
contains every positive integer stage. `rationalAdeleFactorialStageRead`
defines $E_n$ on this union by reading every level-$M_n$ representative
line. The Schwartz slice condition ensures that the profiles are defined
regardless of whether the function belongs to the sampled stage.
On any fixed source stage $m$, reading at $n$ is continuous: Transition
from $m$ to $k=\max(m,n)$ and select the old lines from $n$ in stage $k$.
The [transition formulas](../../Proofs/Props/RationalAdeleStageTransition.lean)
check equality of those finite representatives, not just cell membership.

[The residual proposition](../../Proofs/Props/RationalAdeleStageResidual.lean)
uses $R_n=E_{n+1}-T_n E_n$, where $T_n$ is the adjacent same-function
transition. It proves continuity after assembly from every fixed stage,
vanishing on stage $n$, and detection of stage $n$ **within stage $n+1$**.
For an arbitrary element of the union, `mem_rationalAdeleSchwartzStage_iff_residual`
proves membership in stage $m$ iff **all** residuals with $n\ge m$ vanish.
For the converse, descend from any stage containing the given function.
No topology on the union is used in these statements.

Independent Yah statement review (`lf-residual-review`, agent `PidjlVJ`)
checked both stage restrictions and the source comparison against
SHA-256-matched layout extraction, not rendered pages. The factorial
filtration and residuals are project constructions. The underlying split
tensor inclusions appear in the proof of Proposition 2.1.3.2,
(2.1.3.3), pp. 69–70. The residuals target the bounded-family premise
in the proof of Theorem 2.2.3.4(4), pp. 84–85. The validation scope is
`lake --wfail build Proofs`, `leanchecker` for the three linked modules,
and type and axiom checks for the new public declarations.

## Checked rational Schwartz inductive topology and bounded families

Objective: Prove the common-stage bounded-family input for the rational
model of Theorem 2.2.3.4(4), pp. 84–85, and use it to reach uniform theta
estimates on bounded rational adelic Schwartz families.

[RationalAdeleSchwartzLF.lean](../../Proofs/Props/RationalAdeleSchwartzLF.lean)
equips the algebraic stage union with the topology of **all** complex
seminorms whose restrictions to the product Schwartz stages are continuous.
`rationalAdeleLF_continuous_iff` is the stagewise continuity criterion for
complex-linear maps into seminorm-defined spaces. In particular,
`rationalAdeleLF_finest` gives the finest such topology making the assemblies
continuous. The readings separate points by reading in a stage containing
both inputs, so the space is Hausdorff. Each assembly has the corresponding
continuous reading as left inverse and embeds its stage as a closed subspace
with the original topology. The topology is not inherited from the ambient
function type.

[RationalAdeleSchwartzBounded.lean](../../Proofs/Props/RationalAdeleSchwartzBounded.lean)
proves `rationalAdeleLF_bounded_iff`: A set is von Neumann bounded over
$\mathbb C$ iff it is the image of a bounded product-Schwartz family under
a single factorial-stage assembly. If a set escapes every stage, there are
unboundedly many indices $n$ for which some member has nonzero residual
$R_n$. For each such index choose a detecting coordinate and pull back
its Schwartz sup seminorm `(0, 0)`, scaled to have value $n+1$ on that
member. Use zero at inactive indices. The
[pointwise finite seminorm sum](../../Proofs/Lemmas/EventualZeroSeminormSum.lean)
restricts on stage $m$ to the continuous finite sum over $n<m$, but is
unbounded on the set. Containment in a common stage then gives bounded
coordinates by continuity of the reading. The converse uses continuity of
assembly.

Independent Yah statement review checked the rational scope and the needed
bounded-family interface against the digest-matched text extraction of
(2.1.3.3), pp. 69–70, and Theorem 2.2.3.4(4), pp. 84–85. In the extraction,
C.2.5.1(4) is used for the finite-adelic factor, and C.2.3.13(2),
(C.2.3.26), pp. 682–683, is a tensor topology comparison, not the full
bounded-hull step. That step on p. 84 cites [Schaefer, Ch. II, §6, 6.5,
p. 59]; p. 85 uses boundedness of the real Schwartz set $B_\infty$.
The residual proof is a direct project argument. It neither verifies the
Schaefer reference nor identifies the rational LF model with the manuscript's
topological tensor product. Source readings are extraction-based, not visual.

<a id="next-orbit-step-uniform-theta-estimates-for-rational-lf-bounded-families"></a>

## Checked uniform theta estimates for rational LF-bounded families

In [RationalAdeleLFThetaTails.lean](../../Proofs/Theorems/RationalAdeleLFThetaTails.lean),
`rationalAdeleLF_uniform_theta_tails` proves the rational LF-model versions
of Theorem 2.2.3.4(1)–(2), (4)–(5), (2.2.3.4)–(2.2.3.5), pp. 82–86.
For every bounded family $B$ and integer $m\ge0$, one $K>0$ works for
all $f\in B$ and all rational idele classes $d$ of norm $r$:

$$
|\theta_f(d)|\le K/r^m\quad(r\ge1),\qquad
|\theta_f(d)-r^{-1}\widehat f(0)+f(0)|\le Kr^m\quad(r\le1).
$$

`rationalAdeleLF_uniform_theta_log_bound` gives the version of (3)–(5),
(2.2.3.6): If both zero modes of a member vanish, its theta function is
bounded by $K e^{-m|\log r|}$ on the whole class group. The constant is
still chosen before the member and class. Taking the maximum of the two
constants makes one work for all three inequalities. Both tails include
norm one, and neither requires vanishing of a zero mode.

`rationalAdeleLF_bounded_iff` puts $B$ in one bounded tuple family at a
factorial level. The inverse stage coordinates fix the box centers and
scales for the whole tuple family. Continuous linear projection makes
its coordinate images bounded. The existing box estimates therefore
apply to each assembled function, with the equality holding on all
adeles. The Fourier-side bound comes from the fixed-box argument, not
from assuming the as-yet unproved LF Fourier automorphism. There is no
identification with the manuscript tensor topology or extension to
other number fields. The source locators refer to the digest-matched
text extraction, not a rendered-page reading.

## Checked real dilation generator on the rational LF space

[RationalAdeleLFDilationDeriv.lean](../../Proofs/Theorems/RationalAdeleLFDilationDeriv.lean)
proves the positive real norm-section case of Lemma 2.2.4.2,
(2.2.4.2)–(2.2.4.5), pp. 87–88, in the rational factorial-stage LF
model. `Masullo.rationalAdeleLFDilationDeriv` is a continuous
complex-linear endomorphism. Its `_apply` theorem gives
$Df(u,z)=u\,\partial_u f(u,z)$ for every adele, including $u=0$.
Its `_assembly` theorem applies the real Euler operator coordinatewise
on each stage without changing any finite cell. The two `HasDerivAt`
endpoints `hasDerivAt_rationalAdeleLF_dilate` and
`hasDerivAt_rationalAdeleLF_logDilation` identify this same value with
the derivative at scale $1$ and at log scale $0$, respectively. The
all-real scale formula is an extension of the positive-scale formula
near $1$; the log theorem uses the actual idelic section.

The [stagewise proof](../../Proofs/Lemmas/RationalAdeleDilationDeriv.lean)
uses `SchwartzMap.derivCLM` followed by `SchwartzMap.smulLeftCLM`
with `Complex.hasTemperateGrowth_ofReal`. For an arbitrary LF element,
stage membership represents each real slice by a Schwartz function,
so the formula uses a genuine pointwise derivative, not just a totalized
`deriv`. Derivative uniqueness makes the chosen stage immaterial;
`rationalAdeleLF_continuous_iff` gives continuity of the resulting map.

Independent Yah statement review checked sign, parameters, and scope
against the digest-matched extraction of pp. 87–88. No rendered page
was independently inspected. This result does not assert differentiability
of the orbit as an LF-valued map, identify the manuscript topology,
prove its tensor identity (2.2.4.6), or treat arbitrary one-parameter
subgroups.

<a id="next-orbit-step-differentiate-rational-class-theta"></a>

### Checked differentiation of rational class theta

[RationalAdeleClassThetaDerivative.lean](../../Proofs/Theorems/RationalAdeleClassThetaDerivative.lean)
proves the positive real norm-section case of Lemma 2.2.4.3,
(2.2.4.7), pp. 88–91. For every rational Schwartz LF test $f$, every
rational idele class $d$, and every real log scale $s$,
`Masullo.hasDerivAt_rationalAdeleClassTheta_logDilation` gives

$$
\frac{d}{ds}\theta_f(\tau(s)d)=\theta_{Df}(\tau(s)d),
$$

with $\tau$ the log-norm section on classes. The derivative at zero is
continuous in $d$ by `Masullo.continuous_rationalAdeleClassTheta_LF`
applied to $Df$. Neither zero mode is required to vanish.

The [series proof](../../Proofs/Lemmas/RationalAdeleThetaDerivative.lean)
fixes a lift $k$ of $d$. The ideles $\tau(t)k$ for $|t-s|\le1$ form a
compact set (here using the section upstairs). The existing compact box
majorant for $Df$ bounds all the differentiated nonzero rational samples
on this set. A separate majorant for $f$ at the base point gives absolute
summability there. This is enough for `hasDerivAt_tsum_of_isPreconnected`;
there is no need to invoke the printed fractional-ideal bound (2.2.4.8)
for unrestricted representatives or take a limit in the LF space.

Independent Yah statement review checked the sign, parameters, and no-moment
scope against the digest-matched layout extraction. At a fixed lift the
compactness used here follows from the compact log interval alone; the
proof does not claim one bound over all representatives. The result does
not identify the manuscript's tensor topology or assert compact-uniform
convergence of difference quotients on idele classes.

<a id="next-orbit-step-the-fourier-zero-mode-of-the-generator"></a>

### Checked zero modes of the rational real dilation generator

[RationalAdeleLFDilationZeroModes.lean](../../Proofs/Theorems/RationalAdeleLFDilationZeroModes.lean)
checks the rational positive real section case of Lemma 2.2.4.5(1).
For every rational Schwartz LF test $f$, with no moment hypotheses,
`Masullo.rationalAdeleLFDilationDeriv_at_zero` and
`Masullo.rationalAdeleFourier_LFDilationDeriv_at_zero` give

$$
(Df)(0)=0,\qquad \widehat{Df}(0)=-\widehat f(0).
$$

`Masullo.rationalAdeleLFDilationDeriv_preserves_zero_modes` then gives
preservation of the intersection of the two kernels in (2.2.4.23).
The Fourier statements use additive adelic Haar, with no quotient
measurability hypothesis. They do not construct the quotient isomorphism
in (2.2.4.25).

The spatial identity follows from the Euler factor at zero. For the
Fourier identity, put $f$ and $Df$ in the same factorial stage and use
the same finite boxes for both. Those stage boxes have zero real centers
and unit real scales. At frequency zero each box transforms to its
idele Jacobian times the integral of its profile. This Jacobian is
unchanged by replacing the profile $b$ by $u b'(u)$.
Mathlib's `integral_mul_deriv_eq_deriv_mul_of_integrable` gives
$\int u b'(u)\,du=-\int b(u)\,du$ because $b$, $u b$, and $u b'$
are integrable Schwartz functions. No adelic limit is interchanged
with the integral.

Independent Yah statement review checked the sign, stage geometry, and
scope against the digest-matched extraction, pp. 91–95. The p. 92 proof
appears to conclude that $\widehat{\partial_\gamma f}(0)=0$ for general
$f$ because $\gamma(t)^{-1}0=0$. That does not remove the norm factor in
(2.2.4.29). For the positive real norm section, `ideleNorm_logSection`
with $s=\log t$ gives $|\gamma(t)|=t$, and the quotient at zero for
$t\ne1$ is $-t^{-1}\widehat f(0)$. Its limit agrees with (2.2.4.27)
and the closing sentence on p. 95, not with the extracted intermediate
zero claim. The sign can also be tested on an unramified tensor of a
nonnegative smooth bump with positive integral. This is an extracted,
not visually verified, reading.

## Checked pointwise Fourier covariance at every frequency

`Masullo.hasDerivAt_rationalAdeleFourier_LFDilation` in
[RationalAdeleLFFourierDilation.lean](../../Proofs/Theorems/RationalAdeleLFFourierDilation.lean)
proves, for every rational Schwartz LF test $f$ and every adelic
frequency $y$, that

$$
\left.\frac{d}{ds}\left(e^{-s}\widehat f(\tau(-s)y)\right)\right|_{s=0}
=\widehat{Df}(y).
$$

Here $\tau$ is the upstairs log-norm section, $D$ is the checked real
Euler generator, and Fourier is the integral against the conjugated
rational pairing. No moment condition is needed. At $y=0$ this gives
$-\widehat f(0)$, in agreement with the separate zero-mode identity.
Independent Yah statement review matched this to (2.2.4.29), pp. 92–95,
for $\gamma(t)=\tau(\log t)$: $|\gamma(t)|=t$ and the change of parameter
has derivative one at the base point. This is a provisional source
reading of the digest-matched extraction, not a rendered-page check.

[RationalAdeleFourierEuler.lean](../../Proofs/Lemmas/RationalAdeleFourierEuler.lean)
derives $\mathcal F(u b')=-\mathcal F b-\xi(\mathcal F b)'$ from
$(u b)'=b+u b'$ and Mathlib's two Schwartz identities for Fourier
and the directional derivative in direction $1$. In the common
factorial stage for $f$ and $Df$, the box assembly has zero real
centers and unit real scales, now exposed in the stage assembly
lemmas. Consequently the translated-box transform has constant
finite support and character along $\tau(-s)y$, leaving just the
weighted inverse dilation of each real Schwartz profile. The proof
sums a finite family of derivatives rather than differentiating an
adelic integral or extending from a sequentially dense subclass.

## Checked Fourier continuity on each rational Schwartz stage

The proof on p. 95 invokes a Fourier automorphism of $\mathcal S(A_F)$
with its Schwartz–Bruhat topology. The corresponding upstream argument,
Lemma D.1.6.19(2), pp. 773–775, reduces the transform to the structural
levels $(k,\Gamma)$ and their dual levels $(\Gamma^\perp,k^\perp)$.
At p. 774 the text explicitly notes that its cited Lemma D.1.5.2(3)
assumes $\widehat f\in L^1$, not yet available at this step; the required
support and invariance follow instead by translation and the integral
for $f\in L^1$. The rational box transform already computes the integral
without assuming Fourier-side integrability. Part (1) of D.1.6.19 is
about invariant differential operators, not the real Euler operator;
it does not itself supply the dilation identity.

In [RationalAdeleStageFourier.lean](../../Proofs/Theorems/RationalAdeleStageFourier.lean),
`Masullo.rationalAdeleStageFourier M` is a continuous complex-linear map
on the $M^2$ real Schwartz profiles. For $M>0$ it computes

$$
(T_M b)_k = \frac1M \sum_{j=0}^{M^2-1}
  \overline{\chi_f((j/M)(k/M))}\,\mathcal F_{\mathbb R} b_j,
$$

where $\chi_f$ is the finite factor of the actual rational additive
character. `Masullo.rationalAdeleStageCoordinates_symm_fourier` shows
that assembly of the output is exactly the normalized adelic Fourier
integral of the assembled input at every frequency.
`Masullo.rationalAdeleLFAssembly_fourier` gives the same identity for
each factorial-stage inclusion into the rational LF space.

The scaled unramified factor cuts out $M^{-1}\widehat{\mathbb Z}$ on
the frequency side. The phase is constant under changing $k/M$ by
$Mz$ with $z\in\widehat{\mathbb Z}$, since the pairing changes by
$jz\in\widehat{\mathbb Z}$. The Jacobian is exactly $1/M$: Multiply
the box scale $(1,M)$ by the diagonal $M^{-1}$ and use the product
formula. This leaves real scale $M^{-1}$ and finite scale one. The
CLM is a finite matrix composed with `FourierTransform.fourierCLM` on
real Schwartz profiles. The proof uses no Fourier-side $L^1$ premise. In the cell-box
identification, the normalization equation is proved in the finite
adele ring and then transported to integral membership. This avoids a
kernel replay stall encountered when the same calculation rewrote a
projected full-adele expression under the integral-membership predicate.
The result proves forward continuity on levels, not the manuscript's full
Fourier automorphism or an identification of LF topologies. The
source comparison above is based on the digest-matched extraction.

### Checked Taylor remainder on real Schwartz profiles

Remark 2.2.4.6, p. 92, asks for the limit in $L_\beta$: Uniform on
bounded input families in the **target Schwartz topology**. In the
pinned PDF's layout extraction, the bound following (2.2.4.42), p. 94,
appears to omit the norm-weight term from (2.2.4.39). At zero frequency
the full rational scale kernel quotient is $-1/t$, not zero. A bound of
$4+16\pi|u_\infty y_\infty|$ for $t\in[1/2,3/2]$ suffices for
fixed-frequency domination with the project's rational kernel, not for
convergence in Schwartz seminorms. Equicontinuity alone does not supply
that convergence. This reading is provisional, not a rendered-page check.

[SchwartzWeightedDilation.lean](../../Proofs/Lemmas/SchwartzWeightedDilation.lean)
implements a repair on the real profiles. Let $U_s b(x)=e^{-s}b(e^{-s}x)$
and $Gb(x)=-b(x)-xb'(x)$. Both operators are continuous complex-linear
maps on $\mathcal S(\mathbb R,\mathbb C)$ for each fixed $s$.
`Masullo.seminorm_weightedInverseDilation_difference_quotient` proves, for
all $a,d\in\mathbb N$, every profile $b$, and $0<|s|\le1$,

$$
p_{a,d}\big((U_s b-b)/s-Gb\big)
\le e^{|a-d-1|}|s|\,p_{a,d}(G^2 b).
$$

After $d$ spatial derivatives, one log-scale derivative replaces $b$
by $Gb$, and two replace it by $G^2b$. Multiplying by $|x|^a$ and
rescaling the spatial argument gives the factor $e^{(a-d-1)s}$.
Two scalar mean value estimates give the quadratic remainder before
division by $s$. This uses neither integration in Schwartz space nor
moment assumptions. Independent Yah statement review checked the
operator weight, sign, real casts of the indices, and both signs of
$s$ against this calculation and the digest-matched source extraction.

## Checked bounded-set Fourier dilation differentiation

[RationalAdeleLFFourierUniformDilation.lean](../../Proofs/Theorems/RationalAdeleLFFourierUniformDilation.lean)
proves `Masullo.tendstoUniformlyOn_rationalAdeleLFFourier_dilation` and
`Masullo.tendstoUniformlyOn_rationalAdeleLFFourier_logDilation`. For every
complex von Neumann bounded family in the rational LF space, the weighted
inverse Fourier dilation quotient tends uniformly to $\widehat{Df}$ in the
additive uniformity of that LF topology. In scale $t$ near one the weight
and real frequency multiplier are both $t^{-1}$, and the denominator is
$t-1$. In log scale the denominator is $s$. Neither endpoint needs moment
vanishing, inverse Fourier continuity, or an inversion theorem.

The [stage operators](../../Proofs/Lemmas/RationalAdeleLFStageOperators.lean)
assemble the normalized forward Fourier integral and the weighted inverse
log dilation as global continuous linear maps preserving each stage. The
[profile argument](../../Proofs/Lemmas/SchwartzUniformDilation.lean) bounds
the seminorms on the images under $G$ and $G^2$, with $G=-1-x\partial_x$.
For $q=\log t/(t-1)$, the scale error is $q$ times the log error plus
$(q-1)Gb$; the log slope limit is one. Common-stage boundedness reduces
the adelic claim to finitely many such profile limits, and continuous
linear assembly transports the limit. Pointwise derivative uniqueness
identifies it via $\widehat{Df}=-\widehat f-D\widehat f$.

Independent Yah statement review (`statement-review`, base
`ab734c259dd2dcced1be79605ebeb47d73261262`) checked the two filters, both
signs, the Haar weight, the fixed-stage argument, and the LF uniformity
against the pinned text extraction of pp. 91–95. Remark 2.2.4.6 requests
bounded-set convergence in the target Schwartz topology, but its compact
image argument needs continuity of the extended quotient orbit in that
topology, not just the pointwise derivative from (2.2.4.28)–(2.2.4.29).
Even equicontinuity would not by itself give uniform convergence on
bounded sets. Lemma D.1.6.19(2), pp. 773–775, gives a continuous Fourier
isomorphism between Schwartz spaces, not continuity of the dilation
quotient at the puncture. The seminorm remainder is our repair. The
phase-only bound following (2.2.4.42), p. 94, also misses the contribution
from the reciprocal norm: At frequency zero the scale quotient is
$-t^{-1}\widehat f(0)$, not zero. These manuscript observations are
provisional text readings, not rendered-page verification. The theorem
does not identify the two Schwartz topologies, validate the explicit
phase in (2.2.4.30), or treat general number fields.

<a name="next-fourier-step-normalize-the-finite-matrix-for-inversion"></a>

## Checked rational LF Fourier inversion

[RationalAdeleLFFourierInversion.lean](../../Proofs/Theorems/RationalAdeleLFFourierInversion.lean)
constructs `Masullo.rationalAdeleLFFourierEquiv`, a complex continuous
linear self-equivalence of `RationalAdeleSchwartzLF`, with the Borel
measurable-space assumptions on the full rational adeles. Its forward map
is exactly `rationalAdeleLFFourier` and agrees pointwise with the normalized
adelic integral at every adelic frequency. Its inverse commutes with
assembly at each factorial level and acts there by the explicit stage
inverse.

For positive $M$, the [cyclic stage calculation](../../Proofs/Lemmas/RationalAdeleCyclicFourier.lean)
identifies the phase at cells $j,k$ as $e^{2\pi i jk/M^2}$. The finite
character on the rational diagonal $jk/M^2$ has the negative sign
because the full character is trivial there and the real component has
the positive sign. Conjugating gives the positive cyclic phase. Under
`ZMod.finEquiv`, the finite operator is $M$ times Mathlib's inverse DFT
at modulus $M^2$, hence has coefficients of magnitude $1/M$. Its inverse
is $M^{-1}$ times the forward DFT, followed by inverse real Schwartz
Fourier on each profile. Both cyclic operators are continuous on the
Schwartz-valued product by finite sums of continuous evaluations, not
because the space of profiles is finite-dimensional. Global injectivity
uses a common factorial stage for two inputs. Stagewise inversion supplies
surjectivity and gives the restrictions of the global inverse, so the LF
continuity criterion applies to the inverse as well.

This realizes the structural-pair reduction of Lemma D.1.6.19(2), pp.
773–775, in the rational model. Footnotes 5–6 leave the level scalar
unspecified; here the existing normalized Haar integral fixes it. On
p. 775 the proof cites D.1.1.2(5), p. 747, after obtaining integrability
of the input and transform. The cited inversion formula (D.1.1.11)
uses reflection for the double forward transform; its literal claim of
pointwise continuity of an arbitrary measurable representative cannot
follow from the two $L^1$ hypotheses (changing one point on $\mathbb R$
leaves the Fourier integral unchanged). Our continuous Schwartz inputs
and real-plus-cyclic equivalences do not require that assertion. These
are provisional text-extraction readings of the digest-pinned PDF, not
visual review. The result does not identify the model topology with the
manuscript tensor topology, parametrize all dual characters, or prove
Plancherel or D.1.6.19(3).

Independent Yah review (`inversion-endpoint-review`, base
`d8aec550372603be45ca566c91c47fd96b2870ff`) checked the stage phase,
normalization, forward-integral identification, inverse assembly, and
LF topology against the drafted statements and the pinned passage.

## Checked rational Schwartz Parseval for normalized Haar

The theorem
[`Masullo.rationalAdeleFourier_parseval`](../../Proofs/Theorems/RationalAdeleFourierParseval.lean)
proves, for every `RationalAdeleSchwartzLF` input $f$, that $|f|^2$ and
$|\widehat f|^2$ are integrable against `rationalAdeleAddHaar`, and that

$$
\int_{\mathbb A_{\mathbb Q}} |\widehat f(y)|^2\,d\mu_A(y)
= \int_{\mathbb A_{\mathbb Q}} |f(x)|^2\,d\mu_A(x).
$$

Here $\widehat f$ is the normalized Fourier integral evaluated at every
adelic frequency, not a chosen $L^2$ representative. No moment conditions
are used. At a positive stage $M$, the
[stage norm calculation](../../Proofs/Lemmas/RationalAdeleStageNorm.lean)
writes the squared norm integral as $M^{-1}\sum_j\int_{\mathbb R}|b_j|^2$.
Pointwise disjointness eliminates mixed terms. The integral finite cylinder
has a probability finite factor; the affine substitution has real scale
one and full modulus $1/M$, the **finite-factor** mass of one cell.
The [cyclic calculation](../../Proofs/Lemmas/RationalAdeleCyclicFourier.lean)
uses primitivity at the difference of two distinct residue indices, not
invertibility of that difference. It gives orthogonality in the positive
cyclic phase: The $M^2$ terms on the diagonal cancel the squared matrix
weight $1/M^2$. This includes $M=1$. Integrate that finite squared norm
identity in the real frequency and apply `SchwartzMap.integral_norm_sq_fourier`
to each profile. The assembled forward integral is the existing pointwise
stage transform; the proof does not need the inverse equivalence.

This is the Schwartz restriction of (D.1.1.9), Lemma D.1.1.2(4), p. 747,
in the rational frequency parameterization, using the unit-strip measure
of Example A.3.1.8, p. 558. The manuscript cites a general Plancherel
theorem and explains the global normalization via a fixed Gaussian tensor.
The Lean proof directly checks the squared norms on every rational stage.
It uses the project character's conjugated finite factors for diagonal
cancellation, not the literal positive local product in the provisional
extraction of Examples A.3.1.5–8. Independent Yah statement review
(`parseval-statement-review`, base `572ff46e4820e60927c9d9c3944aa055366cbc3b`)
checked the formulation, both occurrences of $1/M$, the character sign,
and the scope against the digest-matched layout extraction, not rendered
pages. This does not identify the full dual or its Haar measure, or prove
(D.1.1.10), the extension to all of $L^2$.

### Next Fourier step: L² approximation of compactly supported continuous tests

Toward (D.1.1.10), prove that every continuous compactly supported complex
function on the rational adeles can be approximated in normalized $L^2$
by assembled Schwartz stages. First approximate uniformly by sampling
along `rationalAdeleAt t (rationalAdeleStageRepresentative M j)` in each
cell, extending by zero outside the stage support. Choose the finite
support level by `exists_rationalFinite_support_bound`, then refine by
divisibility using `HasCompactSupport.uniformContinuous_of_continuous`
and `exists_rationalFinite_invariance_bound`. The sampled functions and
the original share a fixed compact real interval and a fixed finite
support cylinder, so uniform error there controls $L^2$ error. Then use
`SchwartzMap.denseRange_toLpCLM` on the finitely many real profiles and
the same cell norm calculation, generalized to square-integrable real
profiles for the differences. This step does not require identifying the
full dual or the manuscript tensor topology. Afterward, prove density of
these compactly supported tests in the actual adelic $L^2$ and use the
Schwartz inverse and Parseval to construct the surjective isometric extension.

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

## Checked strict integrability threshold for boundary jets

In [BoundaryLogJet.lean](../../Proofs/Props/BoundaryLogJet.lean),
`Masullo.memLp_boundaryLogJet_iff` proves that for $s\ge0$ and
$|\Re z|=\alpha$, including $\alpha=0$, the divided kernel
$k(x)=x^m e^{zx}/W(x)$ belongs to $L^2(dx)$ **if and only if**
$2m+1<s$. Here $W$ is the very same positive weight root as for
interior jets. The imaginary part does not enter the squared norm:

$$
|k(x)|^2=e^{2(\Re z\,x-\alpha|x|)}\frac{|x|^{2m}}{(1+x^2)^{s/2}}.
$$

The exponential factor is at most one everywhere and is exactly one
on the tail with the sign of $\Re z$ (both tails at width zero).
`Masullo.integrableOn_sobolevJetPolynomial_Ioi_iff` compares the
polynomial factor on $(1,\infty)$ to $x^{2m-s}$ above and to
$2^{-s/2}x^{2m-s}$ below, using $x^2\le1+x^2\le2x^2$. Mathlib's
`integrableOn_Ioi_rpow_iff` then gives the strict power test. Reflect
the negative tail and use continuity on the compact middle interval.
At equality the nondecaying tail has a divergent $1/|x|$ lower bound.
The criterion concerns the ambient rational log-line space, not an
identification with the adelic completion. The interior theorem is
unchanged.

The independent Yah statement review checked the pinned extraction of
(9.2.2.4), p. 412, and (10.2.2.3)–(10.2.2.5), pp. 445–446, for the
weight, bilinear pairing, positive exponent, and boundary indexing.
The provisional extraction of (10.2.2.5) uses $\lfloor(s-1)/2\rfloor+1$
as the boundary cap before taking the minimum with multiplicity.
Upstream, Corollary 9.2.2.5(2), (9.2.2.24), p. 414, repeats the
non-strict bracket cutoff for continuous boundary evaluations. Its
proof refers to the one-sided result via Proposition 9.2.2.4, whose
part (3) states the Mellin identification for even integer $s$ only.
Separately, the reciprocal norm (9.2.2.40), p. 417, used by Proposition
9.2.2.11 gives precisely the squared tail tested here on the symmetric
strip. That proposition assumes a nondegenerate interval; the Lean
calculation does not. For the analogous singleton cap (10.3.1.4),
p. 448, the text explicitly defines the bracket by $N\le x$, not
$N<x$. If the extracted cap includes $m$ when $s=2m+1$ and the
multiplicity exceeds $m$, it includes a kernel outside the reciprocal
weighted $L^2$ space. The $s=2$ cap is unaffected. These are readings
of the digest-matched text extraction, not rendered-page verification.

## Checked boundary pairings and annihilation of the theta closure

`Masullo.boundaryLogJet` and `Masullo.boundaryLogJet_toLp` in
[BoundaryLogJet.lean](../../Proofs/Props/BoundaryLogJet.lean) use the
strict threshold $2m+1<s$ and exactly the same log-Lebesgue $L^2(dx)$
coordinate $U=Wu$ as the interior jets. The $L^2$ class of the conjugate
of the divided kernel $k(x)=x^m e^{zx}/W(x)$ represents the continuous
complex-linear functional. Conjugation is only in the representing
vector: The value on $U$ is the absolutely convergent **bilinear**
integral $\int u(x)x^m e^{zx}\,dx$.

In [RationalThetaJetClosure.lean](../../Proofs/Theorems/RationalThetaJetClosure.lean),
`Masullo.rationalThetaWeightedLog_closure_subset_boundary_ker` proves
annihilation of the same weighted closure as in the interior theorem.
For $z=\rho-a$, the hypotheses are $0<\Re\rho<1$, $|\Re z|=\alpha$,
$m<\operatorname{ord}_\rho\zeta$, and $2m+1<s$. Width zero is allowed.
The once-twisted moment identity gives vanishing on every generator,
and continuity makes the kernel closed. The interior theorem retains
its statement and shares only the reciprocal-weight pairing proof.

The digest-matched layout extraction of (9.2.2.4), p. 412, and
(9.2.2.40), p. 417, gives the weight and its reciprocal. Equations
(10.1.1.3), p. 434, and (10.2.2.3)–(10.2.2.5), pp. 445–446, give the
one-time twist, bilinear pairing, and positive exponent. We realize
only the strictly integrable boundary orders in the rational model.
Theorem 10.2.2.1 cites Theorem 9.3.2.6 for the stronger basis claim;
that citation assumes a nondegenerate interval and its extracted
projector argument has the [nesting issue](trace-spectral-strip-q.md#source-interface-a-missing-totality-step).
The closed-kernel inclusion uses neither that limit nor a converse
inclusion. It does not identify the adelic completion or settle the
printed cap at equality; the source reading is provisional.

## Checked obstruction to bounded extension on compact tests

In [BoundaryLogJet.lean](../../Proofs/Props/BoundaryLogJet.lean),
`Masullo.boundaryLogJet_exists_extension_iff` proves that a continuous
complex-linear functional on the ambient weighted log line can agree with
the Mellin pairing on the compact conjugate-kernel tests if and only if
$2m+1<s$. This holds for $s\ge 0$, $|\Re z|=\alpha$, and every natural
$m$, including at width zero and without any zero or multiplicity premise.

Write $k=x^m e^{zx}/W$ for the divided kernel.
`Masullo.boundaryLogJetTest_ae_eq` identifies the test with
$U_n=\mathbf 1_{[-n,n]}\overline k$ in the $U=Wu$ coordinate. The
literal pairing for $u=U_n/W$ is the absolutely convergent integral
$\int_{[-n,n]}\overline k k\,dx=\|U_n\|_2^2$.
[CompactKernelPairing.lean](../../Proofs/Lemmas/CompactKernelPairing.lean)
shows that the operator-norm bound forces $\|U_n\|_2\le\|F\|$.
Monotone convergence on the increasing intervals gives $k\in L^2$;
conversely, the conjugate of an $L^2$ kernel represents the functional.
Thus no such extension exists for excluded orders, even if one only asks
for agreement on this explicit sequence. This does not rule out agreement
on the theta inputs alone, or assert a smooth test-domain result.

Independent Yah statement review checked the scope and pairing against
(9.2.2.4), p. 412, (9.2.2.40)–(9.2.2.41), p. 417, and
(10.2.2.3)–(10.2.2.5), pp. 445–446, in the digest-matched layout
extraction. The strict criterion is a project repair to the apparent
non-strict bracket cutoff, also appearing in Corollary 9.2.2.5(2), p. 414.
Proposition 9.2.2.11 assumes a nondegenerate interval. Its extracted
reciprocal weight informs the calculation but does not supply the
width-zero proof. The printed cap still needs a rendered-page check.

## Checked obstruction on smooth compactly supported profiles

`Masullo.boundaryLogJet_exists_smooth_extension_iff` in
[BoundaryLogJet.lean](../../Proofs/Props/BoundaryLogJet.lean) proves that
requiring agreement only on smooth compactly supported profiles still
forces $2m+1<s$ (with $s\ge 0$, $|\Re z|=\alpha$, and any natural $m$).
The converse uses the existing boundary functional. Equality is excluded also
at width zero. No zero or multiplicity hypothesis is used.
`Masullo.weightedCompact_memLp` embeds each profile as the $L^2(dx)$
class of $Wu$; the pairing is $\int u(x)x^m e^{zx}\,dx$.

The proof selects the nondecaying tail, using the positive tail at
width zero. For $n\ge 0$, a `ContDiffBump` equals one on $[1,n+2]$
and vanishes outside $[1/2,n+5/2]$ in the selected orientation. With
$g=x^m e^{zx}$ and $V=e^{(\Re z)x}(1+x^2)^{s/4}$, set
$u_n=\chi_n\overline{g/V}/V$. The globally smooth $V$ coincides with
$W$ on the bump support, so the kink in $W$ at zero is immaterial.
[SmoothKernelPairing.lean](../../Proofs/Lemmas/SmoothKernelPairing.lean)
uses $Wu_n=\chi_n\bar k$, $u_n g=\chi_n|k|^2$, and
$\chi_n^2\le\chi_n$ to bound the weighted test norms by $\|F\|$.
Monotone convergence bounds the full tail mass by $\|F\|^2$.
The checked power criterion for $|x|^{2m}/(1+x^2)^{s/2}$ on that tail
then gives the strict inequality, with logarithmic divergence at equality.

Independent Yah statement review checked this interface against the
SHA-256-matched extraction of Definition 9.2.2.1 and (9.2.2.4), p. 412,
(9.2.2.37)–(9.2.2.41), p. 417, and (10.2.2.3)–(10.2.2.5),
pp. 445–446. Under $t=e^x$, the smooth compact log profiles have support
away from both endpoints and meet the decay conditions of Definition
B.2.1.1, p. 593, in the real-line starting domain $S_E(\mathbb R_{>0})$.
This inclusion is a source interpretation, not a Lean formalization of
that domain. The obstruction is a project repair, not a visual check
of the printed cap, a claim about testing on theta inputs alone, or an
identification of the adelic completion. The p. 417 duality proposition
assumes a nondegenerate interval, while the checked result does not.

The independent Haar branch now has a [checked window comparison](#checked-haar-comparison-for-a-normalized-upstairs-window)
and a [checked finite-unit identification](#checked-finite-unit-identification-of-the-norm-one-classes).
The [local restriction comparison](#checked-local-multiplicative-haar-and-its-restriction-to-integral-units)
is now checked. The [positive real multiplicative measure](#checked-positive-real-multiplicative-measure)
is also checked. [Upstairs normalization and window strip mass](#checked-upstairs-haar-and-window-strip-mass)
are checked for the constructed measure. The [finite-stage embeddings](#checked-open-embedding-of-every-rational-idele-stage)
are checked. The [full real local measure](#checked-full-real-local-multiplicative-haar-measure)
is checked. The [finite-stage Haar comparison](#checked-finite-stage-product-of-local-haar-measures)
is checked. The [global restricted-product characterization](#checked-global-restricted-product-characterization)
is checked over $\mathbb Q$. The [centered local Fourier indicator](#checked-fourier-transform-of-the-integral-indicator-over-qp)
is now checked on the separate additive branch, as is the [scaled and
translated formula](#checked-fourier-transform-of-dilated-and-translated-integral-balls).
The [diagonal phase cancellation](#checked-cancellation-of-the-rational-diagonal-phases)
is now checked, as is the [rational adelic character](#checked-rational-adelic-character).
The [finite-denominator clearing step](#checked-clearing-of-finite-adelic-denominators)
is checked, and the [global rational diagonal annihilator](#checked-rational-diagonal-annihilator)
is now exactly the diagonal. The [additive quotient topology](#checked-additive-quotient-topology-over-the-rationals)
is checked. The [half-open additive fundamental domain](#checked-half-open-additive-fundamental-domain)
is also checked, as is the [upstairs unit-strip mass](#checked-additive-haar-normalization-over-the-rationals).
The [additive quotient probability Haar](#checked-probability-haar-on-the-additive-rational-quotient)
is checked, as is the [nonnegative Weil formula](#checked-nonnegative-weil-formula-over-the-additive-rational-quotient).
The [complex Borel $L^1$ version](#checked-complex-weil-formula-and-absolute-summability)
is checked, as are the [quotient Fourier coefficient comparison and point
separation](#checked-unfolding-of-the-quotient-fourier-coefficients) and
[uniform density and Haar orthogonality](#checked-density-and-orthogonality-of-the-rational-quotient-characters).
The [pointwise reconstruction and rational counting-series formula](#checked-pointwise-poisson-summation-with-explicit-convergence-hypotheses) are checked under explicit convergence hypotheses. The [unramified tensor periodization](#checked-periodization-of-the-rational-unramified-tensor) is now absolutely convergent at every lift and continuous on the quotient, with the input integrable upstairs. The [unramified transform and pointwise Poisson formula](#checked-fourier-transform-and-pointwise-poisson-for-the-unramified-tensor) now discharge Fourier-side summability. The [adelic theta inversion theorem](#checked-adelic-theta-inversion-for-the-unramified-tensor) now applies to the actual tensor sums at every idele. The [integral-stage additive product formula](#checked-local-product-on-the-integral-finite-additive-stage) now identifies the compact factor as a product of local Haar probabilities. The [all-stage product theorem and global characterization](#checked-restricted-product-formula-for-rational-additive-haar) now give the rational global formula (A.3.1.3). The [global additive dilation law](#checked-rational-additive-haar-scaling-under-idele-dilation) is checked over $\mathbb Q$. The [translated finite-box transform](#checked-fourier-transform-of-translated-finite-boxes) and [pointwise Poisson summation for these boxes](#checked-pointwise-poisson-summation-for-finite-boxes) are now checked. The resulting [generator-span Poisson theorem](#checked-poisson-summation-on-the-translated-generator-span) is checked. The [pointwise theta identity](#checked-pointwise-theta-inversion-on-the-generator-span) is checked on that span; [joint convergence, continuity, and class theta inversion](#checked-joint-orbit-convergence-and-theta-inversion-on-idele-classes) are also checked.
