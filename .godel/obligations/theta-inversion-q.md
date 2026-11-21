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

## Next Haar step: Identify the full real local measure

Implement the real factor of Definition A.3.2.2(1), p. 560, on
$\mathbb R^\times$, with its Borel sigma-algebra. A concrete route is the
sign and log-absolute-value splitting: Transport counting measure on the
order-two sign group times log-Lebesgue measure, using counting measure
rather than probability so each sign has mass one. Identify its pushforward
under the real value map with $dt/|t|$ off zero. On the positive ray use
`Masullo.map_volume_exp_eq_restrict_realMultiplicative`; on the negative
ray use reflection. Audit the Haar instance and mass one on the inverse
image of $[1,e]$. The positive-ray result alone does not supply a measure on
both components.

Then compare the pullback of `rationalIdeleHaar` on each checked stage with
the product of that real Haar, the finitely many field-unit Haar measures
in $S$, and the compact product of integral-unit probabilities off $S$.
The open homomorphism gives the local topology for the pullback. For the
comparison by Haar uniqueness, use the preimage of $K$: The real value
lies in $[1,e]$, and all finite coordinates are integral units, including
those in $S$. The local masses are one. The Borel and product measure
interfaces, measure transport, and stage equalities remain open. The
additive finite Fourier self-duality problem is independent.

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
are checked. The [full real local measure](#next-haar-step-identify-the-full-real-local-measure)
can run separately from checking the printed endpoint at the visual gate.
