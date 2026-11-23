# Primary coordinate cuts and the global principal-value ranges

**Printed passage.** Masullo, *The Music of the Primes*, §1.3.2,
printed pp. 26–27, from “If we let $f$ (equivalently $f_S$) vary”
through the display after “yet smaller and closed subspace.” Write
$H=\mathrm H_{0,\mathrm{cont}}(\chi|_{C_F^1},\mathcal S_0(\mathbf A_F))$.
The paragraph puts the resulting theta images of the $k$th and
$(k+1)$st restrictions in $\mathrm{PV}_{P_k}H$ and
$\mathrm{PV}_{S_{p_{k+1}}}\mathrm{PV}_{P_k}H=\mathrm{PV}_{P_{k+1}}H$,
respectively, calling the latter a smaller, closed subspace. It
follows the convention that restriction is the coordinate unit cut
on a test representative, not restriction of a function on $C_F$
to a subset of that quotient. It follows the explicit first-primes
convention for $P_k$; earlier, (1.3.2.2) used tested sets disjoint
from $S$. The subsequent subquotient and its basis are a separate
claim.

Chapter Markdown and PDF layout extraction located the passage;
raster OCR checked the prose, and spot inspection of rendered crop
pixels checked the principal-value indices, $\mathcal S_0$ source,
and the phrase “yet smaller and closed subspace” across the two
pages. The local PDF matched the [edition pin][source]. The
parallel pp. 493–494 of §11.3.1.1, the Chapter 5 proof of Lemma
5.3.1.5, and the discussion of the moments in Lemma 5.5.2.1 were
consulted in chapter Markdown and are provisional here as new
readings of those passages.

**Failure for the literal cuts.** Take $F=\mathbf Q$, $S=\{\infty,2\}$,
and the trivial character. This $S$ is saturated, contains all the
required places, and has trivial $S$-class group. Take a nonzero even
nonnegative smooth bump $b$ supported away from zero at infinity,
$1_{\mathbf Z_2^\times}-1_{2\mathbf Z_2}$ at $2$, and integer-ring
indicators at the other primes. This test is of the prescribed
shape and belongs to $\mathcal S_0$: Its value at zero vanishes, and
so does its additive integral, since the two $2$-adic sets have equal
additive mass. The cut at $P_1=\{2\}$ kills the second summand and
leaves a strictly positive additive integral. The theta function
of the cut is not merely given by a bad representative: It is not
in $H$ at all.

For that last assertion, normalize additive mass of
$\widehat{\mathbf Z}$ to one, and evaluate theta at the class of
$(t,1,1,\ldots)$, $t>0$. The cut theta sum is
$\sum_{n\text{ odd}}b(nt)$. Multiplying by $t$ and sending $t$ to zero
gives $\tfrac12\int_{\mathbf R}b(x)\,dx>0$. For any rational
Schwartz–Bruhat test, the same scaled limit for the nonzero theta
sum is its additive integral. Indeed, write it as a finite sum of
real Schwartz functions times indicators of finite-adèle cosets
of $N\widehat{\mathbf Z}$ contained in $N^{-1}\widehat{\mathbf Z}$,
for some integer $N\ge 1$. Each coset intersects the rational
diagonal in one progression $a+N\mathbf Z$ by the Chinese remainder
theorem, and each scaled Riemann sum tends to the real integral
divided by $N$, the additive mass of the coset. Omitting zero does
not change that limit. The trivial norm-one projection does not
change the vanishing of the limit for two-zero-moment inputs:
Every norm-one rational idèle class has a sign-and-finite-unit
representative by clearing valuations. One can average the test
over this compact group before taking theta; it preserves the
additive integral and remains Schwartz–Bruhat (there is a common
open stabilizer on each finite test). On the cut example the
group acts trivially, so the projection only contributes a
nonzero scalar if the Haar measure is not normalized. Thus no
two-zero-moment input has its projected theta function equal to
the cut output. This refutes the claimed containment for the
literal filtration already at level one, not closedness of the
principal-value image as a separate claim.

The raw coordinate cut also need not descend, even when both
outputs have zero moments: Use the $2$-unit indicator and a real
factor $h(x)-\tfrac12h(x/2)$, with $h$ nonnegative, even, and
supported in $1<|x|<1.1$. Translate this test by the diagonal
rational $2$ using $T_a f(x)=f(a^{-1}x)$. The two tests remain in
$\mathcal S_0$ and in the same fixed tensor stage, with identical
theta by reindexing the rational sum. The cut fixes the first
and kills the second. The first theta is nonzero: Choose $t$ in
$(1,1.1)$ with $h(t)>0$. Only the odd integers $\pm1$ contribute,
and $h(t/2)=0$. Both theta functions before cutting are in the
trivial norm-one isotype. This obstruction is about cutting inside
$S$, not about descent of a principal-value operator.

**What does work.** If $P_k$ is disjoint from $S$, each tested
factor of a supplied tensor is $1_{\mathcal O_{F_v}}$. On it
$1-T_{\pi_v}$ gives $1_{\mathcal O_{F_v}^\times}$, as in Masullo's
parallel explanation in §11.3.1.1, p. 493. The later unit-averaged
factor $1-T_{\pi_v}U_v$ gives the same result on that factor,
since the normalized unit average $U_v$ fixes it. Both products
preserve the two zero moments and intertwine theta with the
corresponding products of translations and, where used, unit
averages. Thus for a supplied fixed-stage representative in
$\mathcal S_0$ the restricted theta is precisely the image of the
original theta under the corresponding principal-value product;
two such representatives of the same projected theta class give
the same output. If also the new fiber is disjoint from $S$, this
applies at both levels. The product equality and nesting are
algebraic for a consistent choice of commuting descended local
factors and the disjoint union of place sets. Nesting by itself
gives neither strictness nor closedness. Using all of $H$ in the
fixed-stage argument requires representatives with the two zero
moments, not just (1.3.2.1) read as surjectivity from the full
local test space. Lemma 5.5.2.1's moment descent and norm-one
invariance are inputs for that comparison.

**Open topological step.** For closedness, prove closed range of
the finite product in the intrinsic global two-zero-moment theta
quotient topology. It would suffice to obtain closed topological
embeddings on $H$ for the successive individual factors (a finite
composition is then a closed embedding), or verify the full
quotient closed embedding of Lemma 5.3.1.5 for the product and
justify the restriction to the closed moment kernel and isotype
with the intended topology. The [earlier closedness audit][closed]
identifies the missing quotient step. The repetition on pp.
493–494 supplies no proof of closedness. The [Mellin-step audit][step]
checks a raw zeta comparison, which also supplies no closed-range
argument.

**Provenance and Lean comparison.** The two containments and the
closedness assertion are Masullo's. The disjoint-factor identity
uses Masullo's uniformizer-difference explanation. The overlap
examples, scaled Riemann-sum argument, and separation of algebraic
nesting from closedness are the reviewer's. The existing
`Masullo.rationalAdeleLF_uniform_theta_tails` in
`Proofs/Theorems/RationalAdeleLFThetaTails.lean` at the candidate
base `e7cf12509d9926d58b33c64fcc9be7b8e356ed99` bounds the two tails
of the unprojected class theta on a bounded family of rational LF
tests, retaining both zero modes at small norm. It is not used in
the Riemann-sum proof. It does not address coordinate cuts,
principal-value membership, or the general closed range; no Lean
declaration is added or used to prove the refutation. Owning
source-review session: `01a2056a-f3ce-7a75-88fb-d796bae9feb5`.

## Lean bridge for the literal cut at 2

[`Masullo.rationalAdeleStageCell_two_eq_primeUnits`][two-cut] has no
additional hypotheses. On the full rational adeles, with unrestricted
real coordinate, let $W$ be the integral-finite cylinder, $U$ the unit
condition at $2$, and $C_j$ the level-$2$ stage cell of index $j$. The
endpoint gives $C_0=W\setminus U$ and $C_2=W\cap U$. The residue theorem
applied to $x/2$ covers $W$ by these two cells. Their finite coordinates
are $2z$ and $1+2z$, respectively, with $z$ integral at every finite
place. The completion valuation gives $v_2(2z)<1$ and $v_2(1+2z)=1$.

The manuscript mapping inherits the rendered reading above (pp. 26–27,
§1.3.2) and the [fixed-stage hypotheses][stage] (p. 25, (1.3.2.1)). It
uses $F=\mathbf Q$, $S=\{\infty,2\}$, the trivial character, and
$P_1=\{2\}$, not the disjoint-from-$S$ convention of (1.3.2.2). The
Lean identities do not depend on an isotype or on a theta-range claim.
Independent exact-source statement and applicability review:
`two-cell-statement` (`ArgOQLU`), in Yah session
`01a2058a-1b00-77fb-96bd-3b7e63112704`. The same session owns the
candidate build and fresh signature and axiom checks. No new rendered
reading was used for this bridge.

## Checked moment loss under the literal prime-two cut

[`Masullo.rationalAdeleLiteralTwoCut_moments`][two-cut] assembles two
rational adelic LF tests at factorial index $1$ (level $2$). For every
$b\in\mathcal S(\mathbb R,\mathbb C)$, put
$B_j(b)(x)=1_{C_j}(x)b(x_\infty)$. The assembled tests satisfy
$f=B_2(b)-B_0(b)$ and $g=1_U f=B_2(b)$ on the full adeles. The checked
moments are
$$
f(0)=-b(0),\qquad \widehat f(0)=0,\qquad
\widehat g(0)=\tfrac12\int_{\mathbb R} b(t)\,dt.
$$
The boxes use `rationalAdeleBox_stageCell`, and the cut uses the
cell identities above. In `rationalAdeleLFAssembly_fourier`, the
output profile at the cell of zero has coefficient $1/2$ for each
input profile, since its finite character factor is one.
`Masullo.rationalAdeleLiteralTwoCut_loses_moment` specializes to the
existing `bandSchwartzBump 2`, that is, a smooth real-valued bump
centered at real $2$, with $b(0)=0$ and nonzero integral. Both
endpoints use the Borel measurable-space instances for the normalized
adelic Fourier integral. Neither assumes evenness, any zero mode
of the profile, or any quotient topology.

The scope is the literal $P_1=\{2\}$ test cut for $F=\mathbf Q$,
$S=\{\infty,2\}$, and the trivial character. Source evidence is
inherited from the rendered readings above (Masullo, §1.3.2,
pp. 26–27) and in the [fixed-stage note][stage] (p. 25, (1.3.2.1));
no new manuscript reading was made. The endpoints do not formalize
that the averaged theta of $g$ has no two-moment representative,
and do not concern closedness. Independent exact-source statement
and applicability review: `two-cut-moment-statement` (`fAcdExh`),
Yah `01a20597-4e49-7616-916c-6623d59bbe85`, which also owns the
candidate build and fresh signature and axiom checks.

## Checked exclusion from the averaged two-moment range

In [RationalThetaAverageFourierZero.lean][average-zero],
`Masullo.tendsto_rationalAdeleClassThetaFiniteUnitAverage_exp_mul`
proves, for every rational adelic LF test $h$,
$$
e^x\Theta_{\rm av}(h)(\tau(x))\longrightarrow \widehat h(0)
\qquad(x\to-\infty),
$$
where $\tau(x)$ is the actual rational idele class log section at
`Multiplicative.ofAdd x`. The project finite-unit mean is ordinary
class theta of the averaged LF test, with both moments unchanged.
The [LF tail estimate][lf-tails] at $m=0$ for that singleton bounds
the corrected remainder on $x\le 0$. Since $\|\tau(x)\|=e^x$,
multiplying by $e^x$ makes both the bounded remainder and the spatial
zero-mode term tend to zero. The auxiliary measurable and Borel
structures on the **additive** adele quotient are chosen locally;
all three endpoints assume only the measurable and Borel structures
on the adeles. The limit assumes no vanishing or parity conditions.

`Masullo.rationalAdeleClassThetaFiniteUnitAverage_fourier_zero_eq`
uses uniqueness of this limit when two averaged class functions
coincide. With the literal cut witness above,
`Masullo.rationalAdeleLiteralTwoCut_averagedTheta_not_mem_range`
then gives $f$ with both moments zero and $g=1_U f$ with
$\Theta_{\rm av}(g)$ outside the image of **all** two-moment LF tests
under the same average. It excludes a different representative, not
just preservation of the moments on the supplied one. The accepted
`range_rationalAdeleClassThetaFiniteUnitAverage` identifies that range
with the project's radial two-moment class-theta range.

The cut mapping inherits the rendered notes above for §1.3.2,
pp. 26–27, and [the fixed-stage note][stage] for (1.3.2.1), p. 25.
It is the rational trivial-character case with $S=\{\infty,2\}$ and
$P_1=\{2\}$, not the disjoint product of (1.3.2.2). The tail's
comparison to Theorem 2.2.3.4, pp. 82–86, is extraction-based and
not a premise of the Lean proof. This is a result for the project
average, not a Lean identification with the printed projection or
its principal-value image. It does not address closedness.

Independent fixed-statement and exact-source applicability review:
`averaged-zero-statement` (`dKRAfMW`), Yah
`01a205a2-07e1-72b0-947f-e912f7a93ca1`. The same owning session records
the dependency probe (including the local quotient instances),
integrated build, fresh signatures and axiom reports, and adoption.
No new manuscript reading was used.

## Checked identification with the compact Haar average

In [RationalThetaFiniteUnitAverage.lean][finite-average],
`Masullo.rationalAdeleClassThetaFiniteUnitAverage_eq_integral` gives
$$
\Theta_{\rm av}(h)(d)=\int_{C_{\mathbf Q}^1}\Theta(h)(kd)\,dk
$$
with `rationalNormOneHaar`. This holds pointwise for every rational
adelic LF test $h$ and every idele class $d$, with no moment or parity
hypotheses. The only measurable-space binders are on the idele class
group, with its Borel structure. The averaged LF test has norm-one
invariant theta without moment conditions. The continuous compact
slices are integrable; integrating the constant averaged slice and
using translation invariance on each term of the finite mean gives
the identity. No topology on the theta image is involved.

Replacing the finite mean by this integral on **both** sides of the
range comparison transfers the checked literal prime-two obstruction
to compact Haar averaging. The rewrite works by function extensionality
and was checked in Lean. It does not identify the printed
principal-value operator or its closure.

**Source scope.** The [theta-jet note][theta-jets] supplies the inherited
rendered compact averaging display (2.2.5.2), p. 95; with trivial
character, inversion of the compact translator does not affect the
average. The [weighted pairing note][pairing] maps (2.2.5.7), p. 96,
to counting Haar on extraction evidence only. The [rational moment
note][unit-haar] supplies the inherited rendered mass-one specialization
of (A.3.2.1), pp. 559–560. These are source mappings, not premises of
the Lean equality. No new manuscript reading was used.

Independent exact-statement and applicability review:
`theta-haar-statement` (`pklqvoL`), transcript in Yah
`01a205ae-4590-795b-a902-0051e8cce501`. The review was source-only;
the same owning session checked elaboration, including the finite-sum
interchange without importing a separate finite-unit Haar transport.

## Checked disjoint prime-two positive control

[`Masullo.exists_rationalAdeleUnramifiedTwoCut`][unramified-two-cut]
assumes a supplied LF test $f$ whose underlying function is
$b\otimes1_{\widehat{\mathbb Z}}$, with $b$ a complex-valued Schwartz
function on $\mathbb R$. It realizes the literal prime-two unit cut $g$ as an LF
representative, with the pointwise cut equality on all additive
adèles. The level-two assembly uses just cell $2$, of profile $b$.
For every rational idele class $d$, Lean proves

$$
\Theta(g)(d)=\Theta(f)(d)-\Theta(f)([\varpi_2]^{-1}d).
$$

There are no measurability, moment, or parity hypotheses on this
endpoint. The cut is invariant under finite-unit multiplication:
It preserves the real coordinate and all finite valuations. The
class-theta pullback and finite-unit description of the norm-one
classes transport the section formula to $d$. Unramified theta
already depends only on the norm, and the inverse uniformizer
multiplies that norm by $2$. This uses the norm formula, which has
weaker hypotheses than `rationalThetaRadialProfile_uniformizer`.

For the two-moment specialization, the input theta is already
norm-one invariant, so it belongs to the represented radial
core. The right side is the class theta of the represented
`rationalThetaRadialPrimeDifference`, by applying
`rationalThetaRadialPrimeDifferences_class_insert` to the empty set.
Both the cut and uncut class theta are fixed by compact Haar
averaging, by `rationalAdeleClassThetaFiniteUnitAverage_of_invariant`
and `rationalAdeleClassThetaFiniteUnitAverage_eq_integral`. The joint
check specializes to a
`RationalThetaRadialInput` for these two comparisons; the Haar
rewrite uses the Borel structure on the idele class group. The
claim here does not identify an operator on arbitrary choices of
representatives, the printed principal-value operator, or any
closure. It does not contradict the overlap obstruction above:
The latter's input finite factor at $2$ is not the integral-ball
indicator.

**Source scope.** For $\mathbb Q$ and the trivial compact character,
$S=\{\infty\}$ contains the archimedean and ramified places and has
trivial $S$-class group, on the intended reading of a finite set
of places. The [fixed-stage note][stage] verifies the printed
requirements and the tensor shape in (1.3.2.1), p. 25;
we assume the tensor, not the uniform supply of representatives.
The [ordinary filtration note][ordinary] verifies (1.3.2.2),
p. 25, with $P_1=\{2\}$ disjoint from $S$. The [tensor audit][tensor]
verifies the outside-$S$ input in (11.3.1.1), p. 492, and the
printed index in §1.3.2, p. 26. We use its repair with complement
of $S\cup P_1$, not the right-hand index as printed. The defining
nonzero rational theta sum in (2.2.3.1), p. 81, and the two moments
in (2.2.4.23), p. 91, inherit the [rendered theta readings][theta-sum].
The compact averaging evidence and its limits are as in the
previous section. These source readings are inherited, not new
verification or premises of the Lean equality.

Independent fixed-statement and applicability review:
`two-cut-statement` (`tViZcAs`), Yah
`01a205bb-627a-797f-84e6-d6e639142d5e`. The review checked exact
source, not elaboration. The same owning transcript records the
integrated build, fresh signature and axiom report, and both
specialization checks.

## Checked LF realization at any single rational prime

[`Masullo.exists_rationalAdelePrimeMaskedLF`][prime-mask-lf] takes any
`p : Nat.Primes` and `b : 𝓢(ℝ, ℂ)` and gives
`∃ g : RationalAdeleSchwartzLF, g.toUnion.val = rationalAdelePrimeMasked p b`.
This is function equality on **all additive adèles**. In particular, if
an LF test $f$ has underlying function `rationalAdeleUnramified b`, then
the same $g$ is the indicator of `rationalAdelePrimeUnits p` times $f$.
No moment, parity, or measurability premises are required, nor does the
endpoint require an LF witness for the uncut tensor as input.

The compact-open-stage assembly uses support contained in
$W_f=\widehat{\mathbb Z}$ and translation subgroup $pW_f$. Adding a
translation preserves $W_f$ membership in both directions. Its local
valuation at $p$ is strictly less than one in the multiplicative
convention, so the valuation-one condition is preserved by addition
and recovered by subtraction. Neither direction assumes the starting
adèle integral. The translation does not change the real coordinate,
and each real fiber is $b$ or zero. This replaces the level-two cell
assembly for LF existence, not the all-class calculation above.

**Source scope:** The [ordinary filtration note][ordinary] supplies the
inherited rendered disjointness clause in (1.3.2.2), p. 25, applicable
because $S=\{\infty\}$ and the tested place is finite. The [tensor
audit][tensor] supplies the inherited rendered outside-$S$ input in
(11.3.1.1), p. 492. Its separate rendered reading of §1.3.2, p. 26,
verifies the printed index, which this realization does not use: The
untested integer-ring factors are indexed by the complement of
$S\cup\{p\}$. The scope is a supplied tensor, not a theorem furnishing
such representatives for an entire isotype.

**Review and checks:** `prime-mask-lf-statement` (`QWROJwZ`), in Yah
`01a205c8-dccc-7772-b80f-9b4e18bba3ee`, independently checked the fixed
statement, compact-open-stage reduction, and applicability of the
inherited readings against accepted source, without elaboration.
The same owning transcript records the integrated build, fresh
signature and axiom report, and supplied-tensor application check.

The [all-prime result below](#checked-all-class-theta-identity-at-any-single-rational-prime)
uses this witness to extend the class calculation to every prime.

## Checked all-class theta identity at any single rational prime

[`Masullo.exists_rationalAdeleUnramifiedPrimeCut`][unramified-prime-cut]
takes `p : Nat.Primes`, `b : 𝓢(ℝ, ℂ)`, and a supplied LF test $f$
whose underlying function is `rationalAdeleUnramified b`. It gives
an LF test $g$ whose underlying function equals the literal $p$-unit
indicator times $f$ on **all additive adèles**. For every rational
idele class $d$ it gives

$$
\Theta(g)(d)=\Theta(f)(d)-\Theta(f)([\varpi_p]^{-1}d).
$$

The result assumes no moment, parity, or measurability conditions.
`exists_rationalAdelePrimeMaskedLF` supplies $g$. Multiplication by
finite units preserves all finite valuations and the real coordinate,
so class theta of the mask is invariant under the norm-one classes.
This transports `rationalTheta_eq_primeMasked_idele_sum` off the
positive section. Uncut theta depends only on the norm, and
`ideleNorm_rationalThetaRadialUniformizer` identifies the removed term
at $pN(d)$, not $N(d)/p$. The two-moment radial input is not used.
The prime-two theorem retains its statement as a specialization.

**Source scope:** The inherited rendered readings establish separate
clauses: The [ordinary filtration note][ordinary] gives disjointness
in (1.3.2.2), p. 25, satisfied by a finite $p$ with $S=\{\infty\}$;
the [tensor audit][tensor] gives the outside-$S$ input in (11.3.1.1),
p. 492; and the [theta source interface][theta-sum] gives the sum over
nonzero rationals on an idele representative after specializing
(2.2.3.1), p. 81. The tensor audit separately verifies the printed
right-hand index in §1.3.2, p. 26. We use the **repair** with the
complement of $S\cup\{p\}$, not that printed index. Neither supply of
representatives for a whole isotype, descent across arbitrary input
LF lifts, nor identification with the printed principal-value
operator is established.

**Review and checks:** Fixed-statement source review `prime-cut-statement`
(`HuHmzhK`), Yah `01a205d5-516f-72c6-b2e4-6577e182438a`, checked both
the class reduction and applicability of the inherited passages,
without elaboration. The owning transcript in that same session
records the variable-prime dependency probe and the integrated
build and joint signature and axiom checks.

The [joint LF realization below](#checked-joint-lf-realization-at-two-rational-primes)
supplies the witness for a two-prime theta comparison.

## Checked joint LF realization at two rational primes

[`Masullo.exists_rationalAdeleUnramifiedTwoPrimeMaskLF`][prime-mask-lf]
takes `p q : Nat.Primes`, `b : 𝓢(ℝ, ℂ)`, and a supplied
`f : RationalAdeleSchwartzLF` with `f.toUnion.val = rationalAdeleUnramified b`.
It gives a single `g : RationalAdeleSchwartzLF` with
`g.toUnion.val = Set.indicator (rationalAdelePrimeUnits p ∩ rationalAdelePrimeUnits q) f.toUnion.val`.
This is equality on **all additive adèles**, including zeros and
nonintegral finite coordinates. No distinctness, moment, parity, or
measurability premises are needed. When $p=q$ the indicator is the
one-prime cut. The earlier one-prime signatures are unchanged.

For $W_f=\widehat{\mathbb Z}$, use the open additive subgroup
$pW_f\cap qW_f\subseteq W_f$. The one-prime proof's valuation-one
invariance is now a shared private lemma: Addition and subtraction of
an element of $pW_f$ preserve the unit predicate at $p$, without
requiring the starting adèle to be integral. On the intersection,
both invariances hold. Translation also preserves integrality and
the real coordinate. The joint function vanishes off finite support
$W_f$, and each real fiber is $b$ or zero. The existing compact-open
stage assembly then supplies $g$. This is not an iteration of the
one-prime theorem, which does not take a masked tensor as input.

**Source scope:** The [ordinary filtration note][ordinary] gives the
inherited rendered disjointness in (1.3.2.2), p. 25, satisfied by
$S=\{\infty\}$ and $P=\{p,q\}$. The [tensor audit][tensor] gives the
inherited rendered outside-$S$ input in (11.3.1.1), p. 492, and
separately verifies the printed right-hand index in §1.3.2, p. 26.
This is the **repair** with integer rings indexed by the complement
of $S\cup P$, not the printed right-hand index. The Lean result is LF
existence for the supplied tensor, not supply of representatives for
an isotype, moment preservation, descent across arbitrary lifts, or
an evaluation of the principal-value operator.

**Review and checks:** `joint-mask-statement` (`jwapTMz`), in Yah
`01a205df-58d2-785b-a3a7-c3e6a3d2093e`, independently checked the fixed
statement, stage reduction, and applicability of the inherited
readings by exact-source inspection, not elaboration. The same owning
transcript records the dependency probe, integrated build, joint
signature and axiom reports, and adoption.

**Continuation:** The [section comparison below](#checked-two-prime-theta-on-the-positive-norm-section)
now evaluates the joint witness supplied here.

## Checked two-prime theta on the positive norm section

[`Masullo.rationalTheta_eq_twoPrimeMasked_idele_sum`][two-prime-section]
takes distinct `p q : Nat.Primes`, `b : 𝓢(ℝ, ℂ)`, and `0 < t`. Write
$\sigma(t)=(t,1,\ldots)$ and use the representative sum over
$\mathbb Q^\times$. The norm series of the joint mask is summable, and

$$
\Theta_{p,q}(\sigma(t)) = \Theta_p(\sigma(t)) - \Theta_p(\sigma(qt)).
$$

The statement is for the underlying tensor functions, without any LF
witness hypotheses. The companion
[`Masullo.exists_rationalAdeleUnramifiedTwoPrimeCutSection`][two-prime-section]
takes `f : RationalAdeleSchwartzLF` with `f.toUnion.val = rationalAdeleUnramified b`.
It gives a single pair of LF tests for all positive $t$, with exact
pointwise mask equalities on all additive adèles. No spatial or Fourier
zero-mode condition, parity, or averaging is used.

Both pieces at $q$ are dominated by the norm of the single-prime
series. The two instances of
`rationalAdelePrimeMasked_section_support_iff` identify the discarded
indices as $n\in\mathbb Z\setminus\{0\}$ with $p\nmid n$ and $q\mid n$.
Multiplication by $q$ in $\mathbb Q^\times$ pulls that index set back
to the nonzero integers $m$ with $p\nmid m$, since $p\ne q$. It pulls
the discarded summand back to the single-prime summand at $qt$,
including the zero extensions off those index sets. No class transport
or descent across arbitrary lifts is asserted.

**Source scope:** The [ordinary filtration note][ordinary] supplies the
inherited rendered disjointness clause (1.3.2.2), p. 25, applicable with
$S=\{\infty\}$. The [tensor audit][tensor] separately verifies the
outside-$S$ input in (11.3.1.1), p. 492, and the printed right-hand
index in §1.3.2, p. 26. We use the repaired complement of
$S\cup\{p,q\}$, not that printed index. The
[theta source interface][theta-sum] supplies the inherited rendered
nonzero representative sum (2.2.3.1), p. 81. The dilation identity is
a Lean calculation on this repaired tensor, not a source reading or
an assertion about an entire isotype.

**Review and checks:** Fixed-statement independent source review
`two-prime-section-review` (`OIzuCBZ`), in Yah
`01a205e8-2171-719c-b51e-19e976a68a1f`, checked the two signatures, the
reindexing and LF reductions, and the applicability of the inherited
readings at `7b1cd58ee10636e87883a82168945cabd56d8c72` without
elaboration. The owning transcript in that same session records the
matching-workspace dependency probe and the integrated build and
joint signature and axiom checks.

The [all-class result below](#checked-two-prime-theta-on-every-rational-idele-class)
transports this identity without changing the tensor or redoing the
series calculation.

## Checked two-prime theta on every rational idele class

[`Masullo.rationalAdeleClassTheta_twoPrimeMasked`][two-prime-section]
takes `p q : Nat.Primes`, `hpq : p ≠ q`, `b : 𝓢(ℝ, ℂ)`, and
`d : IdeleClassGroup (𝓞 ℚ) ℚ`. Let $M_p b$ and $M_{p,q}b$ be the
single- and joint-unit masks of the supplied unramified tensor. Then

$$
\Theta(M_{p,q}b)(d) = \Theta(M_pb)(d) - \Theta(M_pb)([\varpi_q]^{-1}d).
$$

There is no LF witness, moment, parity, or section hypothesis. The
proof-private `masked_theta_section` uses the one-prime valuation
calculation for any mask predicate determined by the finite valuations.
Finite-unit multiplication preserves those valuations, the integral
support, and the real coordinate. This checks both unit tests at once,
without using distinctness. On a representative, commute the finite
unit past each principal multiplier and apply `tsum_congr`. The two
norm-one invariance equivalences then reduce both class theta functions
to the positive section. The translated norm is $qN(d)$, not $N(d)/q$,
by `ideleNorm_rationalThetaRadialUniformizer`. At this point the accepted
section identity applies with $t=N(d)>0$.

**Source scope:** The inherited [ordinary filtration reading][ordinary]
verifies disjointness in (1.3.2.2), p. 25, which holds here since both
places are finite and $S=\{\infty\}$. The [tensor audit][tensor] verifies
the outside-$S$ input in (11.3.1.1), p. 492, and separately the printed
right-hand index in §1.3.2, p. 26. The checked identity uses the repaired
complement of $S\cup\{p,q\}$, not that printed index. The
[theta source interface][theta-sum] verifies the nonzero representative
sum in (2.2.3.1), p. 81. No new source reading was needed. This is neither
a descent theorem across arbitrary LF lifts nor a range theorem for the
printed principal-value operator.

**Review and checks:** `all-class-two-prime-statement` (`ZqTlhPv`),
in Yah `01a20631-9b06-7231-a074-94229e60c07b`, independently checked
the fixed signature, section reduction, norm direction, and application
of the inherited readings against `998be47bb20823c621cf4f99969f980f41b8c39b`
by exact-source review, without elaboration. The same owning transcript
records the dependency probe and assembled candidate checks.

**Next bounded check:** For $p=2$, $q=3$, identify the two integral
level-six cells on which both masks are one. In the `j/6` coordinate of
`rationalAdeleStageRepresentative`, the expected indices are $6$ and
$30$ (residues $1$ and $5$ modulo $6$). The level-two proof of
`rationalAdeleLiteralTwoCut_moments` already gives the zero-frequency
reduction for a factorial-stage assembly: At the zero cell the character
factor in `rationalAdeleStageFourier_apply` is one, and here each
surviving profile would have weight $1/6$. What remains is the actual
joint support identification using `mem_rationalAdeleStageCell_iff`
and the local unit predicates, then application of the stage formula
at level six. This would give the Fourier zero mode $\tfrac13\widehat b(0)$,
not an assertion about arbitrary representatives. The
[theta source interface][theta-sum] separately verifies the two-mode
domain in (2.2.4.23), p. 91, and the Fourier integral convention in
(2.2.4.32), p. 92, under which the phase is one at zero. The finite
coefficient is a project calculation on the repaired tensor.

[two-prime-section]: ../../Proofs/Theorems/RationalThetaUnramifiedTwoPrimeCut.lean

[unramified-prime-cut]: ../../Proofs/Theorems/RationalThetaUnramifiedPrimeCut.lean

[prime-mask-lf]: ../../Proofs/Theorems/RationalAdelePrimeMaskLF.lean

[unramified-two-cut]: ../../Proofs/Theorems/RationalThetaUnramifiedTwoCut.lean
[theta-sum]: ../obligations/trace-theta-density-qi.md#source-interface

[finite-average]: ../../Proofs/Theorems/RationalThetaFiniteUnitAverage.lean
[average-zero]: ../../Proofs/Theorems/RationalThetaAverageFourierZero.lean
[lf-tails]: ../obligations/theta-inversion-q.md#checked-uniform-theta-estimates-for-rational-lf-bounded-families
[theta-jets]: ../obligations/trace-theta-jets-qi.md
[pairing]: ../obligations/single-place-norm.md#weighted-gaussian-decay-at-small-norm
[unit-haar]: ../obligations/trace-moment-codimension-q.md#printed-statement-and-domain
[ordinary]: divisorial-filtration.md
[tensor]: primary-divisorial-tensor-cut.md

[two-cut]: ../../Proofs/Theorems/RationalAdeleLiteralTwoCut.lean
[stage]: fixed-stage-theta-representatives.md
[source]: ../sources/masullo/README.md
[closed]: global-orbital-submodule.md
[step]: primary-divisorial-mellin-step.md
