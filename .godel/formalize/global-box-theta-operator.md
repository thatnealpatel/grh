# Global theta on the number-field adelic box span

[Formalize receipt](4a01261d4f3c84fac068171d7405f89eacc58301aed2304d9880590548f692e3-e248719c5f013e7e37cd053a7a79092c108220df0759201885fc23d3f14ece2a.json) ·
[Lean module](../../Proofs/Theorems/AdeleBoxThetaOperator.lean)

Writer base: `a684299f2b54e602be826969b35b7c1f30742700`.
Owning Yah check session: `01a20558-ef10-7d62-9c7c-6e761890d947`.
The owning session records the integrated candidate and base, the independent
review, and the exact-candidate checks separately from the writer checks below.

## Source and scope

Edition checked (940 pages, 6,756,996 bytes): [Masullo, *The Music of the
Primes*](../sources/masullo/README.md), SHA-256
`e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5`.
The locators below refer to the page renders. Printed page numbers equal
one-based PDF ordinals at these locators.

- **§1.1.4, third bullet, p. 12:** the unnumbered display is
  \(\Phi_F(f)(g)=\sum_{\xi\in F^\times} f(\xi g)\), for
  \(g\in\mathrm{GL}_1(\mathbf A_F)\). The test space is
  \(\mathcal S(\mathbf A_F)\); the space of global theta functions is its
  quotient by \(\ker\Phi_F\), and the text asserts strict LF by the
  Structure Theorems. The bullet does not specify the quotient topology
  there. This is neither the S-unit sum in the first bullet nor the
  decay assertion in the next bullet.
- **Lemma 2.2.2.1, pp. 77–81:** the display (2.2.2.1) uses
  \(f(g(\xi+x))\) on \(\mathrm{GL}_1(\mathbf A_F)\times\mathbf A_F\).
  The series is asserted absolutely and compact-uniformly convergent;
  part (2), p. 77, gives continuity and principal invariance at \(x=0\).
  The proof reduces to tensors at (2.2.2.4), p. 78, bounds the union of
  the diagonal supports on the compact set by one fractional ideal
  (p. 79, (2.2.2.10) and the paragraph below), and uses the corresponding
  norm series (pp. 80–81, (2.2.2.11), (2.2.2.13)–(2.2.2.14), with
  exponent greater than \([F:\mathbb Q]\)). The proof below only handles
  \(x=0\); it obtains a common lattice directly on an arbitrary compact
  idele set, and not the stronger fractional-ideal assertion of part (3).
- **Definition 2.2.3.1, pp. 81–82:** (2.2.3.1) uses the sum over
  \(F^\times\) with an idele lift \(g'\) of a class \(g\in C_F\). The
  continuation on p. 82 asserts independence of the lift by invariance and
  complex linearity with values in \(C(C_F)\).
- **Definition 5.1.1.1(3), p. 223:** the left quotient in (5.1.1.3)
  is the global one, with its quotient topology. **Theorem 5.1.1.3(1),
  pp. 223–224**, asserts the kernels are closed; its proof, p. 229,
  uses continuity of the Mellin transform (Lemma 5.1.3.1(1)) and equality
  of kernels (Lemma 5.1.2.1(1), (5.1.2.1), p. 224) in the global case.
  Neither Mellin result is used in the new Lean proof.
- **Theorem 5.2.1.1(1), p. 230, and proof, p. 231:** the global
  quotient is asserted to be a strict locally convex inductive limit of
  nuclear Fréchet spaces. The first part of the proof passes from the
  closed kernel to Fréchet quotients of the Fréchet source stages, but
  does not check that their induced transitions are closed topological
  embeddings before invoking completeness. If \(K=\ker\Phi_F\) and
  \(E_n\subseteq E_{n+1}\) are successive Fréchet stages, the preimage
  in \(E_{n+1}\) of the image of the smaller quotient is
  \(E_n+(K\cap E_{n+1})\). Its closedness would give a closed Fréchet
  target image and the open mapping theorem would give the embedding.
  Closedness of \(K\cap E_{n+1}\) alone does not show this. This is a
  missing argument, not a refutation of strict LF or of an alternative
  presentation.

### Separate S-stage issue in Theorem 5.2.1.1(2)–(3)

These parts concern enlargement of the finite set of places and insertion
into the global quotient, (5.2.1.1)–(5.2.1.3), p. 230. On p. 231 the
pullback identity \(\pi_S^{-1}K=\ker\Phi_{F,S}\) identifies the kernel
on a stage. It does not imply preservation of \(K\) by a projection from
the ambient space onto that stage. Immediately before “descends” the
printed equality is
\(\overline\Pi_S(K)=K\cap\pi_S(\mathcal S(\mathbf A_{F,S}))
=\overline\pi_S(\ker\Phi_{F,S})\subset K\).
The bars are quotient-map notation in this theorem; the equality required
for the argument is at the source level, with unbarred maps. The proof
uses that preservation to obtain closed complemented images (pp. 231–232;
p. 231 also marks “WORK 1: adjust this Theorem”). The isotype statement
starting at Theorem 5.2.3.1, p. 233, is separate.

In fact, the specific tensor projection in **Lemma 2.1.4.3(1), p. 73**
((2.1.4.9) and the proof using Hahn–Banach) need not preserve \(K\).
That proof takes identity on the S-factor and \(w\mapsto\lambda(w)h\)
on the complementary factor, with \(h\) the indicator of the product
of the integer rings and \(\lambda(h)=1\). For a counterexample, take
\(F=\mathbb Q\), \(S=\{\infty\}\), \(h=1_{\widehat{\mathbb Z}}\),
and a smooth bump \(b\) supported in \((3/4,5/4)\), \(b(1)=1\). The
Schwartz–Bruhat function
\[
 f(x,z)=b(2x)h(2z)-b(x)h(z)
\]
is in \(K\) by reindexing the absolutely convergent sum by multiplication
by \(2\) on \(\mathbb Q^\times\). Its projection is
\((\lambda(h(2\,\cdot))b(2x)-b(x))h(z)\). At the identity idele, the
finite indicator in this projection selects precisely the nonzero rational
integers. None of their doubles lies in the support of \(b\), and only
\(1\) contributes to the second term, so its global theta value is
\(-1\), for every choice of \(\lambda\) above. This is a mathematical
counterexample to that projection descending, not a Lean endpoint, and
not a counterexample to strict LF, the stage pullback identity, or the
existence of other projections.

## What is formalized

At the writer base, `Masullo.adeleBoxSpan` ([AdeleBoxDilation](../../Proofs/Lemmas/AdeleBoxDilation.lean))
is the complex span in the actual adelic function space of
\(\phi(x_\infty)1_{a+g\widehat{\mathcal O}_K}(x_f)\), with arbitrary
Schwartz \(\phi\) on the Euclidean mixed space, a finite adele \(a\),
and an actual finite-adele unit \(g\). See `adeleBoxTensor` and
`finiteAdeleBox` in the accepted [`AdeleBoxFourier`](../../Proofs/Theorems/AdeleBoxFourier.lean)
and [`FiniteBoxStageFourier`](../../Proofs/Lemmas/FiniteBoxStageFourier.lean).
Mathematically the boxes generate the finite factor: use the local cosets
in Example 2.1.2.6, p. 65, (2.1.2.1), and the compact-open subgroup
stage presentation of Proposition 2.1.2.8(1), p. 65. A compactly supported
locally constant function has a finite cover of its nonzero support by
constant boxes; taking a common smaller box subgroup gives a finite
disjoint partition by translates (each compact box has finite index over
that open subgroup). The source tensor isomorphism in Lemma 2.1.3.2(2),
p. 68, (2.1.3.2), gives the corresponding algebraic generators globally;
its proof starts on p. 69. This uses translated compact-open cosets, not the
subgroup-only indicators literally listed in 2.1.3.2(3), p. 68 (those
indicators are even and cannot generate general finite tests). There is no
new Lean identification with a separately defined general Schwartz–Bruhat
LF space and its stages. This is not a restriction to decomposable
Archimedean factors or a claim that the boxes generate a mathematically
proper subclass of the tests.

The accepted `Masullo.rationalRealThetaQuotient_closedStage` in
[`RationalRealThetaQuotient`](../../Proofs/Theorems/RationalRealThetaQuotient.lean)
concerns the separate real S-local quotient. The accepted
`Masullo.idele_periodization_rapidDecay_of_support` in
[`IdeleClassRapidDecay`](../../Proofs/Theorems/IdeleClassRapidDecay.lean)
is a support-conditional decay estimate, not a summability or
continuity theorem for general adelic tests on compact idele sets.

Write \(d:K^\times\to\mathrm{GL}_1(\mathbf A_K)\) for
`IdeleGroup.unitEmbedding`, the diagonal on units. `val` is the underlying
adele. The units topology records both the underlying adele and the
underlying adele of the inverse; it is not just the subspace topology
of the units in the adeles. The target of `adeleBoxThetaLinear` uses Mathlib's actual
`IdeleClassGroup`, the topological quotient by the image of \(d\).

For a generator and a compact idele set \(B\), first clear the translate
and scale using `exists_finiteAdele_clearDenominator` in
[`FiniteAdeleDenominators`](../../Proofs/Lemmas/FiniteAdeleDenominators.lean).
The product of these two nonzero denominators embeds as a principal idele
\(c\) taking the whole box into the finite integer rings. Now apply
`exists_uniform_denominator_of_isCompact` in
[`IdeleCompactDenominators`](../../Proofs/Lemmas/IdeleCompactDenominators.lean)
to the compact idele set \(cB\). This gives one positive integer \(m\)
such that every index \(b\) contributing at **any** \(h\in B\) satisfies
\(mb\in\mathcal O_K\). There is no dependence of this support constraint
on the individual idele.

At infinity, all the inverse coordinates have bounded norms on \(B\),
so all forward norms have one positive lower bound. Multiplicativity of
coordinate norms gives \(l\|\iota(mb)\|_\infty\leq\|x(d(b)h)\|_2\)
for some \(l>0\) independent of \(b,h\), where \(\iota\) is the mixed
embedding and \(x\) is the Euclidean Archimedean coordinate. On the
fixed support subtype, \(b\mapsto\iota(mb)\) is an injection into the
integer lattice \(\Lambda\), and its image avoids zero. For
\(p=\mathrm{rk}_{\mathbb Z}\Lambda+1\) Schwartz decay bounds the summands
by \(D l^{-p}\|\iota(mb)\|_\infty^{-p}\); Mathlib's lattice summability
makes this a summable majorant. It extends by zero outside the subtype;
the series is still indexed by every \(b:K^\times\). The triangle
inequality and scalar norm extend this to the entire complex span.

Thus the complex and absolute subsums converge uniformly on each compact
set. Each summand is continuous: the product of finite integer rings is
clopen in the restricted product, and the box is its preimage under
\(z\mapsto g^{-1}(z-a)\). The idele group is locally compact (the scoped
`Masullo.locallyCompact_ideleGroup` in
[`IdeleIdealClassStrict`](../../Proofs/Theorems/IdeleIdealClassStrict.lean)),
so uniform convergence on a compact neighborhood at each point gives
continuity on ideles. Reindexing the actual sum by \(b\mapsto bu\)
proves principal invariance. The quotient map transfers continuity to
classes, and absolute summability justifies addition and scalar
multiplication termwise. There are no Haar-measure premises.

The construction proves continuity **in the idele class variable**.
It does not give continuity **as an operator on a Schwartz–Bruhat source
with its LF topology**, closedness of its theta kernel there, the
quotient topology, strict embeddings, or nuclearity. The idele-class
target quotient is not the quotient of the test space by the theta kernel.
For a retry, identify the boxes with a general countable Schwartz–Bruhat
Fréchet stage model, prove stage-wise continuity of theta evaluations or
identify the kernel with that of a continuous source operator, and then
prove the indicated quotient-stage closedness or give an alternate strict
presentation with the same quotient topology. Obtain stage nuclearity and
its permanence for the indicated closed quotients separately. The specific
S-projection above cannot supply the necessary kernel-preserving retractions.

## Reproduce the writer checks

From this workspace, run `lake build --wfail +Theorems.AdeleBoxThetaOperator`.
For the joint ordinary-import signature and axiom check:

```sh
check=$(mktemp --suffix=.lean)
{
  printf 'import Theorems.AdeleBoxThetaOperator\nimport Lemmas.AdeleBoxDilation\n'
  sed -nE 's/^public (def|theorem) ([A-Za-z0-9_]+).*/\2/p' \
    Proofs/Theorems/AdeleBoxThetaOperator.lean |
    while IFS= read -r name; do
      printf '#check @Masullo.%s\n#print axioms Masullo.%s\n' "$name" "$name"
    done
} > "$check"
lake env lean "$check"
```

The seven endpoint checks report only `propext`, `Classical.choice`,
`Quot.sound`. The following client is checked on a fresh scratch copy
with `lake env lean`. It uses a translated-box generator, obtains an
actual bound and sums, pulls continuity back from the class function,
and evaluates a complex linear combination on a different principal lift.

```lean
import Theorems.AdeleBoxThetaOperator

open IsDedekindDomain Masullo NumberField Set
open scoped Classical InnerProductSpace SchwartzMap

variable {K : Type*} [Field K] [NumberField K]
local notation "A" => AdeleRing (𝓞 K) K
local notation "F" => FiniteAdeleRing (𝓞 K) K
local notation "I" => IdeleGroup (𝓞 K) K
local notation "C" => IdeleClassGroup (𝓞 K) K
local notation "E" => mixedEmbedding.euclidean.mixedSpace K
local notation "d" => IdeleGroup.unitEmbedding (𝓞 K) K

example (φ : 𝓢(E, ℂ)) (a : F) (g : Fˣ) {B : Set I} (hB : IsCompact B) :
    ∃ R : ℝ, ∀ h ∈ B, (∑' b : Kˣ, ‖adeleBoxTensor φ a g (d b * h).val‖) ≤ R := by
  have hf := adeleBoxTensor_mem_adeleBoxSpan φ a g
  obtain ⟨M, hM, hle⟩ := exists_adeleBoxPrincipalMajorant hf hB
  refine ⟨∑' b, M b, fun h hh ↦ ?_⟩
  exact (summable_norm_adeleBoxPrincipal hf h).tsum_le_tsum (fun b ↦ hle b h hh) hM

example (φ : 𝓢(E, ℂ)) (a : F) (g : Fˣ) {B : Set I} (hB : IsCompact B) {h : I} (hh : h ∈ B) :
    HasSum (fun b : Kˣ ↦ adeleBoxTensor φ a g (d b * h).val)
      (adeleBoxThetaLinear (⟨_, adeleBoxTensor_mem_adeleBoxSpan φ a g⟩ : adeleBoxSpan K)
        (QuotientGroup.mk h : C)) ∧
    HasSum (fun b : Kˣ ↦ ‖adeleBoxTensor φ a g (d b * h).val‖)
      (∑' b : Kˣ, ‖adeleBoxTensor φ a g (d b * h).val‖) := by
  have hf := adeleBoxTensor_mem_adeleBoxSpan φ a g
  rw [adeleBoxThetaLinear_apply]
  exact ⟨(hasSumUniformlyOn_adeleBoxPrincipal hf hB).hasSum hh,
    (hasSumUniformlyOn_adeleBoxPrincipal_norm hf hB).hasSum hh⟩

example (φ : 𝓢(E, ℂ)) (a : F) (g : Fˣ) :
    Continuous fun h : I ↦ ∑' b : Kˣ, adeleBoxTensor φ a g (d b * h).val := by
  let f : adeleBoxSpan K := ⟨_, adeleBoxTensor_mem_adeleBoxSpan φ a g⟩
  have hc := (adeleBoxThetaLinear f).continuous.comp
    (QuotientGroup.continuous_mk (N := IdeleGroup.principalSubgroup (𝓞 K) K))
  convert hc using 1
  funext h
  exact (adeleBoxThetaLinear_apply f h).symm

example (φ ψ : 𝓢(E, ℂ)) (a : F) (g : Fˣ) (h : I) (u : Kˣ) (c : ℂ) :
    adeleBoxThetaLinear
        (c • (⟨_, adeleBoxTensor_mem_adeleBoxSpan φ a g⟩ : adeleBoxSpan K) +
          ⟨_, adeleBoxTensor_mem_adeleBoxSpan ψ a g⟩) (QuotientGroup.mk (d u * h) : C) =
      c * (∑' b : Kˣ, adeleBoxTensor φ a g (d b * h).val) +
        ∑' b : Kˣ, adeleBoxTensor ψ a g (d b * h).val := by
  let f : adeleBoxSpan K := ⟨_, adeleBoxTensor_mem_adeleBoxSpan φ a g⟩
  let k : adeleBoxSpan K := ⟨_, adeleBoxTensor_mem_adeleBoxSpan ψ a g⟩
  change adeleBoxThetaLinear (c • f + k) (QuotientGroup.mk (d u * h) : C) = _
  rw [map_add, map_smul, ContinuousMap.add_apply, ContinuousMap.smul_apply,
    adeleBoxThetaLinear_apply, adeleBoxThetaLinear_apply,
    adeleBoxPrincipalSum_invariant f.property u h, adeleBoxPrincipalSum_invariant k.property u h]
  rfl
```
