# Translation on the rational real S-local theta quotient

Assignment `8180dbde73c3a521b0dd019dba1c70abb4c26aa3c5b9e1fd4eaba810723f7492`,
Walk revision `3a6b021e0b0ad6bdba255e27d613f75bcf5ef6b3e2aec010f54772c93fe0b7a8`.
Writer base `b22f627f46435575506d7f23195a469516f80312`. The owning Formalize
session `01a2058b-3662-7125-a67b-f5468c48cfae` records exact-candidate
integration, independent review, and adoption. This handoff records the
writer's checked partial result, not adoption.

[Receipt](8180dbde73c3a521b0dd019dba1c70abb4c26aa3c5b9e1fd4eaba810723f7492-3a6b021e0b0ad6bdba255e27d613f75bcf5ef6b3e2aec010f54772c93fe0b7a8.json) ·
[Translation module](../../Proofs/Theorems/RationalRealThetaTranslation.lean) ·
[Schwartz continuity](../../Proofs/Lemmas/SchwartzWeightedDilation.lean)

## Manuscript claim and proof route

The rendered source is Masullo's *The Music of the Primes*, edition SHA-256
`e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5` (verified
on the PDF bytes against `.godel/sources/masullo/README.md`). Each printed page
number here equals its one-based PDF ordinal. In particular the fifth bullet
of §1.1.4 (p. 12) names the isotypes for the restrictions of χ_S and χ to
`J_{F,S}^1` and `C_F^1`. The bullet asserts nuclear Fréchet, continuous left
translation by the **full** groups, and the consequent convolution actions
of their respective test-function algebras. This is not a claim about the
Hilbert-space completion. In the first bullet the ambient local space has
the intrinsic quotient topology; see Definition 2.3.1.1, p. 99, (2.3.1.1)–(2.3.1.2)
for the S-unit sum, and §2.3.1, pp. 99–100, for its descent to
`J_{F,S} = GL₁(A_{F,S}) / O_{F,S}ˣ`. Definition 5.2.2.1, p. 232,
(5.2.2.3)–(5.2.2.4) specifies the homogeneous-operator kernel quotients.

- Equations (5.2.3.5)–(5.2.3.6), p. 235, state continuity on products with the
  ambient spaces. Equations (5.2.3.7)–(5.2.3.8) define closed ω-eigenspaces for
  restricted actions, by `ρ(h, v) = ω(h)v` for every norm-one `h`. Because the
  full groups are abelian, their action on each ambient space preserves these
  subspaces. Preservation does not prove that the topology transferred from
  the homogeneous quotient is the subspace topology.
- Proposition 5.2.3.2(1), pp. 236–237, uses Pettis averaging for that
  topological identification. Its proof applies Lemma 4.3.3.1 to the twisted
  action, citing quasi-completeness from Theorem 5.2.1.1 and uniform continuity
  via the Mellin action. Pointwise diagonalization through a continuous
  injection alone would not control the intrinsic seminorms. A direct
  conditional argument is available: given joint continuity on the intrinsic
  space, compactness of the norm-one group gives, for each seminorm `p`, a
  neighborhood of zero on which `sup_h p(ρ(h)v) ≤ 1`, by the tube lemma at
  the compact set of pairs `(h, 0)`. The supremum is then a continuous
  seminorm; unitary twisting does not change it. Pettis averaging bounded by
  this seminorm gives a continuous operator. On the eigenspace this operator
  is multiplication by the Haar mass, so its induced map from its kernel
  quotient to its range has a continuous inverse given by dividing by the
  mass and passing to the quotient. This argument is not formalized here.
- Theorem 5.4.1.1(1)–(2), pp. 265–266, (5.4.1.2)–(5.4.1.3), claims that the
  local intrinsic homogeneous quotient embeds in the product of two
  half-plane Fréchet spaces with closed range given by agreement under a
  functional equation, and that the quotient is separable nuclear Fréchet.
  The proof at p. 274 uses the embedding for metrizability and cites Theorem
  5.2.3.1 for nuclearity. A strict LF presentation does not by itself imply
  metrizability. At pp. 295–297, Theorem 6.2.1.1 uses `Pic(O_{F,S}) = 1` and
  unramifiedness outside `S` for eventual surjectivity; the topological
  isomorphism also uses the previous stage embedding, not just surjectivity
  from an unspecified stage. Corollary 6.2.1.2 (pp. 295–296) chooses a large
  enough stage meeting these conditions and transfers the local result to
  the global isotype.
- Theorem C.4.3.5, p. 713, takes a locally compact Hausdorff domain, a **finite**
  complex Radon measure, a Hausdorff locally convex quasi-complete complex
  target, and a continuous compactly supported integrand. Thus on a Fréchet
  isotype with the claimed continuous action, a test function `a` gives a
  Pettis integral of `a(g)ρ(g)v` using Haar measure restricted to the compact
  support. The compact-parameter seminorm argument bounds the operator in
  the intrinsic topology. Continuous linear functionals commute with the
  integrals, and scalar Fubini and the action law give the convolution law
  (with Haar change of variables); the Hausdorff locally convex dual
  separates points. This is a conditional justification, not checked Lean
  evidence for either integrability or convolution.

### Conjugation and Haar mass are different issues

The rendered (5.2.3.9), p. 236, has an overbar on the weight `ω(g)` in **both**
operator integrals. The local (2.3.1.13), p. 105, uses `gh` with **unbarred**
`ω(h)`, as does the global (2.2.5.2), p. 95, with `hg`. The latter's proof
(p. 96) describes `hg` as the image of `g` translated on the left by `h⁻¹`;
what fixes the functional convention is the actual calculation on p. 97:
`Φ_{F,ω}(f)(h₀⁻¹g) = ω(h₀) Φ_{F,ω}(f)(g)`, with the inverse written in the
argument. The paragraph after (5.2.2.4), p. 232, also writes `ϕ(g⁻¹x)`.
For `ρ(g)ϕ(x) = ϕ(g⁻¹x)`, evaluating `ρ(h⁻¹)ϕ` at `x` gives `ϕ(hx)`
(and `ϕ(xh)` in the local abelian group). Thus Haar invariance under inversion
on the compact abelian norm-one group gives

```
(P_ω ϕ)(x) = ∫ conj(ω(g)) ϕ(g⁻¹x) dg = ∫ ω(h) ϕ(hx) dh.
```

Consequently, with the same measure, the local and global homogeneous theta
operators are `P_ω Φ`, **not** `P_(conj ω) Φ` as in the rendered subscripts in
the proof of (5.2.3.15) on p. 237 (both global and local). This is a repair of
the displayed identities, not a counterexample to the topological
isomorphism with consistent labels. For instance, on the circle, `ϕ(x) = x⁻¹`
has inverse-translation character `ω(g) = g`; normalized `P_ω` fixes it and
normalized `P_(conj ω)` annihilates it. This tests the convention and is not
an assertion about occurrence of that vector in a particular theta space.

Separately, for Haar mass `m > 0`, the operator of (5.2.3.9) satisfies
`P_ω² = m P_ω`; `P_ω/m` is the idempotent. This agrees with the normalization
clause of Corollary 4.3.3.3(2), p. 183. The nonzero scalar does not change the
kernel or range or prevent the induced topological isomorphism. For the
one-point norm-one group the sole character is trivial, the averaged theta
operator is `m Φ`, and this has the same kernel as `Φ`. These statements about
the manuscript averaging are mathematical audit notes, not Lean integration
or projection theorems in this candidate.

## Checked Lean result

Take `F = ℚ`, `S = {∞}`. The group is the actual quotient of the real units by
the image of integer units (not an arbitrary positive parameter substituted
for the quotient). Its norm is continuous by descent through the group
quotient map. The two possibilities `u = ±1` at `|u| = 1` are both accounted
for in the subgroup. The theorem `rationalRealLocalIdeleNorm_eq_one` gives
triviality of the norm-one subgroup. In this specialization the ambient
local theta quotient is the only norm-one isotype as explained above.

The underlying space is the existing `Masullo.RationalRealThetaQuotient` in
`Theorems.RationalRealThetaQuotient`, the quotient of `𝓢(ℝ, ℂ)` by the kernel
of `f ↦ (x ↦ f(x) + f(-x))` with `x` a real unit. This is the actual S-unit
sum; continuity at zero means extending the sum to all reals leaves its
kernel unchanged. The checked `rationalRealThetaEquiv` is a continuous linear
equivalence to the even Schwartz subspace, sending `[f]` to its unnormalized
symmetrization, with inverse `[v/2]`. See [real quotient handoff](rational-real-theta-quotient.md)
for the intrinsic Fréchet proof (`rationalRealThetaQuotient_frechet`) and
[character handoff](s-local-idele-character.md) for separate character descent
work. Neither is a proof of general isotype topology or nuclearity.

`Lemmas.SchwartzWeightedDilation` proves joint continuity of
`(s, b) ↦ exp(-s) • b(exp(-s) ·)` in the Schwartz topology. For each seminorm
of weight `a` and derivative order `d`, the dilation has local operator bound
`exp(|a-d-1|)` for `|s|≤1`. The derivative in `s` is the dilation of the
Schwartz generator `Gb = -b - x b'`, pointwise on the jets. Applying the
mean-value inequality yields
`p(U(s)b-b) ≤ exp(|a-d-1|) p(Gb) |s|` near zero. Combining these bounds gives
joint continuity near `(0,b)` for any `b`; the dilation composition law
and continuity of each fixed operator transfer this to every `s`.

`Theorems.RationalRealThetaTranslation` cancels the weight by multiplying by
`exp(s)`, takes `s = log ‖g‖`, restricts to the even subspace, and transports
through `rationalRealThetaEquiv` in both directions. The resulting operator
acts on even representatives by `v(x) ↦ v(‖g‖⁻¹ x)`; multiplicativity of the
norm yields the action laws. Continuity is on the product of the group and
the intrinsic quotient, not pointwise or separate continuity. Evenness
ensures descent of value evaluation in the idele argument; the result on
actual Schwartz representatives is `Θ(f)(u⁻¹ x)` for all real units `u,x`,
without a modular factor or a normalizing `1/2` in the forward theta map.

No larger local `S`, general number field, global translation, general
isotype identification, nuclearity, Pettis integrals or convolution actions
are established. Retry the general translation step with the actual
Schwartz–Bruhat LF stage maps and quotient descent (jointly continuous
representative translation plus open quotient maps would suffice). Then
check the compact-average quotient identification with the kernel computed
from the same-character identity. Nuclearity and the global comparison need
intrinsic-topology stage embeddings/nuclearity and the claimed eventual stage
isomorphisms. For the real endpoint, separate results on even Schwartz
nuclearity and compactly supported integration would suffice to extend the
scope. No ambient space has been changed to avoid these obligations.

## Replay

Run from the workspace for the exact candidate. Writer `lake build --wfail`
passed these targets together (8125 jobs):

```sh
lake build --wfail \
  +Lemmas.RationalAdeleLFStageOperators +Lemmas.SchwartzUniformDilation \
  +Lemmas.SchwartzWeightedDilation +Theorems.RationalAdeleDualPlancherel \
  +Theorems.RationalAdeleFourierInversion +Theorems.RationalAdeleFourierSupport \
  +Theorems.RationalAdeleFourierTestInversion +Theorems.RationalAdeleL1L2Fourier \
  +Theorems.RationalAdeleL2Fourier +Theorems.RationalAdeleLFFourierInversion \
  +Theorems.RationalAdeleLFFourierUniformDilation +Theorems.RationalAdeleRiemannLebesgue \
  +Theorems.RationalRealThetaQuotient +Theorems.RationalRealThetaTranslation \
  +Theorems.RationalThetaFiniteUnitAverage +Theorems.RationalThetaRadialCore \
  +Theorems.RationalThetaRadialCut
```

Produce `#check @…` and `#print axioms …` for all endpoints in the receipt
(and the existing Fréchet endpoint) in one ordinary-import file:

```sh
receipt=.godel/formalize/8180dbde73c3a521b0dd019dba1c70abb4c26aa3c5b9e1fd4eaba810723f7492-3a6b021e0b0ad6bdba255e27d613f75bcf5ef6b3e2aec010f54772c93fe0b7a8.json
check=$(mktemp --suffix=.lean)
{
  printf '%s\n' 'import Lemmas.SchwartzWeightedDilation' 'import Theorems.RationalRealThetaTranslation'
  jq -r '.evidence[].declarations[]' "$receipt" |
    awk '{print "#check @" $0; print "#print axioms " $0}'
  printf '%s\n' '#check @Masullo.rationalRealThetaQuotient_frechet' \
    '#print axioms Masullo.rationalRealThetaQuotient_frechet'
} > "$check"
lake env lean "$check"
```

Writer reports exactly `[propext, Classical.choice, Quot.sound]` for each
of the 18 new public endpoints and for the existing Fréchet endpoint. In
particular `rationalRealThetaTranslate : J → Q →L[ℂ] Q`, the continuity
statement is `Continuous (fun z : J × Q ↦ rationalRealThetaTranslate z.1 z.2)`,
and the ordinary-import instances have types `MulAction J Q` and
`ContinuousSMul J Q`. The binder sequence in `rationalRealThetaValue_smul_mkQ`
is `(u x : ℝˣ) (f : SchwartzMap ℝ ℂ)` with no additional hypotheses. Copy the
following to a separate fresh `.lean` file and run `lake env lean` on it.
The writer's run of this client passed. It exercises quotient representatives
and instance inference; the action-law test specifies the source semigroup
action type instead of leaving the implicit semigroup parameter of bare
`mul_smul` for elaboration.

```lean
import Theorems.RationalRealThetaTranslation

open Masullo
open scoped SchwartzMap

noncomputable def scaleTwo : ℝˣ := Units.mk0 2 (by norm_num)

example : rationalRealLocalIdele scaleTwo ≠ 1 := by
  intro h
  have hn := (rationalRealLocalIdeleNorm_eq_one _).mpr h
  norm_num [scaleTwo] at hn

example (f : 𝓢(ℝ, ℂ)) (x : ℝˣ) :
    rationalRealThetaValue (rationalRealLocalIdele scaleTwo • rationalRealTheta.ker.mkQ f)
        (rationalRealLocalIdele x) = f ((x : ℝ) / 2) + f (-(x : ℝ) / 2) := by
  rw [rationalRealThetaValue_smul_mkQ, rationalRealTheta_apply, Units.val_mul,
    Units.val_inv_eq_inv_val]
  change f ((2 : ℝ)⁻¹ * (x : ℝ)) + f (-((2 : ℝ)⁻¹ * (x : ℝ))) = _
  simp only [div_eq_mul_inv, neg_mul, mul_comm (x : ℝ)]

example {X : Type*} [TopologicalSpace X] (g : X → RationalRealLocalIdeleGroup)
    (q : X → RationalRealThetaQuotient) (hg : Continuous g) (hq : Continuous q) :
    Continuous (fun t ↦ g t • q t) :=
  continuous_smul.comp (hg.prodMk hq)

example (g h : RationalRealLocalIdeleGroup) (q : RationalRealThetaQuotient) :
    (g * h) • q = g • (h • q) :=
  (inferInstance : SemigroupAction RationalRealLocalIdeleGroup RationalRealThetaQuotient).mul_smul
    g h q

example (g : RationalRealLocalIdeleGroup) (q : RationalRealThetaQuotient)
    (hg : rationalRealLocalIdeleNorm g = 1) : g • q = q := by
  rw [(rationalRealLocalIdeleNorm_eq_one g).mp hg, one_smul]

example (g : RationalRealLocalIdeleGroup) (q r : RationalRealThetaQuotient) :
    g • (q + r) = g • q + g • r := by
  simp only [rationalRealTheta_smul_eq_translate, map_add]
```
