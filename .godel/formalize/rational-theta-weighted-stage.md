# Fundamental divisor sequences: the rational radial weighted arrow

This is a **partial** result for §1.2.1, not a closed-range theorem. For the unrestricted sequence the main missing bridge is a simultaneous preimage: a limit in the weighted class-function space must be the theta of **one** two-mode adelic Schwartz–Bruhat test in the LF union. A solution for each angular projection is not such a test. Even for a single isotype, continuity of the inclusion and the topology on its image are separate from defining the arrow.

## Printed claim and proof scope

Edition: *The Music of the Primes*, SHA-256 `e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5`, as in the [source pin](../sources/masullo/README.md). Page references below give printed page/PDF ordinal (one-based). The digest, rasterized pages and display crops were checked; text extraction is a finding aid.

- **§1.2.1, p. 13/13, opening paragraph and its first two displays.** For a number field \(F\), writing \(\omega=\chi|_{C_F^1}\), the sequences are

  \[
  0\longrightarrow |\cdot|_F^{1/2}H_{0,\mathrm{cont}}(F^\times,\mathcal S_0(\mathbf A_F))
   \longrightarrow \mathcal S_{\mathrm E}(C_F)\longrightarrow \mathscr H_F\longrightarrow0,
  \]

  \[
  0\longrightarrow |\cdot|_F^{1/2}H_{0,\mathrm{cont}}(\omega,\mathcal S_0(\mathbf A_F))
   \longrightarrow \mathcal S_{\mathrm E}(C_F)(\omega)\longrightarrow \mathscr H_F(\omega)\longrightarrow0.
  \]

  The introductory text specifies Hausdorff locally convex spaces, calls the isotypic terms nuclear Fréchet, and below the Mellin-jet display refers back to the isotype sequence as linearly and topologically exact. The distinct Mellin-jet and Hardy–Sobolev sequences are not the obligation here. These claims are announced, not proved in the opening paragraph.
- **§1.1.4, p. 12/12, third through fifth bullets; §6.3.2, p. 304/304, definitions following (6.3.2.5).** The global theta is \(\Phi_F(f)(g)=\sum_{q\in F^\times}f(qg)\); the two modes are \(f(0)\) and \(\widehat f(0)\). The intrinsic restricted-source topology is the quotient topology of \(\mathcal S_0\) by the restricted theta kernel, not a subspace topology taken in the eventual target. The unrestricted source and homogeneous sources use the kernels of their respective theta operators.
- **Def. D.3.3.1, p. 804/804; Def. D.3.3.3, p. 805/805, (D.3.3.1)–(D.3.3.2); Rem. D.3.3.6, p. 806/806.** All real norm weights must give Schwartz–Bruhat functions. On a fixed angular-invariance stage the topology is induced by the weighted coordinates; the full topology is an inductive limit over stages, not established just by embedding a fixed stage into the product of weighted Schwartz spaces. The radial stage has angular quotient a point, so in the log coordinate each factor is ordinary Schwartz on \(\mathbb R\). Norm multiplication by \(|\cdot|^b\) reindexes weights by \(a\mapsto a+b\); it is a topological automorphism in the all-weight case. Thus the p. 13 arrow uses total exponent \(a+1/2\) at ambient weight \(a\). The unshifted quotient in (7.1.4.7), p. 327/327, is to be compared using this automorphism, not by omitting the half twist from p. 13.
- **Def. 2.2.5.1, p. 95/95, (2.2.5.2); Prop. 5.2.3.2, pp. 235–237/235–237; Prop. D.3.3.12, pp. 811–812/811–812, (D.3.3.10).** The homogeneous theta uses the integral of \(\Phi_F(f)(hg)\omega(h)\). For the inverse-left action \((k\varphi)(g)=\varphi(k^{-1}g)\), substitution \(h=h'k\) gives the same eigencharacter \(\omega(k)\), not its inverse. Passing to the isotype of a quotient requires actual continuous equivariant projectors respecting the theta image; a character-by-character formula alone is not that topology check. For the trivial character used here this convention reduces to ordinary invariance.
- **Thm. 6.3.2.1(1), pp. 304–307/304–307, (6.3.2.3)–(6.3.2.4); Thm. D.3.3.13, pp. 812–813/812–813, (D.3.3.11)–(D.3.3.12).** The cited argument is at *one fixed* unitary character in the coordinate \(\chi|\cdot|^s\). It chooses a sufficiently large finite place set, uses a local structural image multiplied by missing Euler factors, and argues closed range by dividing the two half-plane limits using reciprocal growth on suitable segments and gluing the limits. The Mellin transform of the half-twisted image evaluates the untwisted transform at \(s+1/2\). The line on p. 306 that cites Hausdorffness to infer closed range of the two restriction maps together is not a valid reason; the appropriate check there is the description as the equalizer of the two restrictions to the overlap, with holomorphic gluing and the strip seminorms bounded by the two restrictions' seminorms. This does not address a simultaneous LF lift. The nontrivial norm-one character uses the full homogeneous source since the norm-one invariant zero-mode functionals vanish there (p. 304, (6.3.2.2) and following sentence); the trivial case uses the restricted source and descent by its kernel. In particular do not use (6.3.2.5) literally with an onto \(\mathbb C^2\) in the nontrivial case: its stated two functionals vanish there, and (6.3.2.7) instead shows the identity of the two Mellin images.
- **Thm. 6.2.1.1(2) and Cor. 6.2.1.2, pp. 295–296/295–296.** The argument for nuclear Fréchet source isotypes is eventual comparison, for that one character, with a sufficiently large finite-place homogeneous quotient. A result of this shape needs the topological identification, not just a surjection from finite-place tests. See the [real quotient audit](rational-real-theta-quotient.md) for the scope and the gap in inferring strict transitions from closed kernels alone.

## Checked specialization

In [`Theorems.RationalThetaRadialCore`](../../Proofs/Theorems/RationalThetaRadialCore.lean), `RationalThetaRadialInput` is the submodule of represented rational adelic LF tests with **both** zero modes zero and **class theta** invariant under `rationalIdeleClassNormOne`. No finite-place truncation or invariance of the test itself is imposed. `exists_rationalAdeleLF_of_compactOpenStage` explains the cofinal box model; `rationalThetaRadialProfile_class` gives the theta value on every class from the positive-real log section. The accepted `range_rationalAdeleClassThetaFiniteUnitAverage` in [`Theorems.RationalThetaFiniteUnitAverage`](../../Proofs/Theorems/RationalThetaFiniteUnitAverage.lean) identifies this algebraic image with the finite-unit averaged image of all represented two-mode tests; `rationalAdeleLFFiniteUnitAverage_zero_modes` checks preservation of both modes. Neither declaration identifies intrinsic quotient topologies.

[`Theorems.RationalThetaWeightedStage`](../../Proofs/Theorems/RationalThetaWeightedStage.lean) proves:

- `Masullo.rationalThetaRadialWeightedProfiles` and `Masullo.rationalThetaRadialWeightedStage`: linear realizations of the actual half-twisted radial theta into, respectively, all-weight smooth profiles and `logWeightedStage univ`, the range submodule in the product of ordinary complex Schwartz spaces with its induced topology. `Masullo.rationalThetaRadialWeightedStage_apply` gives its real weight coordinate pointwise. In the dependence on the Fourier convention there is no choice of a new zero-mode functional: `Masullo.rationalThetaRadialInput_zero_modes` exposes the original rational adelic evaluations, and `Masullo.rationalThetaRadialTwistedProfile_apply` exposes the exact twist.
- `Masullo.rationalThetaRadialWeightedStage_uniform_seminorm`: for each real weight \(a\), derivative order \(n\), and polynomial degree \(k\), the corresponding Schwartz seminorm has a common bound on each von Neumann bounded family of radial inputs in the subspace topology of the LF test space. In log coordinates the derivative of \(e^{bx}\Phi(f)(\tau(x))\) is the same expression with \(f\) replaced by \((D+b\,\mathrm{id})f\). The continuous dilation generator \(D\) preserves both zero modes (see `rationalAdeleLFDilationDeriv_preserves_zero_modes`); iteration preserves bounded families and the vanishing. The accepted `rationalAdeleLF_uniform_theta_log_bound` applied to this new family gives the arbitrary integer log-exponential rate. Take \(m\ge |b|+1\) and use \(|x|^k\le k!e^{|x|}\), with \(b=a+1/2\). This supplies actual derivative seminorm bounds, unlike a pointwise bound alone.
- `Masullo.rationalThetaRadialWeightedStage_eq_zero_iff`: zero in the weighted realization is equivalent to zero **class theta**, not zero input, nor zero against a support cutoff or in an \(L^2\) band. Evaluation at weight zero and division by the nonvanishing half twist recovers the log profile; invariance recovers the function on all classes. This gives the kernel needed for an algebraic quotient injection. It does **not** assert an identification of topologies or closedness. The accepted [radial Fréchet construction](radial-weighted-frechet.md) applies to the **ambient** stage, not to the image; it does not prove nuclearity.

## Remaining bridge and retry

For the rational trivial isotype, a concrete direct check would be an estimates-based closed-range proof. Use the accepted finite-unit averaging, then show in Lean that each finite-unit invariant stage test reduces, **in class theta and preserving both zero modes**, to an even real Schwartz profile \(b\otimes\mathbf1_{\widehat{\mathbb Z}}\). Classically the finite ball indicators span each fixed stage's finite-unit invariants: their differences give the valuation strata within the support and the deepest ball. Replace each rational finite ball by the unit ball using rational scaling, with the accompanying real rescaling. The even projection uses reindexing by \(-1\); it preserves evaluation at zero and the integral. An arbitrary coordinate projection need not preserve the theta kernel. One needs this actual reduction, not density of these special theta functions in a completion.

At that point the following is a candidate tail estimate, not a checked theorem. Put \(h_b(t)=\sum_{n\ge1}b(nt)\) for \(t>0\) (the class theta is twice this for the even unramified test). For \(r>0\) and \(M>j+1\) so large that \(\sigma=\sum_{n\ge2}n^{j-M}<1\), differentiate the series and isolate its \(n=1\) term. This gives

\[
(1-\sigma)\sup_{t\ge r}t^M|b^{(j)}(t)|\ \le\ \sup_{t\ge r}t^M|h_b^{(j)}(t)|.
\]

The same bounds for \(\widehat b\) follow from \(h_{\widehat b}(t)=t^{-1}h_b(1/t)\) by the **two-mode** Poisson formula, and conversion of \(t\)-derivatives into log derivatives and weights. Choose \(0<r<1/2\). In the self-dual Fourier normalization, the inequalities \(\|b\|_\infty\le 2r\|\widehat b\|_\infty+\int_{|t|\ge r}|\widehat b(t)|\,dt\) and the converse with \(b,\widehat b\) swapped can be combined and solved since \((2r)^2<1\). Weighted Fourier \(L^1\) bounds then give the compact-interval derivative bounds. The intended conclusion is a continuous inverse estimate into the *even two-mode Schwartz* source, so that an ambient limit gives an actual representative by completeness. Forward continuity from the intrinsic quotient must be checked too; a bounded map on a subspace of a strict LF space is not shown continuous just by the bounded-family estimate here.

For the full LF problem, a useful discriminator is an actual continuous fixed-stage angular averaging retraction commuting with theta from some allowed source stage, together with closed isotype embeddings and a check that stage limits lift simultaneously. When the angular quotient of a stage is finite, summing finitely many compatible character lifts in a common larger stage is a possible algebraic lifting argument; one must still verify continuity and the final/quotient topologies. With infinitely many characters, closedness for each character alone is insufficient: in the smooth-torus angular model the finite Fourier sums are dense and proper, even though every single mode space is closed. This example does not refute the number-field claim. Nor does it address finite/profinite stages satisfying the required finite quotient and retraction properties. To get topological exactness and nuclear Fréchet isotypes also verify the descended averaging projectors and completeness/nuclearity on the specific quotient topology. No trace, zero-location, RH, or GRH conclusion follows.

## Reproduce the Lean checks

- **Owning integration checks:** Yah session `01a205b2-d8c2-7631-849d-f6f2786a2cfb` holds the exact-candidate build, ordinary-import client, signature and axiom results. This pointer is not a record of independent review or adoption.
- **Writer checks:** in the same session, writer `dispatch-NHqJXIJ`, task `p8`, ran the warning-free build and the ordinary-import client below on the work finalized as `391060cb1fab9bb7922ed4f7d632712926eab021`. The reproduction command also includes the affected importers checked at integration.

In the campaign integration workspace root:

```sh
lake build --wfail \
  +Theorems.RationalThetaRadialCore +Theorems.RationalThetaWeightedStage \
  +Theorems.RadialWeightedSchwartzFrechet +Theorems.RationalThetaFiniteUnitAverage \
  +Theorems.RationalThetaRadialCut +Theorems.RationalThetaAverageFourierZero
# Paste the following Lean block into a fresh scratch file:
lake env lean /tmp/WeightedThetaClient.lean
```

The seven axiom reports must each list only `propext`, `Classical.choice`, and `Quot.sound`. The applications recover a Schwartz representative for the **untwisted** theta on all classes (by choosing weight \(-1/2\)), recover equality of two raw class-theta functions from equality of the ordinary Schwartz coordinates, and get a uniform derivative seminorm bound at positive weight.

```lean
import Theorems.RationalThetaWeightedStage
import Theorems.RadialWeightedSchwartzFrechet

open Masullo NumberField MeasureTheory Bornology Set
open scoped SchwartzMap

#check @rationalThetaRadialInput_zero_modes
#check @rationalThetaRadialTwistedProfile_apply
#check @rationalThetaRadialWeightedProfiles
#check @rationalThetaRadialWeightedStage
#check @rationalThetaRadialWeightedStage_apply
#check @rationalThetaRadialWeightedStage_uniform_seminorm
#check @rationalThetaRadialWeightedStage_eq_zero_iff
#print axioms rationalThetaRadialInput_zero_modes
#print axioms rationalThetaRadialTwistedProfile_apply
#print axioms rationalThetaRadialWeightedProfiles
#print axioms rationalThetaRadialWeightedStage
#print axioms rationalThetaRadialWeightedStage_apply
#print axioms rationalThetaRadialWeightedStage_uniform_seminorm
#print axioms rationalThetaRadialWeightedStage_eq_zero_iff

local notation "A" => AdeleRing (𝓞 ℚ) ℚ
local notation "E" => RationalAdeleSchwartzLF
local notation "C" => IdeleClassGroup (𝓞 ℚ) ℚ
set_option linter.concreteInstances false
variable [MeasurableSpace A] [BorelSpace A]
variable [MeasurableSpace (A ⧸ rationalDiagonal)] [BorelSpace (A ⧸ rationalDiagonal)]

-- Obtain a Schwartz representative at weight -1/2 which reads the unshifted
-- theta on EVERY idele class, not just at the section.
example (f : RationalThetaRadialInput) :
    ∃ b : 𝓢(ℝ, ℂ), ∀ d : C,
      b (Real.log (ideleClassNorm d)) = rationalAdeleClassTheta f.val.toUnion.val d := by
  let a : (univ : Set ℝ) := ⟨-(1 / 2), mem_univ _⟩
  refine ⟨(rationalThetaRadialWeightedStage f).val a, fun d ↦ ?_⟩
  rw [rationalThetaRadialWeightedStage_apply, rationalThetaRadialTwistedProfile_apply,
    logStageWeight, ← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add,
    rationalThetaRadialProfile_class]
  dsimp only [a]
  rw [neg_mul, neg_add_cancel, Real.exp_zero, Complex.ofReal_one, one_mul]

-- Equality of the ordinary Schwartz coordinate families implies equality of
-- raw class theta on all classes, not an equality of L² classes.
example (f g : RationalThetaRadialInput)
    (h : ∀ a : (univ : Set ℝ), (rationalThetaRadialWeightedStage f).val a =
      (rationalThetaRadialWeightedStage g).val a) :
    rationalAdeleClassThetaLFLinear f.val = rationalAdeleClassThetaLFLinear g.val := by
  have hW : rationalThetaRadialWeightedStage (f - g) = 0 := by
    rw [map_sub, sub_eq_zero]
    exact Subtype.ext (funext h)
  have hΘ := (rationalThetaRadialWeightedStage_eq_zero_iff (f - g)).mp hW
  change rationalAdeleClassThetaLFLinear (f.val - g.val) = 0 at hΘ
  rwa [map_sub, sub_eq_zero] at hΘ

-- A bounded family really has a common bound for a derivative seminorm at a
-- nonzero weight. No stage index or continuity premise is supplied by the client.
example (B : Set RationalThetaRadialInput) (hB : IsVonNBounded ℂ B) :
    ∃ c : ℝ, ∀ f ∈ B,
      SchwartzMap.seminorm ℂ 3 2 ((rationalThetaRadialWeightedStage f).val
        ⟨4, mem_univ _⟩) ≤ c := by
  obtain ⟨c, _, hc⟩ := rationalThetaRadialWeightedStage_uniform_seminorm
    ⟨4, mem_univ _⟩ 3 2 hB
  exact ⟨c, hc⟩
```
