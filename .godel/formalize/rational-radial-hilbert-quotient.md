# Hardy–Sobolev completion of the divisor sequence: separated rational radial repair

Passage `ca025562bbc746aad3f3e5c0772d328a2ac0fc7b289d406421aba548476187f3`, revision `2aa04d22e5867a292f2a2bc2e3c6799d81afe3198a90de95e5e893aaffac5444`. See the [receipt](ca025562bbc746aad3f3e5c0772d328a2ac0fc7b289d406421aba548476187f3-2aa04d22e5867a292f2a2bc2e3c6799d81afe3198a90de95e5e893aaffac5444.json). Writer base `98737322ea237b5e8fbdd87a95b93f597f4a6d29`. The owning integration and review session is `01a205ed-8a99-78ff-8685-524624f8f56b`. That session, not the writer build, records the exact candidate and base, independent review, owning checks, and any adoption.

## Printed statement and gap

Edition: Masullo, *The Music of the Primes*. The writer checked the 6,756,996-byte PDF against SHA-256 `e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5` in the [source pin](../sources/masullo/README.md). The reading used the page rasters (including crop OCR) with `pdftotext -layout` to navigate and cross-check symbols that OCR dropped. At each cited location the printed page and one-based PDF ordinal coincide.

- **§1.2.1, p. 13/13, item (1).** After the introductory sequences and Mellin-jet discussion, the item announces taking the Hardy–Sobolev completion of all terms of the preceding linearly and topologically exact isotype sequence. The display is, with \(\omega=\chi|_{C_F^1}\) and the left completion denoted by \(W_I^{s,2}(-)\),
  \[
  0\longrightarrow W_I^{s,2}(|\cdot|_F^{1/2} H_{0,\mathrm{cont}}(\omega,\mathcal S_0(\mathbf A_F)))
     \longrightarrow W_I^{s,2}(C_F)(\omega)
     \longrightarrow W_I^{s,2}\mathscr H_F(\omega)
     \longrightarrow 0.
  \]
  All terms are asserted to be Hilbert. This item supplies no proof or separate description of separation of the quotient norm. The next lines choose a symmetric base of positive width and a support condition on a trace test; that support condition is not needed for the Hilbert construction here. No trace calculation or historical novelty claim is checked.
- **§1.1.4, p. 12/12, global theta and two-mode bullets; p. 434/434, (10.1.1.1)–(10.1.1.3).** Global theta is given by the sum over \(F^\times\); the restricted source uses \(f(0)=\widehat f(0)=0\). The maps on p. 434 send the theta quotient injectively as functions via multiplication by \(|\cdot|_F^a\), then into the weighted space; the text uses the induced norm. Definition 10.1.1.1(1) defines the resulting left completion as the closure of the twisted global range for a compact nonempty base and real \(s\ge0\). The subsequent local (10.1.1.4)–(10.1.1.5) are a different definition. At p. 13 the exponent of the norm twist is specifically \(1/2\).
- **Definition 9.2.2.9, p. 416/416, (9.2.2.31); Lemma 9.2.2.10(2), p. 417/417, (9.2.2.34).** For the canonical Haar measure and a compact base \([a,b]\), \(a\le b\), the square of the norm integrates \(|\phi(g)|^2\max(|g|_G^{2a},|g|_G^{2b})(1+|\log |g|_G|^2)^{s/2}\). The supremum over subintervals in (9.2.2.31) is attained at the whole interval because its integrand dominates that for each smaller interval; this includes the singleton in the compact formulation. The Sobolev exponent is real \(s\ge0\).
- **§10.2.2, p. 445/445, opening extension and (10.2.2.1)–(10.2.2.2).** The opening specifies a symmetric compact base \([-\alpha,\alpha]\) with \(\alpha\ge0\) and \(s\ge0\). It identifies the original right term with the corresponding test-space quotient, describes the completed term as a Hilbert quotient, and says that by the Open Mapping Theorem it is equivalently the normed completion for the induced quotient norm. The two labeled displays give the Hilbert quotient and its isotypic version; the latter also cites Lemma 4.3.3.1. This is not by itself a proof of separation of the original test-space quotient for the coarser norm.

In fact, if \(e:E\to H\) is the dense embedding and \(T\subset E\) is the original theta range, the norm-distance from \(e(u)\) to \(e(T)\) equals its distance to \(K=\overline{e(T)}^H\). Its zero classes in \(E/T\) are \(e^{-1}(K)/T\), not automatically just zero. For example, let \(E=\ell^1\subset\ell^2=H\) and take \(T\) to be the kernel of summation in \(\ell^1\). It is closed in the finer norm, but dense in \(\ell^2\): for a finite sequence of sum \(c\), add \(n\) new coordinates equal to \(-c/n\), at \(\ell^2\) cost \(|c|/\sqrt n\). Finite sequences are dense in \(H\). Thus \(E/T\ne0\) yet every class has distance zero. This example diagnoses a missing implication; it does not refute saturation for the manuscript's theta range.

## Checked repair and Lean bridges

[`Lemmas.HilbertDenseQuotient`](../../Proofs/Lemmas/HilbertDenseQuotient.lean) uses the continuous orthogonal projection onto \(e(T)^\perp=K^\perp\). Its kernel is the double orthogonal \(K\); it is onto because it fixes the complementary subspace. Its norm at \(y\) is the distance to \(K\), hence to \(e(T)\). Factor the composite with \(e\) by \(T\). The norm formula on representatives and linearity also give the corresponding formula for differences of classes. The kernel of this **descended** map is the pullback stated above by `ker_hilbertDenseQuotientMap`. Since the projection is continuous and onto, the image of \(e(E)\) is dense in the complete closed complement. This gives the separated completion with the quotient distance; it does not put a normed-space instance on the raw algebraic quotient. The Hilbert sequence for \(K\subset H\) is topologically split: the inclusion of the orthogonal complement is an isometric right inverse to the projection. The statements work even if \(K=H\) or \(K=0\); no nontriviality is imposed.

[`Theorems.RationalRadialHilbertQuotient`](../../Proofs/Theorems/RationalRadialHilbertQuotient.lean) specializes the construction to **\(F=\mathbb Q\), trivial norm-one character**:

1. `RationalThetaRadialInput` from [`RationalThetaRadialCore`](../../Proofs/Theorems/RationalThetaRadialCore.lean) is the submodule of the represented adelic LF test space with both original rational adelic zero modes zero and with *class theta* fixed by the rational norm-one subgroup. No band, test invariance or unramified representative restriction is added. `rationalThetaRadialProfile_class` recovers the class theta from its restriction to the log-norm section. Use the accepted [`RationalThetaWeightedStage`](../../Proofs/Theorems/RationalThetaWeightedStage.lean) image in the all-weight Schwartz coordinates. `rationalRadialThetaProfiles` inverts the linear equivalence from all-weight profiles onto that coordinate range; at weight zero, `rationalRadialThetaProfiles_apply` recovers exactly \(e^{x/2}\Theta(f)(\tau(x))\). Its test range \(T\) is the linear range of that map on the full represented source, not a closure.
2. The original radial middle model is `logWeightedProfiles univ`, smooth log profiles with every real exponential weight Schwartz. `rationalRadialHilbert` is the closure of the image of the accepted `logSobolevAllToLp` in `Lp ℂ 2 (logSobolevMeasure a b s)`. Agreement a.e. with the accepted endpoint-stage map gives injectivity on profiles; `logSobolev_commonCompletion` yields the same completion as the interval profiles. The target is a submodule with the restricted \(L^2\) norm and inner product and is complete since its carrier is closed. The two norm formulas in the new module use [`RadialHardySobolevCompletion`](../../Proofs/Theorems/RadialHardySobolevCompletion.lean) and the log-norm measure-preserving map from [`RationalIdeleClassHaar`](../../Proofs/Theorems/RationalIdeleClassHaar.lean). Thus \(dx\) in the log coordinate is exactly canonical rational class Haar on radial integrands, or \(dt/t\) on the positive axis, with no additional scalar. Hypotheses are \(a\le b\) and real \(s\); negative \(s\) is an extension, not needed for p. 13.
3. `rationalRadialThetaToHilbert_ae_eq` checks the precise half-twisted representative after the weighted inclusion. `rationalRadialThetaToHilbert_eq_zero_iff` combines the injective weighted inclusion and accepted stage kernel comparison: the kernel on LF tests is exactly the **original class-theta kernel**. `rationalRadialThetaHilbertRange_eq_range` identifies the submodule used in the projection as the image of the actual LF arrow. `exists_rationalRadialThetaClosureEmbedding` gives the left embedding modulo the original class-theta kernel with dense range and the prescribed image on every input class. Its target `rationalRadialThetaClosure` is complete in the induced Hilbert norm; the left source for this completion uses the norm pulled back from the weighted embedding, not a claim about its intrinsic LF quotient topology.
4. `rationalRadialQuotientProjection_exact` gives the ambient kernel \(K\) and surjectivity onto the complementary Hilbert space. `norm_rationalRadialQuotientMap_mk`, `ker_rationalRadialQuotientMap` and `rationalRadialQuotientMap_dense_complete` compute the original-class seminorm and its kernel, and give the dense map to a complete target. All maps use the same weighted Hilbert subspace. No informal assumption of density, saturation or algebraic-quotient separation is used in this instance.

## Residual obligation

This identifies the exact Hilbert terms and separated quotient in the radial **model**, not the intrinsic idelic Fréchet isotype quotient, the topology of the LF theta quotient, or the general field/character sequence. For norm separation, the precise retry is to lift an all-weight radial profile in the weighted closure back to one represented two-mode LF test with that profile, or to give a nonliftable profile in this pullback. Closedness in all-weight Schwartz seminorms would not suffice for this retry. For the intrinsic topology, the [rational weighted-theta handoff](rational-theta-weighted-stage.md) records a distinct finite-unit reduction and two-tail estimate to try, followed by continuity and quotient-topology checks; one also needs an equivariant idelic-to-profile comparison and compatible projectors on the original quotient. Other isotypes and fields need those source embeddings and the actual density bridge before invoking the generic mechanism. No statement here descends a trace operator or yields a spectral or RH/GRH conclusion.

## Reproduce the checks

From the integration workspace root use `lake build --wfail +Lemmas.HilbertDenseQuotient +Theorems.RationalRadialHilbertQuotient`. For each fully qualified name in the receipt, run `#check @Name` and `#print axioms Name` in a fresh scratch file with the two ordinary imports below. The writer's joint build used Lean 4.36.0 (8035 jobs); the joint import returned exactly `propext`, `Classical.choice`, and `Quot.sound` for each named declaration. No native computation, unchecked placeholder, or new axiom is used. The following ordinary-import client applies the maps to actual source classes, checks invariance of the original right class under addition of global theta, uses the distance to its actual LF range, and obtains a lift of a completed class unaffected by adding a completed theta vector. It also checks the singleton \(s=0\) case and the normalized Haar norm.

```lean
import Lemmas.HilbertDenseQuotient
import Theorems.RationalRadialHilbertQuotient

noncomputable section

open Function NumberField MeasureTheory Set Masullo
open scoped ENNReal

local notation "A" => AdeleRing (𝓞 ℚ) ℚ
variable [MeasurableSpace A] [BorelSpace A]
  [MeasurableSpace (A ⧸ rationalDiagonal)] [BorelSpace (A ⧸ rationalDiagonal)]

set_option maxHeartbeats 500000 in
example (s : ℝ) (f : RationalThetaRadialInput) (u : logWeightedProfiles univ) :
    let hab : (-1 : ℝ) ≤ 1 := by norm_num
    let T := rationalRadialThetaTestRange
    let q := rationalRadialQuotientMap hab s
    let Θ₀ := LinearMap.comp rationalAdeleClassThetaLFLinear rationalThetaRadialInputSubmodule.subtype
    (∃ g : (RationalThetaRadialInput ⧸ Θ₀.ker) →ₗ[ℂ] rationalRadialThetaClosure hab s,
      Injective g ∧ DenseRange g ∧
      (g (Θ₀.ker.mkQ f)).val = rationalRadialThetaToHilbert hab s f) ∧
    q (T.mkQ (u + rationalRadialThetaProfiles f)) = q (T.mkQ u) ∧
    ‖q (T.mkQ u)‖ = Metric.infDist (rationalRadialHilbertInclusion hab s u)
      (range (rationalRadialThetaToHilbert hab s)) := by
  intro hab T q Θ₀
  obtain ⟨g, hi, hd, hg⟩ := exists_rationalRadialThetaClosureEmbedding hab s
  refine ⟨⟨g, hi, hd, hg f⟩, ?_, norm_rationalRadialQuotientMap_mk hab s u⟩
  have ht : rationalRadialThetaProfiles f ∈ T := ⟨f, rfl⟩
  have hz : T.mkQ (rationalRadialThetaProfiles f) = 0 := (Submodule.Quotient.mk_eq_zero T).mpr ht
  rw [map_add, hz, add_zero]

-- A singleton and s=0 use the same ambient, theta space, and right-hand target.
example (f : RationalThetaRadialInput) :
    ((rationalRadialThetaToHilbert (le_refl (0 : ℝ)) 0 f).val : ℝ → ℂ) =ᵐ[logSobolevMeasure 0 0 0]
      fun x ↦ (Real.exp ((1 / 2 : ℝ) * x) : ℂ) * rationalThetaRadialProfile f x := by
  refine (rationalRadialThetaToHilbert_ae_eq (le_refl _) 0 f).trans ?_
  exact Filter.Eventually.of_forall (rationalThetaRadialTwistedProfile_apply _ f)

example : CompleteSpace (rationalRadialThetaClosure (le_refl (0 : ℝ)) 0) := inferInstance
example : InnerProductSpace ℂ (rationalRadialHilbertQuotient (le_refl (0 : ℝ)) 0) := inferInstance
example : CompleteSpace (rationalRadialHilbertQuotient (le_refl (0 : ℝ)) 0) :=
  (rationalRadialQuotientMap_dense_complete (le_refl _) 0).2

-- Surjectivity at Hilbert level supplies a lift, while it is only density on
-- the original right-hand classes. Theta closure is the ambient kernel.
example {a b : ℝ} (hab : a ≤ b) (s : ℝ) (z : rationalRadialHilbertQuotient hab s)
    (k : rationalRadialThetaClosure hab s) :
    ∃ y : rationalRadialHilbert hab s, rationalRadialQuotientProjection hab s (y + k.val) = z := by
  obtain ⟨hk, hs⟩ := rationalRadialQuotientProjection_exact hab s
  obtain ⟨y, hy⟩ := hs z
  have hmem : k.val ∈ (rationalRadialQuotientProjection hab s).ker := by
    rw [hk]
    exact k.property
  have hzero : rationalRadialQuotientProjection hab s k.val = 0 := LinearMap.mem_ker.mp hmem
  exact ⟨y, by rw [map_add, hzero, add_zero, hy]⟩

example [MeasurableSpace RationalIdeleClasses] [BorelSpace RationalIdeleClasses]
    {a b : ℝ} (hab : a ≤ b) (s : ℝ) (u : logWeightedProfiles univ) :
    ‖rationalRadialHilbertInclusion hab s (-u)‖ = Real.sqrt
      (∫ d : RationalIdeleClasses, logSobolevWeight a b s (Real.log (ideleClassNorm d)) *
        ‖u.val (Real.log (ideleClassNorm d))‖ ^ 2 ∂rationalIdeleClassHaar) := by
  rw [map_neg, norm_neg, norm_rationalRadialHilbertInclusion]
```
