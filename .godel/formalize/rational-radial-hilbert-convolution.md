# Bounded convolution on the rational radial theta quotient

Chapter 01, passage `f3c1b67400b3d180a586a682ceec1a8b140f9f1480d372e489b4f455be29f4da`, proof revision `80bba492258d64988564cb13bf3138c3a60eb8d9a2866a8c1a7d268b558c2a73`. [Receipt](f3c1b67400b3d180a586a682ceec1a8b140f9f1480d372e489b4f455be29f4da-80bba492258d64988564cb13bf3138c3a60eb8d9a2866a8c1a7d268b558c2a73.json). Writer base `777c661f54b612d4d69309a45b16c07e62a4122b`; owning integration session `01a20612-a8bd-7cd1-ba3b-e1d2b7c6397c`. The integration handoff, not this writer report, records the checked candidate/base, independent verdict and adoption.

## Source and proof scope

Masullo, *The Music of the Primes*, 940 pages, 6,756,996 bytes. The PDF's SHA-256 was checked against the [edition pin](../sources/masullo/README.md): `e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5`. Printed page equals PDF ordinal at all locators below. The reading uses rendered page rasters and crop OCR, with direct pixel crops for the main integral, boundary multiplicity, and degree comparisons; layout extraction is for navigation and notation cross-checks.

- **§1.2.1(1)–(2), pp. 13–14.** Choose a symmetric base of positive width and a test supported strictly above norm one (above \(1+\epsilon\) for some positive \(\epsilon\)). The displayed degree-zero expression sums \(N(\rho)\mathcal M(\phi)(\chi|\cdot|_F^{\rho-1/2})\) over zeros whose shifts lie in the interior of the strip. At positive degree p. 13 also asserts edge contributions, printing a **max** of \(N(\rho)\) and the bracketed \((s-1)/2\); compare the **min** cap using the bracket plus one in (10.3.2.4) on p. 454. No identification of these prescriptions is used. The first paragraph on p. 14 defines \((A(\phi)\psi)(x)=\int_{C_F}\phi(g)\psi(g^{-1}x)\,d\mu(g)\). It says this acts on the exponentially decaying test space, its isotypes and weighted completions, preserves the completed theta space and descends to the completed quotient isotype; it then claims the descended operator is nuclear and the p. 13 sum is its trace. Only bounded action and descent in a rational radial specialization are checked here. The following discussion of Schauder bases and trace-norm expansion is separate.
- **Definition 9.3.1.1 (9.3.1.1)–(9.3.1.2), p. 419; Lemma 9.3.1.3, pp. 419–420.** These are the Pettis regularization of left translation in the complete ambient spaces and the continuity statement for the kernel-to-operator map with the indicated locally convex topologies. The Bochner integral below gives the Hilbert-valued regularization for the specified kernels; continuity in those source topologies is not asserted.
- **Definition 10.1.1.1, p. 434; Lemma 10.1.1.3(2), p. 435, with (10.1.1.6).** The subspace is the closure of the twisted global theta image in the ambient weighted norm. The lemma asserts invariance by left translation, compatible with the action induced by adelic test translation. Its brief proof describes closedness and the norm; closedness alone would not give invariance. The proof here checks the actual test-level dilation and the scalar correction first, then uses closedness. **§10.2.2, p. 445, (10.2.2.1)–(10.2.2.2)** displays the Hilbert quotient and its isotypic version; see the accepted [quotient handoff](rational-radial-hilbert-quotient.md) for the separation issue in the original quotient seminorm.
- **Theorem 10.4.2.1, p. 459, (10.4.2.3)–(10.4.2.8).** It assumes \(s\ge0\) and a symmetric nonempty base, includes the untruncated projection-after-convolution \(P_a^{\rm spec}A(\phi)\) in its nuclearity assertion, and writes it as \(S_a A_a^{\rm spec}(\phi)Q_a\) in (10.4.2.5). In that proof the nuclearity input is (10.3.1.2) of Theorem 10.3.1.1, p. 448, the singleton result with **\(s>1\)**. The interval Theorem 10.3.2.1, pp. 453–455, also assumes **\(s>1\)**; its operator and trace on p. 454 are (10.3.2.2)–(10.3.2.5). Neither invocation provides the introductory degree-zero trace. This comparison is a gap in the cited argument's scope, not a counterexample to the trace claim.

## Checked construction

Use the actual middle term \(H=\texttt{rationalRadialHilbert}\), the closure \(K=\texttt{rationalRadialThetaClosure}\) of the global half-twisted theta image, and the existing separated quotient \(K^\perp=\texttt{rationalRadialHilbertQuotient}\) with projection \(P\). Work over \(\mathbb Q\), in the trivial norm-one isotype, with symmetric base \([-\alpha,\alpha]\), \(\alpha\ge0\), real \(s\ge0\). In particular, no singleton or positive-degree hypothesis restricts the checked result.

1. [`Theorems.RationalRadialHilbertTranslation`](../../Proofs/Theorems/RationalRadialHilbertTranslation.lean) defines \(T_yv(x)=v(x-y)\) on the dense all-weight profiles. For the square root \(r(x)=e^{\alpha|x|}(1+x^2)^{s/4}\) of the weight, \(r(x+y)\le 2^{s/4}r(y)r(x)\); this uses \(|x+y|\le|x|+|y|\) and \(1+(x+y)^2\le2(1+x^2)(1+y^2)\). It gives the operator-norm bound via translation invariance of \(dx\) and bounded extension. Compactly supported profiles are dense by the accepted profile cutoff approximations. Dominated convergence on each compactly supported profile and the locally uniform operator bound then give strong continuity on \(H\).
2. `rationalRadialProfileTranslate_theta` checks the sign and half twist on the accepted `RationalThetaRadialInput`. The underlying LF test dilation at \(-y\) translates the *untwisted* theta by \(x\mapsto x-y\), preserves the two zero modes and the trivial norm-one isotype. Thus \(T_y(e^{x/2}\Theta f)=e^{x/2}\Theta(e^{-y/2}D_{-y}f)\). The completed theta subspace is invariant and projection intertwines translation on **all** ambient lifts, not only on the chosen complement.
3. [`Theorems.RationalRadialHilbertConvolution`](../../Proofs/Theorems/RationalRadialHilbertConvolution.lean) integrates \(\phi(y)T_yu\) in \(H\) for continuous compactly supported \(\phi:\mathbb R\to\mathbb C\). The integrand is continuous with compact support. Its integrated norm is bounded by \(\|u\|\int |\phi(y)|2^{s/4}r(y)\,dy\). Radial class tests are \(g\mapsto\phi(\log|g|)\). The canonical rational class Haar pushes forward under \(\log|\cdot|\) to Lebesgue measure (unit mass on the norm-one factor); `rationalRadialHilbertConvolution_haar` checks the equality of the Hilbert-valued integrals. This includes the smooth supported radial tests of the introduction without using the support-above-one condition for boundedness.
4. With inclusion \(i:K^\perp\hookrightarrow H\), define the bounded operator \(A_q=PAi\). For every \(u\in H\), `rationalRadialQuotientConvolution_projection` gives \(A_qPu=PAu\) by commuting \(P\) with the integral and applying the pointwise translation identity. Consequently `rationalRadialHilbertConvolution_mem_thetaClosure` gives \(A K\subseteq K\). This is the bounded part of the projection-after-convolution factorization, not any trace-ideal assertion.

## Remaining work

For general class tests on this isotype, compare the class integral with convolution by the norm-one Haar average and establish its radial support and regularity. To move beyond the separated model or to other fields/isotypes, supply equivariant comparisons with their actual test, weighted and theta spaces. Even on this same radial Hilbert quotient and a supported radial test at \(s=0\), boundedness does not imply compactness or trace class. The next spectral input is a joint-kernel identification for the continuous interior zero jets on the *actual* quotient, with justified edge treatment, plus a trace-norm summable approximation or trace-ideal factorization of this convolution, not just individual Mellin multipliers. Then the finite-dimensional block traces must exhaust the operator trace. See the [degree-zero audit](../walk/degree-zero-narrow-strip-spectral-trace.md) and [spectral audit](../obligations/trace-spectral.md); the [positive-degree repair](../obligations/trace-spectral-strip-q.md) does not provide those inputs in degree zero. The toy [Poisson correction](../walk/toy-poisson-normalization.md) and [support vanishing](../walk/toy-trace-support-vanishing.md) are scalar results, not quotient or operator trace results. The accepted unweighted singleton convolution and the fixed-annulus calculation are on different spaces; neither supplies that spectral comparison. No RH/GRH claim follows.

## Reproduce the checks

Build `lake build --wfail +Theorems.RationalRadialHilbertTranslation +Theorems.RationalRadialHilbertConvolution`. Then use `lake env lean` on a fresh file with the following ordinary imports and a `#check @Name` and `#print axioms Name` for each fully qualified name in the receipt. On the writer workspace both modules built with warnings fatal (8039 jobs), each cited endpoint used only `propext`, `Classical.choice` and `Quot.sound`, and the following client compiled. Run this separate ordinary-import client, which applies the projection and Haar identities at a **positive** width and **zero** degree to a change of lift by the actual LF theta arrow, and checks the dense-profile translation sign.

```lean
import Theorems.RationalRadialHilbertTranslation
import Theorems.RationalRadialHilbertConvolution

noncomputable section

open Masullo MeasureTheory NumberField Set

local notation "A" => AdeleRing (𝓞 ℚ) ℚ
local notation "hα" => (zero_le_one : (0 : ℝ) ≤ 1)
local notation "hs" => (le_refl (0 : ℝ))
local notation "hab" => (neg_le_self hα)

variable [MeasurableSpace A] [BorelSpace A]
  [MeasurableSpace (A ⧸ rationalDiagonal)] [BorelSpace (A ⧸ rationalDiagonal)]
  [MeasurableSpace RationalIdeleClasses] [BorelSpace RationalIdeleClasses]

-- A genuine change of lift by a global theta profile. The right side applies
-- the class-Haar convolution to the original lift and then projects it.
example {φ : ℝ → ℂ} (hφ : Continuous φ) (hc : HasCompactSupport φ)
    (v : logWeightedProfiles univ) (f : RationalThetaRadialInput) :
    let P := rationalRadialQuotientProjection hab 0
    let u := rationalRadialHilbertInclusion hab 0 v
    let k := rationalRadialThetaToHilbert hab 0 f
    rationalRadialQuotientConvolution hα hs hφ hc (P (u + k)) =
      P (∫ g : RationalIdeleClasses, φ (Real.log (ideleClassNorm g)) •
        rationalRadialHilbertTranslate hα hs (Real.log (ideleClassNorm g)) u
          ∂rationalIdeleClassHaar) := by
  intro P u k
  have hk : k ∈ rationalRadialThetaClosure hab 0 := by
    change k ∈ closure (rationalRadialThetaHilbertRange hab 0 : Set _)
    apply subset_closure
    rw [rationalRadialThetaHilbertRange_eq_range]
    exact ⟨f, rfl⟩
  have hz : P k = 0 := by
    rw [← (rationalRadialQuotientProjection_exact hab 0).1] at hk
    exact LinearMap.mem_ker.mp hk
  rw [map_add, hz, add_zero, rationalRadialQuotientConvolution_projection,
    rationalRadialHilbertConvolution_haar]

-- The same dense lift is acted on with the inverse sign, not the forward sign.
example (y x : ℝ) (v : logWeightedProfiles univ) :
    ∃ w : logWeightedProfiles univ, w.val x = v.val (x - y) ∧
      rationalRadialHilbertTranslate hα hs y (rationalRadialHilbertInclusion hab 0 v) =
        rationalRadialHilbertInclusion hab 0 w := by
  exact ⟨rationalRadialProfileTranslate y v, rationalRadialProfileTranslate_apply y v x,
    rationalRadialHilbertTranslate_inclusion hα hs y v⟩
```
