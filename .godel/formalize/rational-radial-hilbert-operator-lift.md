# Orthogonal lift of regularized rank-one quotient operators

Chapter 01, passage `966710b2b42724e837d4a12b2803ef93b1f680fb2d2e51c272ea13c0b84fb5b6`, proof revision `fb2cad7bdaa6d0f0a8d4fa317e300f8f02d74e842fc6730be7de8405e4ddf893`. Writer base `1321b109cb8c361d1829a537e4991c6ab96df386`; the request's earlier accepted tip `0c1d5fcef0853fb9f213253b7f60dbd15173c8f9` differs only by seven unrelated Gaussian/positive-bump lemmas. Owning check session: `01a2065e-0f3d-7ec8-9a55-f03c0c1f9642`. The owning session records integrated candidate/base, independent review, exact landing checks and any adoption, not this writer report.

## Rendered source and scope

Verified the local 6,756,996-byte copy of Masullo, *The Music of the Primes*, against [the edition pin](../sources/masullo/README.md): SHA-256 `e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5`. Read the rendered page rasters via OCR with focused display crops; checked the pixels of the critical inequalities separately, using layout extraction for navigation and notation cross-checks. Each locator below gives printed page / one-based PDF ordinal.

- **§1.2.1, pp. 13–15 / 13–15.** After the half twist and isotypic sequence, p. 13(1)–(2) chooses a fixed norm-one isotype, a symmetric interval of positive width, and a smooth compact class test supported above norm \(1+\epsilon\). It takes degree \(s=0\) to fix ideas, retaining interior shifted zeros with full multiplicities. The opening p. 14 convolution uses inverse-left translation. The paragraph beginning “Explicitly, we can use the image” prints the quotient expansion with *transpose-convolved* input jets and the images of the original biorthogonal output vectors, in increasing absolute-ordinate order, in trace norm. The following “Since \(\delta\)” paragraph instead prints bare, test-independent input factors before (1.2.1.1) and then asserts a weighted \(L^2\) kernel for the test-dependent operator. **The assigned p. 15 paragraph (“We may lift the elements”, before (3))** projects representatives of the output vectors to the orthogonal complement of the completed half-twisted theta isotype. It keeps the kernel name \(k_{\mathrm{spec},I,\phi}\) and claims it is still a trace-norm limit of the finite-rank kernels. Its argument is this prescription for the output vectors, inheriting the preceding convergence assertion; it does not separately supply a tail estimate. Items (3) and (4), in particular the later diagonal claim, are not the assigned passage.
- **Definitions and section.** The weighted norm and reciprocal-weight dual use the endpoint powers and Sobolev factor in (9.2.2.41)–(42), p. 417 / 417. Definition 10.1.1.1(1), (10.1.1.3), p. 434 / 434, closes the twisted global theta image in the weight; p. 435 / 435 discusses the half twist. The opening of §10.2.2 and (10.2.2.1)–(2), p. 445 / 445, separate the ambient quotient and its isotypic version. Lemma 10.4.1.2, pp. 456–457 / 456–457, (10.4.1.3)–(5), uses the closed theta subspace, \(s\ge0\), and positive twist parameter \(a\). For \(Q\) the quotient, \(P\) the orthogonal spectral projection, and \(P_{\mathrm{geom}}=1-P\), it gives \(Q=QP\), \(QP_{\mathrm{geom}}=0\), and \(S q=P\widetilde q\) for any representative \(\widetilde q\). The proof splits the identity into the orthogonal projections. Independence and uniqueness also follow because two representatives differ by a theta vector; the orthogonal representative has minimal norm by Pythagoras, giving the isometry for the quotient norm.
- **Later regularized formulas.** The §10.4.3.2 lead-in on p. 471 / 471 cites the estimates of Theorem 10.4.2.8 and announces *convolution after projection*, which is not the order forced by its ensuing lifted rows. Theorem 10.4.3.5, pp. 472–473 / 472–473, allows a positive twist \(a\), a compact symmetric base \([-\alpha,\alpha]\) with \(\alpha\ge0\), and \(s>1\). At the half twist and a fixed isotype, (10.4.3.39) gives the shifted Haar rows, with the unitary character and exponent \(b+it\). Part (1), (10.4.3.41), applies the section to each biorthogonal. Part (2) prints quotient transpose rows paired with quotient outputs in (10.4.3.42), and transpose densities paired with **orthogonally lifted** outputs in (10.4.3.43), in input–output order; the p. 473 continuation asserts convergence in the respective projective tensor topologies (with rectangular cutoffs across the characters / height indices). Restricting to one isotype, use the corresponding height cutoffs on the chosen labels; no equivalence of the full rectangular and lexicographic limits is needed here. Neither the restriction nor the citation lowers the degree to \(s=0\). In part (3), (10.4.3.44) sends a simple tensor to the row acting on the input times the output vector; (10.4.3.45) prints \(A(\phi)P\), and its preceding sentence names the quotient tensor number (10.4.3.42) rather than (43). In contrast, (10.4.1.10)–(11), pp. 457–458 / 457–458, distinguish the orders, and (10.4.2.5), p. 459 / 459, gives \(P A(\phi)=S A_{\mathrm{spec},I}(\phi)Q\). No operator equality with the printed (45) is imported.

## Correct lift and new checked scope

Write \(H\) for the weighted ambient isotype, \(K\) for the closed theta subspace, \(E=K^\perp\) for the realized quotient, \(Q:H\to E\) for the quotient projection and \(S:E\to H\) for the inclusion. Then \(QS=1\), \(SQ=P\). For a quotient row \(\ell_j\) and vector \(u_j\), with quotient convolution \(B=A_{\mathrm{spec},I}(\phi)\), the regularized finite term is \(u_j(\ell_j\circ B)\). Its lift is the operator \(x\mapsto (\ell_j\circ B\circ Q)(x)\,S u_j\). Under the Hilbert inner product linear in the input slot, if \((\ell_j\circ B)(z)=\langle v_j,z\rangle\), then \(\langle v_j,Qx\rangle=\langle S v_j,x\rangle\) exactly; no conjugation of the linear functional or change in Haar normalization is introduced by this step. Here \(v_j\) is a Hilbert Riesz vector, **not** the reciprocal-weight Haar density. Conversion between them would use the input weight and complex conjugation of the Riesz vector. Projecting the output does not turn a bare \(\ell_j\circ Q\) into \(\ell_j\circ B\circ Q\). Nor does the Hilbert-space projection choose pointwise values of an a.e. kernel or produce a product-kernel diagonal.

For quotient finite sums \(B_C\), the lifted sums act as \(S B_C Q\); if the limit on the quotient is \(B\), then the candidate limit on the ambient is \(S B Q=P A\), since \(B Q=Q A\). This is not \(A P\) in general. Under \(A K\subseteq K\), their difference \(A P-P A=(1-P) A P\) need not vanish. For example, on \(\mathbb C^2\), take \(P(x,y)=(x,0)\), \(A(x,y)=(0,x)\). This is a counterexample to interchanging the orders from invariance alone, not a claim that this particular matrix is a class convolution.

[`Lemmas.HilbertQuotientOperatorLift`](../../Proofs/Lemmas/HilbertQuotientOperatorLift.lean) uses the accepted `hilbertQuotientProjection T` for any complex Hilbert space and submodule `T` (it already kills the closure). Unlike the accepted projection/split, these results act on **operators**:

- `hilbertQuotientOperatorLift` is the linear **operator-norm** isometry \(B\mapsto S B Q\). The upper bound follows from \(Q\) contractive and \(S\) isometric; evaluate on \(S z\) for the reverse inequality, with no nontriviality assumption on the quotient. `hilbertQuotientOperatorLift_apply` gives its action and `hilbertQuotientOperatorLift_of_intertwine` gives the projection-after-convolution identity when the input intertwining holds.
- `hilbertQuotientOperatorLift_rankOne` identifies the lift with an actual ambient `InnerProductSpace.rankOne`, including the pulled-back *input* Riesz vector. `hilbertQuotientOperatorLift_sum_rankOne` extends any finite cutoff term by term, so in particular any full height cutoff when the retained labels are given. The norm-product cost of each designated term is unchanged, since both vector norms are inherited from \(H\).
- `hilbertQuotientOperatorLift_hasSum_rankOne` takes a given remainder \(R\) on the quotient, pointwise synthesis of \(R\) by these terms, and summability of the actual products \(\|u_j\|\|v_j\|\). The quotient operator series converges absolutely in operator norm; evaluating identifies its limit with \(R\). Map the series through the linear isometry and apply the checked rank-one identity. The ambient rank-one series has the very same summable sequence of term norms and converges in **operator norm** to \(S R Q\). The theorem needs no bound on a chosen sequence of approximants built into its hypotheses or assumption about where its labels come from.

The client below uses the accepted global LF theta range and the actual `rationalRadialHilbertQuotient`, `rationalRadialQuotientProjection`, and `rationalRadialQuotientConvolution` for \(F=\mathbb Q\), the trivial norm-one isotype, positive symmetric width and degree zero. It checks the compressed convolution, actual finite transpose-convolved rows, and a conditional remainder for that convolution minus an approximant. Its bounded quotient rows and quotient output vectors are parameters, not an assertion of descent of the manuscript's jets or existence of its biorthogonal vectors in these presentations. The accepted [quotient](rational-radial-hilbert-quotient.md), [convolution](rational-radial-hilbert-convolution.md), and [convolution receipt](f3c1b67400b3d180a586a682ceec1a8b140f9f1480d372e489b4f455be29f4da-80bba492258d64988564cb13bf3138c3a60eb8d9a2866a8c1a7d268b558c2a73.json) give the actual space and intertwiner; the [finite-rank expansion receipt](16a67e85f3278df1c7e3fe2d4f93540339cd4d3cbf92f7705b412a99d8db6e27-71bdfdeff3f97cf1bf324f98ff710bbb3614ce38389c1b72058562cd0970390e.json) and [kernel receipt](1bca11d346543ed7f4c4056797b6d63ec3d8969cef608d37d711ca9fa2b248f0-d951d8290be403b35931c65f86b9a325379b6b724d20ed4f81dd09018025aa9f.json) separately document the missing quotient expansion and the bare-kernel mismatch. [`RankOneSeries`](../../Proofs/Lemmas/RankOneSeries.lean) treats synthesis and right composition given estimates, not this two-sided isometric lift. The [operator trace handoff](../adhoc/operator-trace/handoff.md), [spectral audit](../obligations/trace-spectral.md) and [degree-zero audit](../walk/degree-zero-narrow-strip-spectral-trace.md) separate trace identification, this operator order and the diagonal. The toy Poisson normalization and toy support vanishing are scalar checks, not estimates for these lifts.

## Trace norm and explicit remainder

**Ordinary mathematics, not Lean:** Under \(H=S(E)\oplus K\), \(S B Q\) is unitarily equivalent to \(B\oplus 0\). For compact \(B\), its positive absolute-value operator is correspondingly \(|B|\oplus 0\), by uniqueness of the positive square root. The nonzero singular values with multiplicities agree, hence so do the trace norms for trace-class \(B\) (and the differences when a trace-norm convergent quotient approximation is already justified). Conversely the compression by \(Q\) and \(S\) recovers \(B\). The pinned Mathlib `Analysis/InnerProductSpace/SingularValues` is finite-dimensional; no analytic Schatten trace norm on these Hilbert spaces was found in the pinned sources. We did not add a substitute trace norm or treat the cost of a fixed rank-one presentation as such a norm.

**Open:** No trace-norm convergence of the prescribed actual absolute-ordinate expansion, no weighted projective-kernel convergence, no operator trace or diagonal, and no arbitrary-field formal identification. Even for the rational trivial isotype at \(s=0\), an analytic retry needs (i) bounded interior jets annihilating the entire global theta range, with the original biorthogonal pairings checked on the quotient and the correct half shift, (ii) Cauchy control of the actual full regularized zero blocks in the stated cutoffs (for example a summable block trace-norm bound including lifted-vector norms, not coefficient decay alone), and (iii) identification of the limit with the bounded descended convolution, for example by totality of those jets. For using the Lean series theorem specifically, supply norm-product summability and synthesis for the indicated presentation or its actual remainder; a block estimate allowing cancellation need not supply these stronger hypotheses. A full Lean trace-norm transfer further needs the analytic trace ideal with singular values or a proved equivalent norm. Any positive-degree extension must justify the edge order rule, rather than take the p. 13 maximum or the later floor rule at its strict-continuity endpoint as given. Any diagonal step needs a separate representative or differentiation argument.

## Reproduce the writer checks

From the workspace root, `lake build --wfail +Lemmas.HilbertQuotientOperatorLift +Theorems.RationalRadialHilbertConvolution` (Lean 4.36.0). In a fresh scratch file with both ordinary imports below, run `#check @Masullo.Name` and `#print axioms Masullo.Name` for each of the six endpoints above; run `lake env lean -D warningAsError=true` on it and on the separate use client below.

```lean
import Lemmas.HilbertQuotientOperatorLift
import Theorems.RationalRadialHilbertConvolution

noncomputable section

open Masullo MeasureTheory NumberField InnerProductSpace
open scoped InnerProductSpace
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

local notation "AdeleQ" => AdeleRing (𝓞 ℚ) ℚ
local notation "hα" => (zero_le_one : (0 : ℝ) ≤ 1)
local notation "hs" => (le_refl (0 : ℝ))
local notation "hab" => (neg_le_self hα)

variable [MeasurableSpace AdeleQ] [BorelSpace AdeleQ]
  [MeasurableSpace (AdeleQ ⧸ rationalDiagonal)] [BorelSpace (AdeleQ ⧸ rationalDiagonal)]

local notation "H" => rationalRadialHilbert hab 0
local notation "T" => rationalRadialThetaHilbertRange hab 0
local notation "E" => rationalRadialHilbertQuotient hab 0
local notation "Q" => rationalRadialQuotientProjection hab 0

-- Positive width, zero Sobolev degree, actual rational trivial isotype.
example {φ : ℝ → ℂ} (hφ : Continuous φ) (hc : HasCompactSupport φ) :
    let A := rationalRadialHilbertConvolution hα hs hφ hc
    let B := rationalRadialQuotientConvolution hα hs hφ hc
    hilbertQuotientOperatorLift T B = (Submodule.starProjection E).comp A ∧
      ‖(Submodule.starProjection E).comp A‖ = ‖B‖ := by
  intro A B
  have h := hilbertQuotientOperatorLift_of_intertwine T B A
    (rationalRadialQuotientConvolution_projection hα hs hφ hc)
  exact ⟨h, h ▸ (hilbertQuotientOperatorLift T).norm_map B⟩

-- Use the Riesz vectors of the *transpose-convolved* quotient rows.
example {ι : Type*} {φ : ℝ → ℂ} (hφ : Continuous φ) (hc : HasCompactSupport φ)
    (c : Finset ι) (u : ι → E) (ℓ : ι → E →L[ℂ] ℂ) (x : H) :
    let A := rationalRadialHilbertConvolution hα hs hφ hc
    let B := rationalRadialQuotientConvolution hα hs hφ hc
    let v j := (toDual ℂ E).symm ((ℓ j).comp B)
    let D := ∑ j ∈ c, rankOne ℂ (u j) (v j)
    hilbertQuotientOperatorLift T D = ∑ j ∈ c, rankOne ℂ (u j : H) (v j : H) ∧
      hilbertQuotientOperatorLift T D x = ∑ j ∈ c, ℓ j (Q (A x)) • (u j : H) := by
  intro A B v D
  have h := hilbertQuotientOperatorLift_sum_rankOne T c u v
  refine ⟨h, ?_⟩
  rw [show hilbertQuotientOperatorLift T D = _ from h, sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [rankOne_apply, ← Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left (K := E) (v j) x]
  change ⟪v j, Q x⟫_ℂ • (u j : H) = _
  simp only [v, toDual_symm_apply, ContinuousLinearMap.comp_apply]
  rw [rationalRadialQuotientConvolution_projection hα hs hφ hc]

-- A quotient remainder, if given with actual norm-product summability
-- and synthesis, converges to the remainder of projection-after-convolution.
example {ι : Type*} {φ : ℝ → ℂ} (hφ : Continuous φ) (hc : HasCompactSupport φ)
    (D : E →L[ℂ] E) (u : ι → E) (ℓ : ι → E →L[ℂ] ℂ)
    (h : Summable fun j ↦ ‖u j‖ * ‖(ℓ j).comp (rationalRadialQuotientConvolution hα hs hφ hc)‖)
    (hS : ∀ z : E, HasSum (fun j ↦ ℓ j (rationalRadialQuotientConvolution hα hs hφ hc z) • u j)
      ((rationalRadialQuotientConvolution hα hs hφ hc - D) z)) :
    let A := rationalRadialHilbertConvolution hα hs hφ hc
    let B := rationalRadialQuotientConvolution hα hs hφ hc
    let v j := (toDual ℂ E).symm ((ℓ j).comp B)
    (Summable fun j ↦ ‖rankOne ℂ (u j : H) (v j : H)‖) ∧
      HasSum (fun j ↦ rankOne ℂ (u j : H) (v j : H))
        ((Submodule.starProjection E).comp A - hilbertQuotientOperatorLift T D) := by
  intro A B v
  have hLift := hilbertQuotientOperatorLift_of_intertwine T B A
    (rationalRadialQuotientConvolution_projection hα hs hφ hc)
  have hsub : hilbertQuotientOperatorLift T (B - D) =
      hilbertQuotientOperatorLift T B - hilbertQuotientOperatorLift T D :=
    map_sub (hilbertQuotientOperatorLift T).toLinearMap B D
  rw [← hLift, ← hsub]
  refine hilbertQuotientOperatorLift_hasSum_rankOne T (B - D) u v ?_ (fun z ↦ ?_)
  · simpa only [v, (toDual ℂ E).symm.norm_map] using h
  · simpa only [rankOne_apply, v, toDual_symm_apply, ContinuousLinearMap.comp_apply] using hS z
```

Writer checks: targeted build passed (8041 jobs); the joint fresh signature check and ordinary-import application client passed with warnings fatal. All six endpoint axiom reports list exactly `propext`, `Classical.choice`, and `Quot.sound`.
