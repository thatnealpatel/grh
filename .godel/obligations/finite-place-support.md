# Finite-place support on the idele class group

**Status: Worker candidate, not elaborated.** This is a project calculation for the [finite-place support repair](trace-geometric.md#narrowing-the-bridge-project-reasoning-not-a-source-reading). The provisional text of the proof of Theorem 12.5.1.1, p. 520 in the [pinned edition](../sources/masullo/README.md), chooses $S$ so that $|\operatorname{supp}\varphi|_F\subset(T^{-1},T)$ and $T<N(\mathfrak p_v)$ outside $S$. The proof there invokes the orbital trace theorem, not the algebraic result below. The lemma below gives a candidate formalization of the vanishing of the whole single-place restriction under the support and norm-one vanishing hypotheses, without evaluating an orbital trace or comparing any kernel diagonals.

**Local functional (provisional text).** Equation (12.5.1.2), p. 519, applies the linear local distribution with off-identity density $|g|_v^{1/2}/|1-g|_v$ to $g\mapsto\varphi(i_v(g))$, and sums over all finite places. The corresponding term of (12.4.1.3), p. 514, sums over $S_f$. The extracted superscript in the denominator there is unclear, but the prose immediately following names the local unit group, in agreement with (12.5.1.2) and the multiplicative measure in (A.3.2.2), p. 560. The same prefactor appears in (B.4.4.21), p. 625, where the surrounding prose identifies the local test as the pullback from the class group. The prefactor on the unit-group reading is $\log(q_v)/\mu_v(\mathcal O_{F_v}^{\times})$. For a place outside $S$, the input to the distribution is identically zero, including in a neighborhood of the identity, so the omitted term is zero regardless of the prefactor or the regularization at the identity. This does not compare the diagonal traces or justify their Mellin terms. In particular, the orbital terms invoked on p. 520 are indexed by rational residue characteristics absent from $S$, not by individual omitted places.

The proof first descends the norm of the underlying adele on ideles by the product formula. It does not install a norm structure on the class group or claim continuity. The local norm takes values $q_v^n$ for integers $n$, with $q_v=N(\mathfrak p_v)$; the sign convention for the exponent does not matter for detecting the gap about $1$. The support premise uses the nonzero locus of the test, which is sufficient here and follows from the manuscript's stronger support inclusion. No topology or test regularity is needed by this lemma.

Append the following in `namespace Masullo` after the [single-place norm draft](single-place-norm.md), with the same import and opens. `ideleNorm`, `ideleClassNorm`, and `localNorm_eq_zpow` are independent of `norm_idele_ofAdicCompletion`; only the class-group evaluation and its support corollary use that first draft.

```lean
open scoped WithZero

variable {K : Type*} [Field K] [NumberField K]

/-- The adelic norm as a multiplicative map on the idele group. -/
noncomputable def ideleNorm : IdeleGroup (𝓞 K) K →* ℝ where
  toFun x := ‖(x : AdeleRing (𝓞 K) K)‖
  map_one' := by
    change ‖(1 : AdeleRing (𝓞 K) K)‖ = 1
    rw [AdeleRing.norm_apply_of_isUnit isUnit_one]
    change (∏ v : InfinitePlace K, ‖(1 : v.Completion)‖ ^ v.mult) *
      (∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖(1 : v.adicCompletion K)‖) = 1
    simp only [norm_one, one_pow, Finset.prod_const_one, finprod_one, one_mul]
  map_mul' x y := by
    rw [AdeleRing.norm_apply_of_isUnit (x * y).isUnit,
      AdeleRing.norm_apply_of_isUnit x.isUnit, AdeleRing.norm_apply_of_isUnit y.isUnit]
    change
      (∏ v : InfinitePlace K, ‖(x : AdeleRing (𝓞 K) K).1 v *
        (y : AdeleRing (𝓞 K) K).1 v‖ ^ v.mult) *
      (∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖(x : AdeleRing (𝓞 K) K).2 v *
        (y : AdeleRing (𝓞 K) K).2 v‖) = _
    simp only [norm_mul, mul_pow, Finset.prod_mul_distrib]
    let snd : AdeleRing (𝓞 K) K →* IsDedekindDomain.FiniteAdeleRing (𝓞 K) K :=
      MonoidHom.snd _ _
    have hfin (z : IdeleGroup (𝓞 K) K) :
        (fun v : HeightOneSpectrum (𝓞 K) ↦ ‖(z : AdeleRing (𝓞 K) K).2 v‖).HasFiniteMulSupport :=
      NumberField.FiniteAdeleRing.hasFiniteMulSupport_norm (Units.map snd z)
    rw [finprod_mul_distrib (hfin x) (hfin y)]
    ac_rfl

/-- The product formula makes the norm well-defined on idele classes. -/
noncomputable def ideleClassNorm : IdeleClassGroup (𝓞 K) K →* ℝ :=
  QuotientGroup.lift (IdeleGroup.principalSubgroup (𝓞 K) K) ideleNorm (by
    intro x hx
    obtain ⟨u, rfl⟩ := MonoidHom.mem_range.mp hx
    apply MonoidHom.mem_ker.mpr
    change ‖algebraMap K (AdeleRing (𝓞 K) K) (u : K)‖ = 1
    exact AdeleRing.norm_algebraMap_eq_one_of_ne_zero u.ne_zero)

/-- The norm on idele classes restricts to the given local norm at a finite place. -/
theorem ideleClassNorm_ofAdicCompletion (v : HeightOneSpectrum (𝓞 K))
    (u : (v.adicCompletion K)ˣ) :
    ideleClassNorm (IdeleClassGroup.ofAdicCompletion (𝓞 K) K v u) =
      ‖(u : v.adicCompletion K)‖ := by
  rw [ideleClassNorm, IdeleClassGroup.ofAdicCompletion, MonoidHom.comp_apply,
    QuotientGroup.mk'_apply, QuotientGroup.lift_mk]
  exact norm_idele_ofAdicCompletion v u

/-- At a finite place the nonzero local norms are integer powers of the ideal norm. -/
private theorem localNorm_eq_zpow (v : HeightOneSpectrum (𝓞 K))
    (u : (v.adicCompletion K)ˣ) :
    ∃ n : ℤ, ‖(u : v.adicCompletion K)‖ = (v.asIdeal.absNorm : ℝ) ^ n := by
  let w : Valuation (v.adicCompletion K) ℤᵐ⁰ := Valued.v
  have h : w (u : v.adicCompletion K) ≠ 0 := w.ne_zero_iff.mpr u.ne_zero
  refine ⟨WithZero.log (w (u : v.adicCompletion K)), ?_⟩
  rw [FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply (v.absNorm_ne_zero) h]
  push_cast

/-- For a place of ideal norm greater than `T`, the indicated test restricts to zero. -/
theorem finitePlaceRestriction_eq_zero (v : HeightOneSpectrum (𝓞 K)) (T : ℝ)
    (hT : 1 < T) (hq : T < (v.asIdeal.absNorm : ℝ))
    (φ : IdeleClassGroup (𝓞 K) K → ℂ)
    (hband : ∀ g, φ g ≠ 0 → T⁻¹ < ideleClassNorm g ∧ ideleClassNorm g < T)
    (hunit : ∀ g, ideleClassNorm g = 1 → φ g = 0)
    (u : (v.adicCompletion K)ˣ) :
    φ (IdeleClassGroup.ofAdicCompletion (𝓞 K) K v u) = 0 := by
  let g := IdeleClassGroup.ofAdicCompletion (𝓞 K) K v u
  let q : ℝ := v.asIdeal.absNorm
  change φ g = 0
  change T < q at hq
  have hq₁ : 1 ≤ q := (hT.trans hq).le
  obtain ⟨n, hn⟩ := localNorm_eq_zpow v u
  have hn' : ideleClassNorm g = q ^ n := (ideleClassNorm_ofAdicCompletion v u).trans hn
  obtain hneg | heq | hpos := lt_trichotomy n 0
  · by_contra h
    have hlow := (hband g h).1
    have hsmall : q ^ n ≤ q⁻¹ := by
      rw [← zpow_neg_one]
      exact zpow_le_zpow_right₀ hq₁ (by omega)
    have hinv : q⁻¹ < T⁻¹ :=
      (inv_lt_inv₀ (zero_lt_one.trans (hT.trans hq)) (zero_lt_one.trans hT)).mpr hq
    exact (not_lt_of_ge ((hn'.le.trans hsmall).trans hinv.le)) hlow
  · exact hunit g (by simpa only [heq, zpow_zero] using hn')
  · by_contra h
    have hupp := (hband g h).2
    have hlarge : q ≤ q ^ n := by
      conv_lhs => rw [← zpow_one q]
      exact zpow_le_zpow_right₀ hq₁ (by omega)
    exact (not_lt_of_ge (hq.le.trans (hlarge.trans hn'.ge))) hupp
```

**Independent source review.** Yah found the mathematical argument sound, including product-formula descent and the need to vanish on the whole norm-one subgroup, not just at the identity. Source review at Mathlib `fc4f59e577feb1a4956671bc04ac18aaaf8cd842` corrected the valuation logarithm to `WithZero.log` and restricted the positive-exponent rewrite to the left-hand side. The review independently extracted the hash-verified PDF and found the unit-group denominator in raw text on p. 514; the layout extraction displaces the superscript. This is not rendered-page verification. In Lean, the definitional reductions and coercion steps still need elaboration.

Once the designated `GRH_PROOF_WORKER` transport is available, stage both drafts in an isolated proof revision and run this command from the repository root, substituting the full proof-candidate commit ID:

```sh
go run ./cmd/godel check <full-candidate-commit-id> \
  Masullo.norm_idele_ofAdicCompletion \
  Masullo.ideleClassNorm_ofAdicCompletion \
  Masullo.finitePlaceRestriction_eq_zero
```

Until this check is possible, keep both drafts outside `Proofs`.
