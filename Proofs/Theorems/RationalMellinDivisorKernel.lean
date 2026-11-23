module

public import Lemmas.CompletedZetaOrders
public import Lemmas.EntireDivisorDivision
import Lemmas.RationalCompletedZetaZeros
import Mathlib.Tactic.NormNum

/-! # The middle kernel of the rational Mellin divisor sequence

In the rational trivial isotype of §1.2.1 (p. 13), the generator in the
Mellin coordinate `s` is `entireZeta (s + 1 / 2)`. The normalized Taylor
jet is taken at `ρ - 1 / 2`, with the order at `ρ` in the unshifted
coordinate. This proves middle exactness for the displayed left ideal
intersection, not its identification with a theta image or surjectivity
of the jet map.
-/

open Set

namespace Masullo

/-- The underlying set of `A𝒮(ℂ)` in Definition D.3.1.3: entire functions with
uniform Schwartz bounds on each bounded closed vertical strip. This definition
specifies no topology. -/
@[expose] public def schwartzBergmanEntire : Set (ℂ → ℂ) :=
  {f | AnalyticOnNhd ℂ f univ ∧
    ∀ (a b : ℝ) (n k : ℕ), ∃ C : ℝ, ∀ z : ℂ, a ≤ z.re → z.re ≤ b →
      ‖z ^ n * iteratedDeriv k f z‖ ≤ C}

/-- The pole-cleared completed rational zeta function in the half-shifted Mellin coordinate. -/
@[expose] public noncomputable def rationalMellinDivisorGenerator (s : ℂ) : ℂ :=
  entireZeta (s + 1 / 2)

/-- Away from the two poles, this is the literal product printed on p. 13. -/
public theorem rationalMellinDivisorGenerator_eq_mul {s : ℂ}
    (h₀ : s + 1 / 2 ≠ 0) (h₁ : s + 1 / 2 ≠ 1) :
    rationalMellinDivisorGenerator s =
      (s + 1 / 2) * (s - 1 / 2) * completedRiemannZeta (s + 1 / 2) := by
  rw [completedZeta_eq_quotient h₀ h₁, rationalMellinDivisorGenerator,
    show s - 1 / 2 = s + 1 / 2 - 1 by ring,
    mul_div_cancel₀ _ (mul_ne_zero h₀ (sub_ne_zero.mpr h₁))]

private theorem entireZeta_eq_zero_iff (w : ℂ) : entireZeta w = 0 ↔ w ∈ criticalStripZetaZeros := by
  by_cases h₀ : w = 0
  · subst w
    simp [entireZeta, mem_criticalStripZetaZeros]
  by_cases h₁ : w = 1
  · subst w
    simp [mem_criticalStripZetaZeros]
  rw [← completedZeta_eq_zero_iff_mem_criticalStripZetaZeros h₀ h₁,
    completedZeta_eq_quotient h₀ h₁]
  simp [div_eq_zero_iff, mul_ne_zero h₀ (sub_ne_zero.mpr h₁)]

/-- The zeros are exactly the shifted open-critical-strip zeros, with neither
cleared pole and no negative even integer in this divisor. -/
public theorem rationalMellinDivisorGenerator_eq_zero_iff (s : ℂ) :
    rationalMellinDivisorGenerator s = 0 ↔ ∃ ρ : criticalStripZetaZeros, shiftedZetaZero ρ = s := by
  rw [rationalMellinDivisorGenerator, entireZeta_eq_zero_iff]
  refine ⟨fun h ↦ ⟨⟨s + 1 / 2, h⟩, ?_⟩, ?_⟩
  · exact add_sub_cancel_right _ _
  · rintro ⟨ρ, rfl⟩
    rw [show shiftedZetaZero ρ + 1 / 2 = (ρ : ℂ) by simp [shiftedZetaZero]]
    exact ρ.property

/-- At a divisor point the shifted generator retains the *full* analytic multiplicity. -/
public theorem rationalMellinDivisorGenerator_order (ρ : criticalStripZetaZeros) :
    analyticOrderAt rationalMellinDivisorGenerator (shiftedZetaZero ρ) = (zetaZeroOrder ρ : ℕ∞) := by
  have h : AnalyticAt ℂ (fun s : ℂ ↦ s + 1 / 2) (shiftedZetaZero ρ) := by fun_prop
  have hd : deriv (fun s : ℂ ↦ s + 1 / 2) (shiftedZetaZero ρ) ≠ 0 := by simp
  change analyticOrderAt (entireZeta ∘ (fun s : ℂ ↦ s + 1 / 2)) (shiftedZetaZero ρ) = _
  rw [analyticOrderAt_comp_of_deriv_ne_zero h hd]
  obtain ⟨_, hpos, hlt⟩ := mem_criticalStripZetaZeros.mp ρ.property
  rw [show shiftedZetaZero ρ + 1 / 2 = (ρ : ℂ) by simp [shiftedZetaZero],
    analyticOrderAt_entireZeta_eq hpos hlt, zetaZeroOrder_cast_eq]

/-- The `k`-th Taylor coefficient at each shifted zero, for `k` strictly below
its multiplicity. The target consists of all arrays with these coordinates. -/
@[expose] public noncomputable def rationalMellinDivisorJet (f : ℂ → ℂ) :
    (ρ : criticalStripZetaZeros) → Fin (zetaZeroOrder ρ) → ℂ :=
  fun ρ k ↦ iteratedDeriv (k : ℕ) f (shiftedZetaZero ρ) / ((k : ℕ).factorial : ℂ)

/-- For an entire input, vanishing of all rational Mellin-divisor jets is
**equivalent** to division by the shifted, pole-cleared generator with entire
quotient. No strip-decay condition is imposed on that quotient. -/
public theorem rationalMellinDivisorJet_eq_zero_iff {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f univ) :
    rationalMellinDivisorJet f = 0 ↔
      ∃ q : ℂ → ℂ, AnalyticOnNhd ℂ q univ ∧ f = rationalMellinDivisorGenerator * q := by
  have hg : AnalyticOnNhd ℂ rationalMellinDivisorGenerator univ := by
    intro s _
    have h : AnalyticAt ℂ (fun w : ℂ ↦ w + 1 / 2) s := by fun_prop
    exact (entireZeta_analyticOnNhd (s + 1 / 2) (mem_univ _)).comp
      (f := fun w : ℂ ↦ w + 1 / 2) h
  have hg₀ : rationalMellinDivisorGenerator ≠ 0 := by
    intro h
    have he := congrFun h (1 / 2 : ℂ)
    norm_num [rationalMellinDivisorGenerator] at he
  rw [entire_mul_iff_vanishing_jets hf hg hg₀]
  constructor
  · intro hj s hs k hk
    obtain ⟨ρ, rfl⟩ := (rationalMellinDivisorGenerator_eq_zero_iff s).mp hs
    rw [rationalMellinDivisorGenerator_order, ENat.toNat_natCast] at hk
    have hc := congrFun (congrFun hj ρ) ⟨k, hk⟩
    change iteratedDeriv k f (shiftedZetaZero ρ) / (k.factorial : ℂ) = 0 at hc
    exact (div_eq_zero_iff.mp hc).resolve_right (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k))
  · intro hj
    funext ρ k
    have hz := (rationalMellinDivisorGenerator_eq_zero_iff (shiftedZetaZero ρ)).mpr ⟨ρ, rfl⟩
    have hk : (k : ℕ) < (analyticOrderAt rationalMellinDivisorGenerator (shiftedZetaZero ρ)).toNat := by
      rw [rationalMellinDivisorGenerator_order, ENat.toNat_natCast]
      exact k.isLt
    change iteratedDeriv (k : ℕ) f (shiftedZetaZero ρ) / ((k : ℕ).factorial : ℂ) = 0
    rw [hj _ hz k hk, zero_div]

/-- The set-theoretic kernel on the rational Schwartz–Bergman middle space
is precisely the intersection with the principal ideal of the entire-function ring. -/
public theorem rationalMellinDivisorJet_kernel :
    {f ∈ schwartzBergmanEntire | rationalMellinDivisorJet f = 0} =
      {f ∈ schwartzBergmanEntire | ∃ q : ℂ → ℂ, AnalyticOnNhd ℂ q univ ∧
        f = rationalMellinDivisorGenerator * q} := by
  ext f
  change (f ∈ schwartzBergmanEntire ∧ rationalMellinDivisorJet f = 0) ↔ _
  exact and_congr_right fun hf ↦ rationalMellinDivisorJet_eq_zero_iff hf.1

/-- Given infinitude of the rational divisor, the unrestricted Cartesian product
contains a jet array outside the image: the array with every coefficient one.
The hypothesis is precisely on the actual distinct critical-strip zeros. -/
public theorem rationalMellinDivisorJet_ne_one (hinf : Infinite criticalStripZetaZeros)
    {f : ℂ → ℂ} (hf : f ∈ schwartzBergmanEntire) : rationalMellinDivisorJet f ≠ 1 := by
  intro hj
  obtain ⟨C, hC⟩ := hf.2 (-(1 / 2)) (1 / 2) 1 0
  have hbound (ρ : criticalStripZetaZeros) : ‖shiftedZetaZero ρ‖ ≤ C := by
    let k : Fin (zetaZeroOrder ρ) := ⟨0, zetaZeroOrder_pos ρ⟩
    have hvalue : f (shiftedZetaZero ρ) = 1 := by
      have h := congrFun (congrFun hj ρ) k
      simpa [rationalMellinDivisorJet, k] using h
    have hre := abs_lt.mp (abs_re_shiftedZetaZero_lt ρ)
    simpa [hvalue] using hC (shiftedZetaZero ρ) hre.1.le hre.2.le
  have hfinite := shiftedZetaZero_preimage_finite (isCompact_closedBall (0 : ℂ) C)
  apply (Set.infinite_univ_iff.mpr hinf) (hfinite.subset ?_)
  intro ρ _
  exact Metric.mem_closedBall.mpr (by simpa [dist_zero_right] using hbound ρ)

end Masullo
