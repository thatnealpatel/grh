module

public import Lemmas.RankTwoRecoveryMinors
import Mathlib.Tactic.Ring

/-!
# Divisibility of the rank-two recovery minors

Source: `059232cff7d3894d8545eb11ffccf9cd2fec1646:.godel/alice/normal-factor-minors.md:17–39,49`
(introduced at `25765be8`, unchanged at `e96c4611`). This is the divisibility
step at lines 25–31 used to recover the two residual factors from the minors
of a fixed independent pair, including when that pair consists of represented
normals as at line 49. No nonvanishing or counting estimate is asserted.

Instead of completing the represented normal to a basis of the full plane
lattice, use an ambient integral Bézout functional taking value `1` on the
normal. It transfers the divisibilities to the given pair by an integral
linear combination of minors, without requiring the normal to belong to the
integer span of that pair.

Owning check session: `01a20c71-faab-7613-8747-63acf6b0d98e`.
-/

namespace RankTwoRecoveryMinors

private abbrev RationalForm := (Fin 3 → ℚ) →ₗ[ℚ] ℚ

private def eval3 (a b c : ℚ) : RationalForm :=
  a • LinearMap.proj 0 + b • LinearMap.proj 1 + c • LinearMap.proj 2

private theorem cast_exact_quotient {m : ℕ} (hm : 0 < m) {n : ℤ} (hd : (m : ℤ) ∣ n) :
    ((n / (m : ℤ) : ℤ) : ℚ) = (m : ℚ)⁻¹ * (n : ℚ) := by
  rw [← div_eq_inv_mul, eq_div_iff (show (m : ℚ) ≠ 0 by exact_mod_cast hm.ne')]
  exact_mod_cast Int.ediv_mul_cancel hd

private theorem k_eval {q F' fA fB : ℕ} (hd : 0 < fA * fB) {x : Vector}
    (hx : x ∈ lattice q F' fA fB) :
    (((fA * fB : ℕ) : ℚ)⁻¹ • eval3 q F' F') (rationalize x) = (K q F' fA fB x : ℚ) := by
  rw [K, cast_exact_quotient hd hx.2.2]
  simp only [eval3, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.proj_apply,
    smul_eq_mul, rationalize, numerator, Int.cast_add, Int.cast_mul, Int.cast_natCast]
  ring

private theorem coord_eval {f : ℕ} (hf : 0 < f) {j : Fin 3} {x : Vector}
    (hx : (f : ℤ) ∣ x j) :
    ((f : ℚ)⁻¹ • (LinearMap.proj j : RationalForm)) (rationalize x) =
      ((x j / (f : ℤ) : ℤ) : ℚ) := by
  rw [cast_exact_quotient hf hx]
  rfl

private theorem minor_identity {u v w : Fin 3 → ℚ} {s t : ℚ}
    (hw : s • u + t • v = w) (ell F G : RationalForm) (hell : ell w = 1) :
    F u * G v - F v * G u =
      ell u * (F w * G v - F v * G w) - ell v * (F w * G u - F u * G w) := by
  calc
    _ = ell w * (F u * G v - F v * G u) := by rw [hell, one_mul]
    _ = _ := by
      rw [← hw]
      simp only [map_add, map_smul, smul_eq_mul]
      ring

private theorem minor_dvd_of_mem_plane {L : Set Vector} {u v w : Vector}
    (hu : u ∈ L) (hv : v ∈ L) (hw : w ∈ L) (hplane : rationalize w ∈ plane u v)
    {a b c : ℤ} (hprim : a * w 0 + b * w 1 + c * w 2 = 1)
    {F G : Vector → ℤ} {FQ GQ : RationalForm}
    (hF : ∀ x ∈ L, FQ (rationalize x) = (F x : ℚ))
    (hG : ∀ x ∈ L, GQ (rationalize x) = (G x : ℚ))
    {h : ℤ} (hFw : h ∣ F w) (hGw : h ∣ G w) :
    h ∣ minor (values F u v) (values G u v) := by
  let ell (x : Vector) : ℤ := a * x 0 + b * x 1 + c * x 2
  let ellQ : RationalForm := eval3 a b c
  have hell (x : Vector) : ellQ (rationalize x) = (ell x : ℚ) := by
    simp only [ellQ, ell, eval3, LinearMap.add_apply, LinearMap.smul_apply,
      LinearMap.proj_apply, smul_eq_mul, rationalize, Int.cast_add, Int.cast_mul]
  have hellw : ellQ (rationalize w) = 1 := by
    rw [hell, show ell w = 1 from hprim, Int.cast_one]
  obtain ⟨s, t, hst⟩ := Submodule.mem_span_pair.mp hplane
  -- The rational coefficients appear only in the proof of this integer identity.
  have hdet : minor (values F u v) (values G u v) =
      ell u * minor (values F w v) (values G w v) -
        ell v * minor (values F w u) (values G w u) := by
    apply Int.cast_injective (α := ℚ)
    simp only [minor, values, Matrix.cons_val_zero, Matrix.cons_val_one, Int.cast_sub, Int.cast_mul,
      ← hF _ hu, ← hF _ hv, ← hF _ hw, ← hG _ hu, ← hG _ hv, ← hG _ hw, ← hell]
    exact minor_identity hst ellQ FQ GQ hellw
  have hrow (x : Vector) : h ∣ minor (values F w x) (values G w x) :=
    dvd_sub (hFw.mul_right (G x)) (hGw.mul_left (F x))
  rw [hdet]
  exact dvd_sub ((hrow v).mul_left _) ((hrow u).mul_left _)

/-- Both exact quotient minors on any independent lattice pair inherit the corresponding
common divisor at an ambient-primitive lattice vector in the rational plane. The ambient
primitivity is given by integer Bézout coordinates; no integer span membership is needed.
The divisibility argument itself does not require independence. -/
public theorem recovery_minors_dvd {q F' fA fB hA hB : ℕ} {u v w : Vector}
    (hfA : 0 < fA) (hfB : 0 < fB)
    (hu : u ∈ lattice q F' fA fB) (hv : v ∈ lattice q F' fA fB) (hw : w ∈ lattice q F' fA fB)
    (_hind : LinearIndependent ℚ ![rationalize u, rationalize v])
    (hplane : rationalize w ∈ plane u v)
    (hprim : ∃ a b c : ℤ, a * w 0 + b * w 1 + c * w 2 = 1)
    (hAK : (hA : ℤ) ∣ K q F' fA fB w) (hAC : (hA : ℤ) ∣ C₀ fA w)
    (hBK : (hB : ℤ) ∣ K q F' fA fB w) (hBB : (hB : ℤ) ∣ B₀ fB w) :
    ((hA : ℤ) ∣ minor (values (K q F' fA fB) u v) (values (C₀ fA) u v)) ∧
      ((hB : ℤ) ∣ minor (values (K q F' fA fB) u v) (values (B₀ fB) u v)) := by
  obtain ⟨a, b, c, habc⟩ := hprim
  have hK (x : Vector) (hx : x ∈ lattice q F' fA fB) :
      (((fA * fB : ℕ) : ℚ)⁻¹ • eval3 q F' F') (rationalize x) = (K q F' fA fB x : ℚ) :=
    k_eval (Nat.mul_pos hfA hfB) hx
  have hC (x : Vector) (hx : x ∈ lattice q F' fA fB) :
      ((fA : ℚ)⁻¹ • (LinearMap.proj 2 : RationalForm)) (rationalize x) = (C₀ fA x : ℚ) :=
    coord_eval hfA hx.2.1
  have hB (x : Vector) (hx : x ∈ lattice q F' fA fB) :
      ((fB : ℚ)⁻¹ • (LinearMap.proj 1 : RationalForm)) (rationalize x) = (B₀ fB x : ℚ) :=
    coord_eval hfB hx.1
  exact ⟨minor_dvd_of_mem_plane hu hv hw hplane habc hK hC hAK hAC,
    minor_dvd_of_mem_plane hu hv hw hplane habc hK hB hBK hBB⟩

end RankTwoRecoveryMinors
