module

public import Lemmas.FixedInputPartner
import Mathlib.Algebra.Order.Group.Unbundled.Int
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.LinearCombination

/-!
# A projected-hit code determines its occupied endpoint

Sources: `486894b1b648:.godel/alice/projected-erasure.md:115–146`,
`082a89e67352:.godel/alice/shared-row-labels.md:3–9`, and
`082a89e67352:.godel/alice/rich-column-rows.md:3–9`.

Fix one orientation of an actual two-label list. The code does not retain the
actual input `v` or either coordinate of the original column `(c, d)`. The
filters recover the signed row `(c * h, β)`, then the longest sorted prime
prefixes of the two complete reduced products recover `(c, d)`. On that column
the first label recovers `v = c * x` by the determinant of the first rows.
In the other orientation the second column coordinate is named `e` instead.
This is only uniqueness of an occupied endpoint, not existence, a menu price,
a partner count or a capture result.

Owning check session: `01a2102d-ae00-70d1-a793-4b136b9edf79`.
-/

namespace ProjectedHitDecoder

/-- The actual signed second row. Here `m₂ = c * h` and `N = d * Z`.
The second filter divides the complete output `N`, not necessarily `Z`. -/
public structure SecondRow (F₂ q f_h f_N c d : ℕ) (V₀ H₀ cutoff : ℝ) (h Z : ℕ) (β : ℤ) : Prop where
  input_pos : 0 < F₂ * (c * h)
  output_pos : 0 < d * Z
  m_le : ((c * h : ℕ) : ℝ) ≤ V₀
  beta_ne_zero : β ≠ 0
  beta_bound : |(β : ℝ)| ≤ H₀
  primitive : (F₂ * (c * h)).Coprime (d * Z)
  output_eq : ((F₂ * (c * h) : ℕ) : ℤ) - (q : ℤ) * β = ((d * Z : ℕ) : ℤ)
  filter_h : f_h ∣ h
  filter_N : f_N ∣ d * Z
  prefix_c : FixedInputPartner.IsLongestPrimePrefix cutoff (F₂ * (c * h)) c
  prefix_d : FixedInputPartner.IsLongestPrimePrefix cutoff (d * Z) d

/-- The actual first row on the original column, carrying the first label. -/
public structure FirstRow (F₁ q c d : ℕ) (Aplus H : ℝ) (x y : ℕ) (α : ℤ) : Prop where
  x_pos : 0 < x
  y_pos : 0 < y
  x_le : (x : ℝ) ≤ Aplus
  alpha_ne_zero : α ≠ 0
  alpha_bound : |(α : ℝ)| ≤ H
  primitive : (c * x).Coprime (d * y)
  label_dvd : F₁ ∣ x
  det : (c : ℤ) * x - (d : ℤ) * y = (q : ℤ) * α

/-- An occupied endpoint `(v, c, d)` in the chosen orientation, with witnesses
for both rows. The first-row width is expressed without dividing by `d`. -/
@[expose] public def FitsCode (F₁ F₂ q : ℕ) (Aplus H V₀ H₀ cutoff : ℝ) (f_h f_N : ℕ)
    (t : ℕ × ℕ × ℕ) : Prop :=
  t.2.2.Coprime q ∧ 2 * Aplus * H < (t.2.2 : ℝ) * (F₁ : ℝ) ∧
    (∃ (x y : ℕ) (α : ℤ), FirstRow F₁ q t.2.1 t.2.2 Aplus H x y α ∧ t.1 = t.2.1 * x) ∧
    ∃ (h Z : ℕ) (β : ℤ), SecondRow F₂ q f_h f_N t.2.1 t.2.2 V₀ H₀ cutoff h Z β

private theorem SecondRow.row_primitive {F₂ q f_h f_N c d h Z : ℕ} {V₀ H₀ cutoff : ℝ} {β : ℤ}
    (r : SecondRow F₂ q f_h f_N c d V₀ H₀ cutoff h Z β) : (((c * h : ℕ) : ℤ).gcd β) = 1 := by
  let m : ℤ := ((c * h : ℕ) : ℤ)
  let g := m.gcd β
  have hin : (g : ℤ) ∣ ((F₂ * (c * h) : ℕ) : ℤ) := by
    rw [Nat.cast_mul]
    exact (Int.gcd_dvd_left m β).mul_left (F₂ : ℤ)
  have hout : (g : ℤ) ∣ ((d * Z : ℕ) : ℤ) := by
    rw [← r.output_eq]
    exact dvd_sub hin ((Int.gcd_dvd_right m β).mul_left (q : ℤ))
  have hg : g ∣ 1 := by
    rw [← r.primitive.gcd_eq_one]
    exact Nat.dvd_gcd (Int.natCast_dvd_natCast.mp hin) (Int.natCast_dvd_natCast.mp hout)
  exact Nat.dvd_one.mp hg

private theorem SecondRow.column_eq {F₂ q f_h f_N c₁ d₁ c₂ d₂ h₁ Z₁ h₂ Z₂ : ℕ}
    {V₀ H₀ cutoff : ℝ} {β₁ β₂ : ℤ} (hf_h : 0 < f_h) (hf_N : 0 < f_N)
    (hqN : q.Coprime f_N) (hcross : 2 * V₀ * H₀ < (f_h : ℝ) * (f_N : ℝ))
    (r₁ : SecondRow F₂ q f_h f_N c₁ d₁ V₀ H₀ cutoff h₁ Z₁ β₁)
    (r₂ : SecondRow F₂ q f_h f_N c₂ d₂ V₀ H₀ cutoff h₂ Z₂ β₂) :
    c₁ = c₂ ∧ d₁ = d₂ := by
  let m₁ := c₁ * h₁
  let m₂ := c₂ * h₂
  have hN₁ : (f_N : ℤ) ∣ (F₂ : ℤ) * (m₁ : ℤ) - (q : ℤ) * β₁ := by
    rw [← Nat.cast_mul, r₁.output_eq]
    exact Int.natCast_dvd_natCast.mpr r₁.filter_N
  have hN₂ : (f_N : ℤ) ∣ (F₂ : ℤ) * (m₂ : ℤ) - (q : ℤ) * β₂ := by
    rw [← Nat.cast_mul, r₂.output_eq]
    exact Int.natCast_dvd_natCast.mpr r₂.filter_N
  have hrow : ((m₁ : ℤ), β₁) = ((m₂ : ℤ), β₂) :=
    PrimitiveTwoFilterRow.primitiveRow_eq_of_two_filters (F := (F₂ : ℤ)) (q := (q : ℤ))
      (Int.natCast_pos.mpr hf_h) (Int.natCast_pos.mpr hf_N)
      (Int.natCast_pos.mpr (Nat.pos_of_mul_pos_left r₁.input_pos))
      (Int.natCast_pos.mpr (Nat.pos_of_mul_pos_left r₂.input_pos))
      (by exact_mod_cast r₁.m_le) (by exact_mod_cast r₂.m_le) r₁.beta_bound r₂.beta_bound
      r₁.row_primitive r₂.row_primitive
      (Int.natCast_dvd_natCast.mpr (r₁.filter_h.trans (Nat.dvd_mul_left h₁ c₁)))
      (Int.natCast_dvd_natCast.mpr (r₂.filter_h.trans (Nat.dvd_mul_left h₂ c₂)))
      hN₁ hN₂ (by simpa only [Int.gcd_natCast_natCast] using hqN.gcd_eq_one)
      (by exact_mod_cast hcross)
  have hm : m₁ = m₂ := Int.natCast_inj.mp (congrArg Prod.fst hrow)
  have hβ : β₁ = β₂ := congrArg Prod.snd hrow
  have hinput : F₂ * m₁ = F₂ * m₂ := congrArg (F₂ * ·) hm
  have houtput : d₁ * Z₁ = d₂ * Z₂ := Int.natCast_inj.mp <| calc
    ((d₁ * Z₁ : ℕ) : ℤ) = ((F₂ * m₁ : ℕ) : ℤ) - (q : ℤ) * β₁ := r₁.output_eq.symm
    _ = ((F₂ * m₂ : ℕ) : ℤ) - (q : ℤ) * β₂ := by rw [hinput, hβ]
    _ = ((d₂ * Z₂ : ℕ) : ℤ) := r₂.output_eq
  refine ⟨?_, ?_⟩
  · calc
      c₁ = FixedInputPartner.decodePrefix cutoff (F₂ * m₁) :=
        FixedInputPartner.eq_decodePrefix r₁.prefix_c
      _ = FixedInputPartner.decodePrefix cutoff (F₂ * m₂) := by rw [hinput]
      _ = c₂ := (FixedInputPartner.eq_decodePrefix r₂.prefix_c).symm
  · calc
      d₁ = FixedInputPartner.decodePrefix cutoff (d₁ * Z₁) :=
        FixedInputPartner.eq_decodePrefix r₁.prefix_d
      _ = FixedInputPartner.decodePrefix cutoff (d₂ * Z₂) := by rw [houtput]
      _ = d₂ := (FixedInputPartner.eq_decodePrefix r₂.prefix_d).symm

private theorem FirstRow.x_eq {F₁ q c d x₁ y₁ x₂ y₂ : ℕ} {Aplus H : ℝ} {α₁ α₂ : ℤ}
    (hq : 0 < q) (hd : 0 < d) (hdq : d.Coprime q) (hqF : q.Coprime F₁)
    (hwidth : 2 * Aplus * H < (d : ℝ) * (F₁ : ℝ))
    (r₁ : FirstRow F₁ q c d Aplus H x₁ y₁ α₁) (r₂ : FirstRow F₁ q c d Aplus H x₂ y₂ α₂) :
    x₁ = x₂ := by
  let Δ : ℤ := (x₁ : ℤ) * y₂ - (x₂ : ℤ) * y₁
  let B : ℤ := (x₂ : ℤ) * α₁ - (x₁ : ℤ) * α₂
  have hdet : (d : ℤ) * Δ = (q : ℤ) * B := by
    dsimp only [Δ, B]
    linear_combination (x₂ : ℤ) * r₁.det - (x₁ : ℤ) * r₂.det
  have hqΔ : (q : ℤ) ∣ Δ := hdq.symm.isCoprime.dvd_of_dvd_mul_left ⟨B, hdet⟩
  have hFΔ : (F₁ : ℤ) ∣ Δ :=
    dvd_sub ((Int.natCast_dvd_natCast.mpr r₁.label_dvd).mul_right _)
      ((Int.natCast_dvd_natCast.mpr r₂.label_dvd).mul_right _)
  have hqFΔ : (q : ℤ) * (F₁ : ℤ) ∣ Δ := hqF.isCoprime.mul_dvd hqΔ hFΔ
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hA : 0 ≤ Aplus := (Nat.cast_nonneg x₁).trans r₁.x_le
  have hB : |(B : ℝ)| ≤ 2 * Aplus * H := calc
    _ = |(x₂ : ℝ) * (α₁ : ℝ) - (x₁ : ℝ) * (α₂ : ℝ)| := by push_cast [B]; rfl
    _ ≤ |(x₂ : ℝ) * (α₁ : ℝ)| + |(x₁ : ℝ) * (α₂ : ℝ)| := abs_sub _ _
    _ = (x₂ : ℝ) * |(α₁ : ℝ)| + (x₁ : ℝ) * |(α₂ : ℝ)| := by
      simp only [abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _)]
    _ ≤ Aplus * H + Aplus * H := add_le_add
      (mul_le_mul r₂.x_le r₁.alpha_bound (abs_nonneg _) hA)
      (mul_le_mul r₁.x_le r₂.alpha_bound (abs_nonneg _) hA)
    _ = _ := by rw [← two_mul, mul_assoc]
  have hdetR : (d : ℝ) * (Δ : ℝ) = (q : ℝ) * (B : ℝ) := by exact_mod_cast hdet
  have hsmall : |(Δ : ℝ)| < (q : ℝ) * (F₁ : ℝ) := (mul_lt_mul_iff_right₀ hdR).mp <| calc
    (d : ℝ) * |(Δ : ℝ)| = |(q : ℝ) * (B : ℝ)| := by
      rw [← hdetR, abs_mul, abs_of_pos hdR]
    _ = (q : ℝ) * |(B : ℝ)| := by rw [abs_mul, abs_of_pos hqR]
    _ ≤ (q : ℝ) * (2 * Aplus * H) := mul_le_mul_of_nonneg_left hB hqR.le
    _ < (q : ℝ) * ((d : ℝ) * (F₁ : ℝ)) := mul_lt_mul_of_pos_left hwidth hqR
    _ = (d : ℝ) * ((q : ℝ) * (F₁ : ℝ)) := by ac_rfl
  have hzero := Int.eq_zero_of_abs_lt_dvd hqFΔ (by exact_mod_cast hsmall)
  have hcross : x₁ * y₂ = x₂ * y₁ := by
    exact_mod_cast (sub_eq_zero.mp hzero : (x₁ : ℤ) * y₂ = (x₂ : ℤ) * y₁)
  have hp₁ := Nat.Coprime.of_dvd (Nat.dvd_mul_left x₁ c) (Nat.dvd_mul_left y₁ d) r₁.primitive
  have hp₂ := Nat.Coprime.of_dvd (Nat.dvd_mul_left x₂ c) (Nat.dvd_mul_left y₂ d) r₂.primitive
  exact Nat.dvd_antisymm
    (hp₁.dvd_of_dvd_mul_right (hcross ▸ Nat.dvd_mul_right x₁ y₂))
    (hp₂.dvd_of_dvd_mul_right (hcross.symm ▸ Nat.dvd_mul_right x₂ y₁))

/-- Any two actual endpoints fitting the same projected-hit code coincide.
Neither the actual input nor the original column is fixed as code data, and
the filters need not be coprime to each other. -/
public theorem endpoint_eq_of_fitsCode {F₁ F₂ q f_h f_N : ℕ} {Aplus H V₀ H₀ cutoff : ℝ}
    (hq : 0 < q) (hqF : q.Coprime F₁) (hf_h : 0 < f_h) (hf_N : 0 < f_N)
    (hqN : q.Coprime f_N) (hcross : 2 * V₀ * H₀ < (f_h : ℝ) * (f_N : ℝ))
    {t₁ t₂ : ℕ × ℕ × ℕ}
    (ht₁ : FitsCode F₁ F₂ q Aplus H V₀ H₀ cutoff f_h f_N t₁)
    (ht₂ : FitsCode F₁ F₂ q Aplus H V₀ H₀ cutoff f_h f_N t₂) : t₁ = t₂ := by
  obtain ⟨v₁, c₁, d₁⟩ := t₁
  obtain ⟨v₂, c₂, d₂⟩ := t₂
  obtain ⟨hdq, hwidth, ⟨x₁, y₁, α₁, a, hv₁⟩, h₁, Z₁, β₁, b⟩ := ht₁
  obtain ⟨_, _, ⟨x₂, y₂, α₂, a', hv₂⟩, h₂, Z₂, β₂, b'⟩ := ht₂
  have ⟨hc, hd⟩ : c₁ = c₂ ∧ d₁ = d₂ := b.column_eq hf_h hf_N hqN hcross b'
  subst c₂
  subst d₂
  change v₁ = c₁ * x₁ at hv₁
  change v₂ = c₁ * x₂ at hv₂
  have hx := a.x_eq hq (Nat.pos_of_mul_pos_right b.output_pos) hdq hqF hwidth a'
  rw [hv₁, hv₂, hx]

end ProjectedHitDecoder
