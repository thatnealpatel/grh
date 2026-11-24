module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.Index
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Difference indices in the translated determinant chart

Sources: `eb35ed0:.godel/alice/partial-scalar-classes.md:9–11,17–24` and
`eb35ed0:.godel/alice/reference-coset-windows.md:15–19` (in particular the index
calculation on line 19), as used at pin `b3723e8a`.

The chart is `(z₁,s)`, with `n = ρ + b z` and `t = τ + e s`. We count the
quotient by the differences of the **full** nonempty affine filter. Restricting
points to a box preserves determinant divisibility but need not preserve their
difference subgroup. This module does not estimate the number of points or splits
in any box.

Owning check session: `01a20b48-5cad-74c3-865b-b625005166b3`.
-/

namespace AffineDeterminantIndex

/-- The normalized determinant step `d(e/b)`. Exactness for `b ∣ e` is used below. -/
@[expose] public def step (d e b : ℕ) : ℤ := (d : ℤ) * ((e / b : ℕ) : ℤ)

/-- The full affine filter, projected to `(z₁,s)`; `z₂` is the second spatial
coordinate. In particular the filters divide `nᵢ`, not `zᵢ`. -/
@[expose] public def fiber (F₁ : ℕ) (F₂ : ℤ) (d e b a₁ a₂ : ℕ)
    (ρ : ℤ × ℤ) (C : ℤ) : Set (ℤ × ℤ) :=
  {p | ∃ z₂ : ℤ, F₂ * p.1 - (F₁ : ℤ) * z₂ = C + step d e b * p.2 ∧
    (a₁ : ℤ) ∣ ρ.1 + (b : ℤ) * p.1 ∧ (a₂ : ℤ) ∣ ρ.2 + (b : ℤ) * z₂}

private theorem scale_step {d e b : ℕ} (hbe : b ∣ e) :
    (b : ℤ) * step d e b = (d : ℤ) * (e : ℤ) := by
  have h : (b : ℤ) * ((e / b : ℕ) : ℤ) = (e : ℤ) := by
    exact_mod_cast Nat.mul_div_cancel' hbe
  rw [step, mul_left_comm (b : ℤ), h]

variable {F₁ d e b a₁ a₂ : ℕ} {F₂ C τ : ℤ} {ρ : ℤ × ℤ}

/-- An occupied physical chart supplies the integer translation constant. -/
public theorem exists_chart_constant (hbe : b ∣ e) {z₁ z₂ s : ℤ}
    (h : F₂ * (ρ.1 + (b : ℤ) * z₁) - (F₁ : ℤ) * (ρ.2 + (b : ℤ) * z₂) =
      (d : ℤ) * (τ + (e : ℤ) * s)) :
    ∃ C : ℤ, (b : ℤ) * C = (d : ℤ) * τ - F₂ * ρ.1 + (F₁ : ℤ) * ρ.2 := by
  refine ⟨F₂ * z₁ - (F₁ : ℤ) * z₂ - step d e b * s, ?_⟩
  linear_combination h - s * scale_step (d := d) hbe

/-- The affine chart retains the original determinant and coordinate filters. -/
public theorem mem_fiber_iff_physical (hb : 0 < b) (hbe : b ∣ e)
    (hC : (b : ℤ) * C = (d : ℤ) * τ - F₂ * ρ.1 + (F₁ : ℤ) * ρ.2) {p : ℤ × ℤ} :
    p ∈ fiber F₁ F₂ d e b a₁ a₂ ρ C ↔
      ∃ z₂ : ℤ, F₂ * (ρ.1 + (b : ℤ) * p.1) - (F₁ : ℤ) * (ρ.2 + (b : ℤ) * z₂) =
        (d : ℤ) * (τ + (e : ℤ) * p.2) ∧
        (a₁ : ℤ) ∣ ρ.1 + (b : ℤ) * p.1 ∧ (a₂ : ℤ) ∣ ρ.2 + (b : ℤ) * z₂ := by
  constructor
  · rintro ⟨z₂, hz, h₁, h₂⟩
    refine ⟨z₂, ?_, h₁, h₂⟩
    linear_combination (b : ℤ) * hz + hC + p.2 * scale_step (d := d) hbe
  · rintro ⟨z₂, hz, h₁, h₂⟩
    refine ⟨z₂, Int.eq_of_mul_eq_mul_left (Int.natCast_ne_zero.mpr hb.ne') ?_, h₁, h₂⟩
    linear_combination hz - hC - p.2 * scale_step (d := d) hbe

/-- The two residue coordinates on the ambient chart, for a determinant step `D`. -/
@[expose] public def residueMap (F₁ : ℕ) (F₂ D : ℤ) (a₁ a₂ : ℕ) :
    (ℤ × ℤ) →+ ZMod a₁ × ZMod (F₁ * a₂) where
  toFun w := ((w.1 : ZMod a₁), ((F₂ * w.1 - D * w.2 : ℤ) : ZMod (F₁ * a₂)))
  map_zero' := by simp
  map_add' u v := by
    refine Prod.ext (Int.cast_add _ _) ?_
    simp only [Prod.fst_add, Prod.snd_add, Int.cast_sub, Int.cast_mul, Int.cast_add]
    ring

/-- The homogeneous lattice in `(z₁,s)`. Its unfiltered version sets `a₁=a₂=1`. -/
@[expose] public def lattice (F₁ : ℕ) (F₂ D : ℤ) (a₁ a₂ : ℕ) : AddSubgroup (ℤ × ℤ) :=
  (residueMap F₁ F₂ D a₁ a₂).ker

public theorem mem_lattice {D : ℤ} {w : ℤ × ℤ} : w ∈ lattice F₁ F₂ D a₁ a₂ ↔
    ((a₁ : ℤ) ∣ w.1) ∧ ((F₁ : ℤ) * (a₂ : ℤ) ∣ F₂ * w.1 - D * w.2) := by
  rw [lattice, AddMonoidHom.mem_ker]
  change ((w.1 : ZMod a₁), ((F₂ * w.1 - D * w.2 : ℤ) : ZMod (F₁ * a₂))) = (0, 0) ↔ _
  rw [Prod.mk.injEq, ZMod.intCast_zmod_eq_zero_iff_dvd, ZMod.intCast_zmod_eq_zero_iff_dvd,
    Nat.cast_mul]

/-- The spatial difference `w₂` is reconstructed by the homogeneous determinant
relation. When `F₁>0`, that relation also makes it unique. -/
public theorem mem_lattice_iff_exists {D : ℤ} {w : ℤ × ℤ} :
    w ∈ lattice F₁ F₂ D a₁ a₂ ↔
      ∃ w₂ : ℤ, F₂ * w.1 - (F₁ : ℤ) * w₂ = D * w.2 ∧
        (a₁ : ℤ) ∣ w.1 ∧ (a₂ : ℤ) ∣ w₂ := by
  rw [mem_lattice]
  constructor
  · rintro ⟨h₁, k, hk⟩
    exact ⟨(a₂ : ℤ) * k, by linear_combination hk, h₁, dvd_mul_right _ _⟩
  · rintro ⟨w₂, hw₂, h₁, k, hk⟩
    refine ⟨h₁, k, ?_⟩
    linear_combination hw₂ + (F₁ : ℤ) * hk

private theorem dvd_cancel_scale {a b : ℕ} {w : ℤ} (hab : a.Coprime b)
    (hw : (a : ℤ) ∣ (b : ℤ) * w) : (a : ℤ) ∣ w := by
  rw [Int.ofNat_dvd_left] at hw ⊢
  rw [Int.natAbs_mul, Int.natAbs_natCast] at hw
  exact hab.dvd_of_dvd_mul_left hw

/-- Translation by any point of the full filter identifies it with the homogeneous
lattice. This uses `b ∣ e` to cancel `b` in the divisibility filters. -/
public theorem add_mem_fiber_iff (hbe : b ∣ e) (hea : e.Coprime (a₁ * a₂))
    {p w : ℤ × ℤ} (hp : p ∈ fiber F₁ F₂ d e b a₁ a₂ ρ C) :
    p + w ∈ fiber F₁ F₂ d e b a₁ a₂ ρ C ↔ w ∈ lattice F₁ F₂ (step d e b) a₁ a₂ := by
  have hba := Nat.Coprime.of_dvd_left hbe hea
  have hb₁ := (hba.of_dvd_right (Nat.dvd_mul_right a₁ a₂)).symm
  have hb₂ := (hba.of_dvd_right (Nat.dvd_mul_left a₂ a₁)).symm
  obtain ⟨p₂, hp₂, hp₁d, hp₂d⟩ := hp
  rw [mem_lattice_iff_exists]
  change (∃ q₂ : ℤ, F₂ * (p.1 + w.1) - (F₁ : ℤ) * q₂ = C + step d e b * (p.2 + w.2) ∧
    (a₁ : ℤ) ∣ ρ.1 + (b : ℤ) * (p.1 + w.1) ∧ (a₂ : ℤ) ∣ ρ.2 + (b : ℤ) * q₂) ↔ _
  constructor
  · rintro ⟨q₂, hq₂, hq₁d, hq₂d⟩
    refine ⟨q₂ - p₂, by linear_combination hq₂ - hp₂, dvd_cancel_scale hb₁ ?_,
      dvd_cancel_scale hb₂ ?_⟩
    · convert dvd_sub hq₁d hp₁d using 1; ring
    · convert dvd_sub hq₂d hp₂d using 1; ring
  · rintro ⟨w₂, hw₂, hw₁d, hw₂d⟩
    refine ⟨p₂ + w₂, by linear_combination hp₂ + hw₂, ?_, ?_⟩
    · convert dvd_add hp₁d (dvd_mul_of_dvd_right hw₁d (b : ℤ)) using 1; ring
    · convert dvd_add hp₂d (dvd_mul_of_dvd_right hw₂d (b : ℤ)) using 1; ring

/-- All pair differences in a set, with no extra closure operation. -/
@[expose] public def differences (S : Set (ℤ × ℤ)) : Set (ℤ × ℤ) :=
  {w | ∃ p ∈ S, ∃ q ∈ S, p - q = w}

public theorem sub_mem_lattice_of_mem_fiber (hbe : b ∣ e) (hea : e.Coprime (a₁ * a₂))
    {p q : ℤ × ℤ} (hp : p ∈ fiber F₁ F₂ d e b a₁ a₂ ρ C)
    (hq : q ∈ fiber F₁ F₂ d e b a₁ a₂ ρ C) : p - q ∈ lattice F₁ F₂ (step d e b) a₁ a₂ :=
  (add_mem_fiber_iff hbe hea hq).1 (by simpa only [add_comm q, sub_add_cancel] using hp)

/-- Every homogeneous vector is realized as a difference, by adding it to a point
of the nonempty *full* filter. -/
public theorem differences_fiber_eq (hbe : b ∣ e) (hea : e.Coprime (a₁ * a₂))
    (hne : (fiber F₁ F₂ d e b a₁ a₂ ρ C).Nonempty) :
    differences (fiber F₁ F₂ d e b a₁ a₂ ρ C) = ↑(lattice F₁ F₂ (step d e b) a₁ a₂) := by
  ext w
  constructor
  · rintro ⟨p, hp, q, hq, rfl⟩
    exact sub_mem_lattice_of_mem_fiber hbe hea hp hq
  · intro hw
    obtain ⟨p, hp⟩ := hne
    exact ⟨p + w, (add_mem_fiber_iff hbe hea hp).2 hw, p, hp, add_sub_cancel_left _ _⟩

private theorem bezout_three {A D : ℤ} {M : ℕ} (h : (A.gcd D).Coprime M) :
    ∃ x y k : ℤ, A * x - D * y + (M : ℤ) * k = 1 := by
  let g : ℤ := (A.gcd D : ℕ)
  have hg : g.gcd (M : ℤ) = 1 := by
    simpa only [g, Int.gcd_natCast_natCast] using h.gcd_eq_one
  have h₁ := Int.gcd_eq_gcd_ab g (M : ℤ)
  rw [hg, Nat.cast_one] at h₁
  have h₂ : g = A * A.gcdA D + D * A.gcdB D := Int.gcd_eq_gcd_ab A D
  refine ⟨A.gcdA D * g.gcdA M, -(A.gcdB D * g.gcdA M), g.gcdB M, ?_⟩
  linear_combination -h₁ - g.gcdA M * h₂

-- Lift the first target residue and then correct the second without changing the first.
private theorem residueMap_surjective {D : ℤ}
    (h : ((F₂ * (a₁ : ℤ)).gcd D).Coprime (F₁ * a₂)) :
    Function.Surjective (residueMap F₁ F₂ D a₁ a₂) := by
  obtain ⟨x, y, k, hk⟩ := bezout_three h
  intro r
  obtain ⟨x₀, hx₀⟩ := ZMod.intCast_surjective r.1
  obtain ⟨z₀, hz₀⟩ := ZMod.intCast_surjective r.2
  let R := z₀ - F₂ * x₀
  refine ⟨(x₀ + (a₁ : ℤ) * (R * x), R * y), Prod.ext ?_ ?_⟩
  · change ((x₀ + (a₁ : ℤ) * (R * x) : ℤ) : ZMod a₁) = r.1
    simpa [Int.cast_add, Int.cast_mul] using hx₀
  · change ((F₂ * (x₀ + (a₁ : ℤ) * (R * x)) - D * (R * y) : ℤ) : ZMod (F₁ * a₂)) = r.2
    rw [← hz₀]
    apply sub_eq_zero.mp
    rw [← Int.cast_sub, ZMod.intCast_zmod_eq_zero_iff_dvd]
    refine ⟨-(R * k), ?_⟩
    dsimp only [R]
    linear_combination (z₀ - F₂ * x₀) * hk

private theorem lattice_index {D : ℤ} (h : ((F₂ * (a₁ : ℤ)).gcd D).Coprime (F₁ * a₂)) :
    (lattice F₁ F₂ D a₁ a₂).index = F₁ * a₁ * a₂ := by
  let E := QuotientAddGroup.quotientKerEquivOfSurjective
    (residueMap F₁ F₂ D a₁ a₂) (residueMap_surjective h)
  change Nat.card ((ℤ × ℤ) ⧸ (residueMap F₁ F₂ D a₁ a₂).ker) = _
  rw [Nat.card_congr E.toEquiv, Nat.card_prod, Nat.card_zmod, Nat.card_zmod,
    ← Nat.mul_assoc, Nat.mul_comm a₁ F₁]

-- The normalized step need not be a unit modulo F₁. Cancel a₁ from the gcd
-- with the first coefficient instead, using that the step is coprime to a₁.
private theorem coefficient_coprime (hF : F₁.Coprime F₂.natAbs)
    (hde : d.Coprime (F₁ * a₁ * a₂)) (hea : e.Coprime (a₁ * a₂)) (hbe : b ∣ e) :
    ((F₂ * (a₁ : ℤ)).gcd (step d e b)).Coprime (F₁ * a₂) := by
  let g := (F₂ * (a₁ : ℤ)).gcd (step d e b)
  have hgD : g ∣ d * (e / b) := by
    simpa only [g, step, ← Nat.cast_mul, Int.natCast_dvd_natCast] using
      Int.gcd_dvd_right (F₂ * (a₁ : ℤ)) (step d e b)
  have hgA : g ∣ F₂.natAbs * a₁ := by
    simpa only [g, Int.ofNat_dvd_left, Int.natAbs_mul, Int.natAbs_natCast] using
      Int.gcd_dvd_left (F₂ * (a₁ : ℤ)) (step d e b)
  have hdA := hde.of_dvd_right (show a₁ * a₂ ∣ F₁ * a₁ * a₂ by
    rw [Nat.mul_assoc]; exact Nat.dvd_mul_left _ _)
  have hg := Nat.Coprime.of_dvd_left hgD
    (hdA.mul_left (Nat.Coprime.of_dvd_left (Nat.div_dvd_of_dvd hbe) hea))
  have hgF₂ := (hg.of_dvd_right (Nat.dvd_mul_right a₁ a₂)).dvd_of_dvd_mul_right hgA
  exact (hF.symm.of_dvd_left hgF₂).mul_right (hg.of_dvd_right (Nat.dvd_mul_left a₂ a₁))

private theorem base_coefficient_coprime (hF : F₁.Coprime F₂.natAbs) :
    ((F₂ * (1 : ℤ)).gcd (step d e b)).Coprime (F₁ * 1) := by
  simpa using hF.symm.of_dvd_left (Int.gcd_dvd_natAbs_left F₂ (step d e b))

/-- The base difference lattice has index `F₁`. With no filters there are no
coprimality requirements on the determinant step. -/
public theorem base_index (hF : F₁.Coprime F₂.natAbs) :
    (lattice F₁ F₂ (step d e b) 1 1).index = F₁ := by
  simpa using lattice_index (base_coefficient_coprime (d := d) (e := e) (b := b) hF)

/-- The full unfiltered affine fiber also realizes every vector in its base
lattice as a difference, provided it is nonempty. -/
public theorem base_fiber_difference_index (hF : F₁.Coprime F₂.natAbs) (hbe : b ∣ e)
    (hne : (fiber F₁ F₂ d e b 1 1 ρ C).Nonempty) :
    differences (fiber F₁ F₂ d e b 1 1 ρ C) = ↑(lattice F₁ F₂ (step d e b) 1 1) ∧
    (lattice F₁ F₂ (step d e b) 1 1).index = F₁ :=
  ⟨differences_fiber_eq hbe (by simp) hne, base_index hF⟩

/-- Exact index of the full nonempty filtered affine difference lattice in
`(z₁,s)`. The positivity and split assumptions are those of the box sieve;
the quotient computation itself does not need all of them. -/
public theorem filtered_fiber_difference_index (_hF₁ : 0 < F₁) (_hd : 0 < d) (_he : 0 < e)
    (_hb : 0 < b) (_ha₁ : 0 < a₁) (_ha₂ : 0 < a₂) (hF : F₁.Coprime F₂.natAbs)
    (_hsplit : a₁.Coprime a₂) (hde : d.Coprime (F₁ * a₁ * a₂))
    (hea : e.Coprime (a₁ * a₂)) (hbe : b ∣ e)
    (hne : (fiber F₁ F₂ d e b a₁ a₂ ρ C).Nonempty) :
    differences (fiber F₁ F₂ d e b a₁ a₂ ρ C) = ↑(lattice F₁ F₂ (step d e b) a₁ a₂) ∧
    (lattice F₁ F₂ (step d e b) a₁ a₂).index = F₁ * a₁ * a₂ :=
  ⟨differences_fiber_eq hbe hea hne, lattice_index (coefficient_coprime hF hde hea hbe)⟩

/-- A divisor pair weakens the spatial filters and inherits the index formula
with its own product. A point in the original filter witnesses nonemptiness. -/
public theorem subfilter_fiber_difference_index {a₁' a₂' : ℕ} (ha₁' : a₁' ∣ a₁) (ha₂' : a₂' ∣ a₂)
    (hF : F₁.Coprime F₂.natAbs) (hde : d.Coprime (F₁ * a₁ * a₂))
    (hea : e.Coprime (a₁ * a₂)) (hbe : b ∣ e)
    (hne : (fiber F₁ F₂ d e b a₁ a₂ ρ C).Nonempty) :
    differences (fiber F₁ F₂ d e b a₁' a₂' ρ C) = ↑(lattice F₁ F₂ (step d e b) a₁' a₂') ∧
    (lattice F₁ F₂ (step d e b) a₁' a₂').index = F₁ * a₁' * a₂' := by
  have hde' := hde.of_dvd_right (Nat.mul_dvd_mul (Nat.mul_dvd_mul_left F₁ ha₁') ha₂')
  have hea' := hea.of_dvd_right (Nat.mul_dvd_mul ha₁' ha₂')
  obtain ⟨p, z₂, hz, h₁, h₂⟩ := hne
  have hp : p ∈ fiber F₁ F₂ d e b a₁' a₂' ρ C :=
    ⟨z₂, hz, (Int.natCast_dvd_natCast.mpr ha₁').trans h₁,
      (Int.natCast_dvd_natCast.mpr ha₂').trans h₂⟩
  exact ⟨differences_fiber_eq hbe hea' ⟨p, hp⟩,
    lattice_index (coefficient_coprime hF hde' hea' hbe)⟩

/-- The signed determinant of chart vectors, not of the physical vectors. -/
@[expose] public def det (u v : ℤ × ℤ) : ℤ := u.1 * v.2 - v.1 * u.2

private theorem lattice_dvd_det {D : ℤ} (h : ((F₂ * (a₁ : ℤ)).gcd D).Coprime (F₁ * a₂))
    {u v : ℤ × ℤ} (hu : u ∈ lattice F₁ F₂ D a₁ a₂) (hv : v ∈ lattice F₁ F₂ D a₁ a₂) :
    ((F₁ * a₁ * a₂ : ℕ) : ℤ) ∣ det u v := by
  obtain ⟨X, Y, K, hK⟩ := bezout_three h
  obtain ⟨⟨x, hx⟩, k, hk⟩ := mem_lattice.mp hu
  obtain ⟨⟨y, hy⟩, l, hl⟩ := mem_lattice.mp hv
  have hU : F₂ * (a₁ : ℤ) * x - D * u.2 = (F₁ : ℤ) * (a₂ : ℤ) * k := by
    linear_combination hk - F₂ * hx
  have hV : F₂ * (a₁ : ℤ) * y - D * v.2 = (F₁ : ℤ) * (a₂ : ℤ) * l := by
    linear_combination hl - F₂ * hy
  simp only [Nat.cast_mul, det] at hK ⊢
  -- The two residual congruences and the Bézout identity cancel both
  -- coefficients from the determinant of the scaled vectors.
  refine ⟨(v.2 * X - y * Y) * k - (u.2 * X - x * Y) * l + K * (x * v.2 - y * u.2), ?_⟩
  linear_combination (a₁ : ℤ) * ((v.2 * X - y * Y) * hU - (u.2 * X - x * Y) * hV -
    (x * v.2 - y * u.2) * hK) + v.2 * hx - u.2 * hy

/-- Determinants of two differences of filtered points are multiples of the full
lattice index. The four points may be taken from any subset, bounded or not. -/
public theorem dvd_det_of_mem_fiber (hF : F₁.Coprime F₂.natAbs)
    (hde : d.Coprime (F₁ * a₁ * a₂)) (hea : e.Coprime (a₁ * a₂)) (hbe : b ∣ e)
    {p q r s : ℤ × ℤ} (hp : p ∈ fiber F₁ F₂ d e b a₁ a₂ ρ C)
    (hq : q ∈ fiber F₁ F₂ d e b a₁ a₂ ρ C) (hr : r ∈ fiber F₁ F₂ d e b a₁ a₂ ρ C)
    (hs : s ∈ fiber F₁ F₂ d e b a₁ a₂ ρ C) :
    ((F₁ * a₁ * a₂ : ℕ) : ℤ) ∣ det (p - q) (r - s) :=
  lattice_dvd_det (coefficient_coprime hF hde hea hbe)
    (sub_mem_lattice_of_mem_fiber hbe hea hp hq) (sub_mem_lattice_of_mem_fiber hbe hea hr hs)

/-- In the unfiltered chart, determinants of differences are multiples of `F₁`
without any coprimality restriction on `d` or `e`. -/
public theorem base_dvd_det_of_mem_fiber (hF : F₁.Coprime F₂.natAbs) (hbe : b ∣ e)
    {p q r s : ℤ × ℤ} (hp : p ∈ fiber F₁ F₂ d e b 1 1 ρ C)
    (hq : q ∈ fiber F₁ F₂ d e b 1 1 ρ C) (hr : r ∈ fiber F₁ F₂ d e b 1 1 ρ C)
    (hs : s ∈ fiber F₁ F₂ d e b 1 1 ρ C) :
    (F₁ : ℤ) ∣ det (p - q) (r - s) := by
  simpa using lattice_dvd_det (base_coefficient_coprime hF)
    (sub_mem_lattice_of_mem_fiber hbe (by simp) hp hq)
    (sub_mem_lattice_of_mem_fiber hbe (by simp) hr hs)

/-- A determinant bound strictly below the index forces the two differences to
be collinear. No conclusion about generation by the bounded points is needed. -/
public theorem det_eq_zero_of_natAbs_lt (hF : F₁.Coprime F₂.natAbs)
    (hde : d.Coprime (F₁ * a₁ * a₂)) (hea : e.Coprime (a₁ * a₂)) (hbe : b ∣ e)
    {p q r s : ℤ × ℤ} (hp : p ∈ fiber F₁ F₂ d e b a₁ a₂ ρ C)
    (hq : q ∈ fiber F₁ F₂ d e b a₁ a₂ ρ C) (hr : r ∈ fiber F₁ F₂ d e b a₁ a₂ ρ C)
    (hs : s ∈ fiber F₁ F₂ d e b a₁ a₂ ρ C)
    (hsmall : (det (p - q) (r - s)).natAbs < F₁ * a₁ * a₂) : det (p - q) (r - s) = 0 :=
  Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (dvd_det_of_mem_fiber hF hde hea hbe hp hq hr hs)
    (by simpa only [Int.natAbs_natCast] using hsmall)

end AffineDeterminantIndex
