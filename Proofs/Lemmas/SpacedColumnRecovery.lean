module

public import Lemmas.SpacedGapIncidences
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Max
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.Linarith

/-!
# Recovering spaced columns from actual modulus–point incidences

Source: `a9dedc89666e:.godel/alice/spaced-product-cut.md:15–27`, unchanged at
`7817ec43` and Lean base `6467546b`. This is the finite `1 ≤ s ≤ L ≤ H` link
from `SpacedGapIncidences.incidenceCount` toward the fixed-cofactor `hgap_le`
input of `SpacedProductFibers.card_productFiber_le`.

Scope: each actual column has a distinct chosen row completion and a chosen
eligible crossing `f ∣ d` with affine coordinates `(j,b)`. The physical
nonvanishing, divisibility by `d`, and positive-divisor budget are premises;
there is no cancellation of `q` or coprimality assumption on `s` and `d`.
The result neither constructs a crossing nor estimates the asymptotic price.

Owning check session: `01a20fda-fdc5-7fd5-bef7-0dc0da54e6c0`.
-/

namespace SpacedColumnRecovery

open scoped BigOperators
open SpacedGapIncidences SpacedGapModuli

/-- The four coordinates of a column at fixed row inputs. Positivity and the
lower bound for `d` are imposed when counting completions. -/
public structure Completion where
  c : ℤ
  d : ℕ
  y₁ : ℤ
  y₂ : ℤ

private abbrev Incidence := Σ _ : ℕ, ℤ × ℤ

private noncomputable def incidences (a₀ s A B : ℤ) (j₀ b₀ L H : ℝ) (X : ℕ) :
    Finset Incidence :=
  (eligibleModuli A B (L / (s : ℝ)) H X).sigma (affineSolutions a₀ s A B j₀ b₀ L H)

private theorem card_incidences (a₀ s A B : ℤ) (j₀ b₀ L H : ℝ) (X : ℕ) :
    (incidences a₀ s A B j₀ b₀ L H X).card = incidenceCount a₀ s A B j₀ b₀ L H X := by
  rw [incidences, Finset.card_sigma, incidenceCount]

private theorem chosen_mem_incidences
    {a₀ s A B a b : ℤ} {j₀ b₀ L H : ℝ} {X f d : ℕ} {p : ℤ × ℤ}
    (hf : f ∈ eligibleModuli A B (L / (s : ℝ)) H X) (hfd : f ∣ d)
    (hbox : |(p.1 : ℝ) - j₀| ≤ L / (s : ℝ) ∧ |(p.2 : ℝ) - b₀| ≤ H)
    (ha : a = a₀ + s * p.1) (hb : b = p.2)
    (hN : A * a - B * b ≠ 0) (hd : (d : ℤ) ∣ A * a - B * b) :
    (⟨f, p⟩ : Incidence) ∈ incidences a₀ s A B j₀ b₀ L H X := by
  apply Finset.mem_sigma.mpr
  refine ⟨hf, mem_affineSolutions.mpr ⟨hbox, ?_⟩⟩
  rw [← ha, ← hb]
  exact ⟨hN, dvd_trans (Int.natCast_dvd_natCast.mpr hfd) hd⟩

private theorem first_row_modEq {x r c c' y y' : ℤ} {d : ℕ}
    (hd : 0 < d) (hx : Int.gcd x (d : ℤ) = 1)
    (h : c * x - (d : ℤ) * y = r) (h' : c' * x - (d : ℤ) * y' = r) :
    c ≡ c' [ZMOD (d : ℤ)] := by
  have hmul : c * x ≡ c' * x [ZMOD (d : ℤ)] :=
    Int.modEq_iff_dvd.mpr ⟨y' - y, by rw [mul_sub]; linarith only [h, h']⟩
  have hc := Int.ModEq.cancel_right_div_gcd (Int.natCast_pos.mpr hd) hmul
  simpa only [Int.gcd_comm (d : ℤ) x, hx, Nat.cast_one, Int.ediv_one] using hc

private theorem row_forces_y {x r c y y' : ℤ} {d : ℕ} (hd : 0 < d)
    (h : c * x - (d : ℤ) * y = r) (h' : c * x - (d : ℤ) * y' = r) : y = y' := by
  apply mul_left_cancel₀ (Int.natCast_pos.mpr hd).ne'
  linarith only [h, h']

/-- In a nonempty residue fiber, count integer steps from its least occurring `c`. -/
private theorem card_residue_interval_le {Column : Type*} (F : Finset Column) (c : Column → ℤ)
    {C Z : ℝ} {d dMin : ℕ} (hmin : 0 < dMin) (hd : dMin ≤ d) (hZ : 0 ≤ Z)
    (hc : ∀ w ∈ F, C ≤ (c w : ℝ) ∧ (c w : ℝ) ≤ C + Z)
    (hres : ∀ w ∈ F, ∀ w' ∈ F, c w ≡ c w' [ZMOD (d : ℤ)])
    (hinj : Set.InjOn c (↑F : Set Column)) :
    F.card ≤ 1 + ⌊Z / (dMin : ℝ)⌋₊ := by
  classical
  by_cases hne : F.Nonempty
  · obtain ⟨m, hm, hmmin⟩ := Finset.exists_min_image F c hne
    let step (w : Column) : ℤ := (c w - c m) / (d : ℤ)
    let slot (w : Column) : ℕ := (step w).toNat
    have hstep (w) (hw : w ∈ F) : c w - c m = (d : ℤ) * step w := by
      have hdiv := Int.modEq_iff_dvd.mp (hres m hm w hw)
      exact (Int.ediv_mul_cancel hdiv).symm.trans (mul_comm _ _)
    have hslot (w) (hw : w ∈ F) : (slot w : ℤ) = step w :=
      Int.toNat_of_nonneg (Int.ediv_nonneg (sub_nonneg.mpr (hmmin w hw)) (Int.natCast_nonneg d))
    have hprod (w) (hw : w ∈ F) : (c w : ℝ) - (c m : ℝ) = (d : ℝ) * (slot w : ℝ) := by
      have hwstep := hstep w hw
      rw [← hslot w hw] at hwstep
      exact_mod_cast hwstep
    rw [← Finset.card_range (1 + ⌊Z / (dMin : ℝ)⌋₊)]
    apply Finset.card_le_card_of_injOn slot
    · intro w hw
      have hmul : (slot w : ℝ) * (dMin : ℝ) ≤ Z := calc
        _ ≤ (slot w : ℝ) * (d : ℝ) :=
          mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hd) (Nat.cast_nonneg _)
        _ = (c w : ℝ) - (c m : ℝ) := by rw [hprod w hw, mul_comm]
        _ ≤ Z := by linarith only [(hc w hw).2, (hc m hm).1]
      have hmin' : (0 : ℝ) < dMin := Nat.cast_pos.mpr hmin
      have hfloor := (Nat.le_floor_iff (div_nonneg hZ hmin'.le)).mpr
        ((le_div_iff₀ hmin').mpr hmul)
      exact Finset.mem_range.mpr (by omega)
    · intro w hw w' hw' heq
      apply hinj hw hw'
      have hs : step w = step w' := (hslot w hw).symm.trans
        ((congrArg (fun n : ℕ => (n : ℤ)) heq).trans (hslot w' hw'))
      have hwstep := hstep w hw
      rw [hs] at hwstep
      linarith only [hwstep, hstep w' hw']
  · simp [Finset.not_nonempty_iff_eq_empty.mp hne]

/-- For fixed physical gaps, partition by the positive divisors allowed for `d`,
then count one residue class per modulus. -/
private theorem card_fixed_gaps_le {Column : Type*} (F : Finset Column)
    (completion : Column → Completion) {x₁ x₂ q a b N : ℤ} {C Z : ℝ} {dMin D : ℕ}
    (hmin : 0 < dMin) (hZ : 0 ≤ Z) (hN : N ≠ 0) (hD : N.natAbs.divisors.card ≤ D)
    (hdvd : ∀ w ∈ F, ((completion w).d : ℤ) ∣ N)
    (hdMin : ∀ w ∈ F, dMin ≤ (completion w).d)
    (hgcd : ∀ w ∈ F, Int.gcd x₁ ((completion w).d : ℤ) = 1)
    (hc : ∀ w ∈ F, C ≤ ((completion w).c : ℝ) ∧ ((completion w).c : ℝ) ≤ C + Z)
    (hrows : ∀ w ∈ F, let k := completion w
      k.c * x₁ - (k.d : ℤ) * k.y₁ = q * a ∧ k.c * x₂ - (k.d : ℤ) * k.y₂ = q * b)
    (hinj : Set.InjOn completion (↑F : Set Column)) :
    F.card ≤ D * (1 + ⌊Z / (dMin : ℝ)⌋₊) := by
  classical
  let byModulus (d : ℕ) := F.filter fun w => (completion w).d = d
  have hmaps : Set.MapsTo (fun w => (completion w).d) (↑F : Set Column) ↑N.natAbs.divisors := by
    intro w hw
    refine Nat.mem_divisors.mpr ⟨?_, Int.natAbs_ne_zero.mpr hN⟩
    simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr (hdvd w hw)
  have hlocal (d : ℕ) : (byModulus d).card ≤ 1 + ⌊Z / (dMin : ℝ)⌋₊ := by
    by_cases hne : (byModulus d).Nonempty
    · obtain ⟨m, hm⟩ := hne
      obtain ⟨hmF, hmd⟩ := Finset.mem_filter.mp hm
      have hd : dMin ≤ d := hmd ▸ hdMin m hmF
      have hdpos : 0 < d := hmin.trans_le hd
      have hx : Int.gcd x₁ (d : ℤ) = 1 := hmd ▸ hgcd m hmF
      have hr (w) (hw : w ∈ byModulus d) :
          (completion w).c * x₁ - (d : ℤ) * (completion w).y₁ = q * a ∧
          (completion w).c * x₂ - (d : ℤ) * (completion w).y₂ = q * b := by
        obtain ⟨hwF, hwd⟩ := Finset.mem_filter.mp hw
        simpa only [hwd] using hrows w hwF
      apply card_residue_interval_le (byModulus d) (fun w => (completion w).c) hmin hd hZ
      · exact fun w hw => hc w (Finset.mem_filter.mp hw).1
      · exact fun w hw w' hw' => first_row_modEq hdpos hx (hr w hw).1 (hr w' hw').1
      · intro w hw w' hw' heq
        obtain ⟨hwF, hwd⟩ := Finset.mem_filter.mp hw
        obtain ⟨hw'F, hw'd⟩ := Finset.mem_filter.mp hw'
        apply hinj hwF hw'F
        obtain ⟨hr₁, hr₂⟩ := hr w hw
        obtain ⟨hr₁', hr₂'⟩ := hr w' hw'
        change (completion w).c = (completion w').c at heq
        rw [heq] at hr₁ hr₂
        have hy₁ := row_forces_y hdpos hr₁ hr₁'
        have hy₂ := row_forces_y hdpos hr₂ hr₂'
        change Completion.mk (completion w).c (completion w).d (completion w).y₁ (completion w).y₂ =
          Completion.mk (completion w').c (completion w').d (completion w').y₁ (completion w').y₂
        rw [Completion.mk.injEq]
        exact ⟨heq, hwd.trans hw'd.symm, hy₁, hy₂⟩
    · simp [Finset.not_nonempty_iff_eq_empty.mp hne]
  calc
    F.card = ∑ d ∈ N.natAbs.divisors, (byModulus d).card :=
      Finset.card_eq_sum_card_fiberwise hmaps
    _ ≤ ∑ _d ∈ N.natAbs.divisors, (1 + ⌊Z / (dMin : ℝ)⌋₊) :=
      Finset.sum_le_sum fun d _ => hlocal d
    _ = N.natAbs.divisors.card * (1 + ⌊Z / (dMin : ℝ)⌋₊) := by simp
    _ ≤ D * (1 + ⌊Z / (dMin : ℝ)⌋₊) := Nat.mul_le_mul_right _ hD

/-- Bound the actual columns in a fixed-row spaced rectangle. The chosen crossing
and point are used only to assign the column to an incidence; all divisor charges
inside that fiber use the physical value `A * gap₁ - B * gap₂`, not a direction
form. `hcompletion` says that the column objects have distinct chosen coordinate
completions. In particular, taking the columns to be the completions themselves
requires no separate identification of columns with gap pairs. -/
public theorem card_columns_le {Column : Type*} (columns : Finset Column)
    (completion : Column → Completion) (gap₁ gap₂ : Column → ℤ)
    (f : Column → ℕ) (point : Column → ℤ × ℤ)
    {x₁ x₂ q a₀ s : ℤ} {j₀ b₀ L H C Z : ℝ} {X D dMin : ℕ}
    (_hs : 1 ≤ s) (_hsL : (s : ℝ) ≤ L) (_hLH : L ≤ H) (_hq : 0 < q)
    (hmin : 0 < dMin) (hZ : 0 ≤ Z)
    (hbox : ∀ w ∈ columns,
      |((point w).1 : ℝ) - j₀| ≤ L / (s : ℝ) ∧ |((point w).2 : ℝ) - b₀| ≤ H)
    (hgaps : ∀ w ∈ columns, gap₁ w = a₀ + s * (point w).1 ∧ gap₂ w = (point w).2)
    (hdMin : ∀ w ∈ columns, dMin ≤ (completion w).d)
    (hgcd : ∀ w ∈ columns, Int.gcd x₁ ((completion w).d : ℤ) = 1)
    (hc : ∀ w ∈ columns, C ≤ ((completion w).c : ℝ) ∧ ((completion w).c : ℝ) ≤ C + Z)
    (hrows : ∀ w ∈ columns, let k := completion w
      k.c * x₁ - (k.d : ℤ) * k.y₁ = q * gap₁ w ∧
      k.c * x₂ - (k.d : ℤ) * k.y₂ = q * gap₂ w)
    (hcompletion : Set.InjOn completion (↑columns : Set Column)) :
    let g := Int.gcd x₁ x₂
    let A := x₂ / (g : ℤ)
    let B := x₁ / (g : ℤ)
    (∀ w ∈ columns, f w ∈ eligibleModuli A B (L / (s : ℝ)) H X ∧ f w ∣ (completion w).d) →
    (∀ w ∈ columns, let N := A * gap₁ w - B * gap₂ w
      N ≠ 0 ∧ ((completion w).d : ℤ) ∣ N ∧ N.natAbs.divisors.card ≤ D) →
    columns.card ≤ incidenceCount a₀ s A B j₀ b₀ L H X * D * (1 + ⌊Z / (dMin : ℝ)⌋₊) := by
  intro g A B hcross hphysical
  classical
  let incidence (w : Column) : Incidence := ⟨f w, point w⟩
  let I := incidences a₀ s A B j₀ b₀ L H X
  let fiber (i : Incidence) := columns.filter fun w => incidence w = i
  have hmaps : Set.MapsTo incidence (↑columns : Set Column) (↑I : Set Incidence) := by
    intro w hw
    obtain ⟨hf, hfd⟩ := hcross w hw
    obtain ⟨ha, hb⟩ := hgaps w hw
    obtain ⟨hN, hd, _⟩ := hphysical w hw
    exact chosen_mem_incidences hf hfd (hbox w hw) ha hb hN hd
  have hcount (i : Incidence) : (fiber i).card ≤ D * (1 + ⌊Z / (dMin : ℝ)⌋₊) := by
    by_cases hne : (fiber i).Nonempty
    · let a := a₀ + s * i.2.1
      let b := i.2.2
      let N := A * a - B * b
      have hfiber (w) (hw : w ∈ fiber i) : w ∈ columns ∧ gap₁ w = a ∧ gap₂ w = b := by
        obtain ⟨hw', hwi⟩ := Finset.mem_filter.mp hw
        have hp : point w = i.2 := congrArg (fun k : Incidence => k.2) hwi
        obtain ⟨ha, hb⟩ := hgaps w hw'
        exact ⟨hw', by simpa only [hp, a] using ha, by simpa only [hp, b] using hb⟩
      have hphys (w) (hw : w ∈ fiber i) :
          N ≠ 0 ∧ ((completion w).d : ℤ) ∣ N ∧ N.natAbs.divisors.card ≤ D := by
        obtain ⟨hw', ha, hb⟩ := hfiber w hw
        simpa only [ha, hb, N] using hphysical w hw'
      obtain ⟨w₀, hw₀⟩ := hne
      obtain ⟨hN, _, hD⟩ := hphys w₀ hw₀
      refine card_fixed_gaps_le (a := a) (b := b) (x₁ := x₁) (x₂ := x₂) (q := q) (C := C)
        (fiber i) completion hmin hZ hN hD (fun w hw => (hphys w hw).2.1) ?_ ?_ ?_ ?_ ?_
      · exact fun w hw => hdMin w (hfiber w hw).1
      · exact fun w hw => hgcd w (hfiber w hw).1
      · exact fun w hw => hc w (hfiber w hw).1
      · intro w hw
        obtain ⟨hw', ha, hb⟩ := hfiber w hw
        simpa only [ha, hb] using hrows w hw'
      · exact fun w hw w' hw' => hcompletion (hfiber w hw).1 (hfiber w' hw').1
    · simp [Finset.not_nonempty_iff_eq_empty.mp hne]
  calc
    columns.card = ∑ i ∈ I, (fiber i).card := Finset.card_eq_sum_card_fiberwise hmaps
    _ ≤ ∑ _i ∈ I, D * (1 + ⌊Z / (dMin : ℝ)⌋₊) := Finset.sum_le_sum fun i _ => hcount i
    _ = I.card * D * (1 + ⌊Z / (dMin : ℝ)⌋₊) := by simp [Nat.mul_assoc]
    _ = _ := by rw [card_incidences]

end SpacedColumnRecovery
