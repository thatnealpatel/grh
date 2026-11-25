module

public import Lemmas.FixedInputPartner
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Choose

/-!
# Crossing endpoint count at a fixed actual input

Source: `00e46ec:.godel/alice/input-first-erasure.md:55–90`, with the decoder
clarification at `542813da:.godel/alice/input-first-erasure.md:81–93`.

This is the finite, per-input count. It charges the full erased part, a pivot
multiplier in the appropriate region, and one divisor specifying the split into
the two filters. It makes no input-sum, Rankin, or asymptotic estimate.

Owning check session: `01a21012-2ca1-71e9-a51f-6efd061fa400`.
-/

namespace FixedInputCrossingCount

/-- The primitive signed row of an actual endpoint `d`, before installing filters. -/
public structure IsActualRow (c F₂ q : ℕ) (U H₀ cutoff : ℝ) (d : ℕ)
    (h β : ℤ) (Z : ℕ) : Prop where
  h_pos : 0 < h
  h_le : (h : ℝ) ≤ U
  beta_bound : |(β : ℝ)| ≤ H₀
  primitive : h.gcd β = 1
  output_pos : 0 < d * Z
  output_eq : (c : ℤ) * (F₂ : ℤ) * h - (q : ℤ) * β = ((d * Z : ℕ) : ℤ)
  longest_prefix : FixedInputPartner.IsLongestPrimePrefix cutoff (d * Z) d

private theorem fitsCode_of_actualRow {v e c F₂ q f_h f_Z d Z : ℕ}
    {h β : ℤ} {U H₀ cutoff : ℝ} (hr : IsActualRow c F₂ q U H₀ cutoff d h β Z)
    (hh : f_h ∣ h.natAbs) (hZ : f_Z ∣ Z) :
    FixedInputPartner.FitsCode v e c F₂ q U H₀ cutoff f_h f_Z (v, d, e) := by
  refine ⟨rfl, rfl, h, β, Z, hr.h_pos, hr.h_le, hr.beta_bound, hr.primitive, ?_, ?_,
    hr.output_pos, hr.output_eq.symm, hr.longest_prefix⟩
  · simpa only [Int.natAbs_of_nonneg hr.h_pos.le] using Int.natCast_dvd_natCast.mpr hh
  · rw [hr.output_eq]
    exact Int.natCast_dvd_natCast.mpr (hZ.trans (dvd_mul_left Z d))

private theorem endpoint_eq_of_filters {v c F₂ q f_h f_Z d₁ d₂ Z₁ Z₂ : ℕ}
    {h₁ h₂ β₁ β₂ : ℤ} {U H₀ cutoff : ℝ}
    (hr₁ : IsActualRow c F₂ q U H₀ cutoff d₁ h₁ β₁ Z₁)
    (hr₂ : IsActualRow c F₂ q U H₀ cutoff d₂ h₂ β₂ Z₂)
    (hh₁ : f_h ∣ h₁.natAbs) (hZ₁ : f_Z ∣ Z₁) (hh₂ : f_h ∣ h₂.natAbs) (hZ₂ : f_Z ∣ Z₂)
    (hh : 0 < f_h) (hZ : 0 < f_Z) (hq : q.Coprime f_Z)
    (hcross : 2 * U * H₀ < (f_h : ℝ) * (f_Z : ℝ)) : d₁ = d₂ := by
  -- Both actual triples have the same input; the last coordinate is only bookkeeping.
  have heq := FixedInputPartner.triple_eq_of_fitsCode hh hZ hq hcross
    (fitsCode_of_actualRow (v := v) (e := 0) hr₁ hh₁ hZ₁)
    (fitsCode_of_actualRow (v := v) (e := 0) hr₂ hh₂ hZ₂)
  exact congrArg (fun t : ℕ × ℕ × ℕ ↦ t.2.1) heq

/-- The full `S`-part retains every occurrence of each selected prime. -/
@[expose] public def fullPart (S : Finset ℕ) (n : ℕ) : ℕ :=
  (n.primeFactorsList.filter (fun p ↦ p ∈ S)).prod

private theorem fullPart_pos (S : Finset ℕ) (n : ℕ) : 0 < fullPart S n :=
  List.prod_pos fun _ hp ↦ (Nat.prime_of_mem_primeFactorsList (List.mem_of_mem_filter hp)).pos

private theorem fullPart_supported (S : Finset ℕ) (n : ℕ) {p : ℕ}
    (hp : p ∈ (fullPart S n).primeFactorsList) : p ∈ S := by
  have hperm : List.Perm (n.primeFactorsList.filter (fun p ↦ p ∈ S)) (fullPart S n).primeFactorsList :=
    Nat.primeFactorsList_unique rfl fun _ h ↦
      Nat.prime_of_mem_primeFactorsList (List.mem_of_mem_filter h)
  simpa using (List.mem_filter.mp (hperm.mem_iff.mpr hp)).2

private theorem fullPart_mul_dvd {E P : Finset ℕ} (hdisj : Disjoint E P)
    {n : ℕ} (hn : n ≠ 0) : fullPart E n * fullPart P n ∣ n := by
  have hprod (ps : List ℕ) :
      (ps.filter (fun p ↦ p ∈ E)).prod * (ps.filter (fun p ↦ p ∈ P)).prod =
        (ps.filter (fun p ↦ decide (p ∈ E) || decide (p ∈ P))).prod := by
    induction ps with
    | nil => simp
    | cons p ps ih =>
      by_cases he : p ∈ E
      · have hp : p ∉ P := fun hp ↦ (Finset.disjoint_left.mp hdisj) he hp
        simp [he, hp, ← ih]; ac_rfl
      · by_cases hp : p ∈ P
        · simp [he, hp, ← ih]; ac_rfl
        · simpa [he, hp] using ih
  rw [fullPart, fullPart, hprod]
  simpa only [Nat.prod_primeFactorsList hn] using
    (List.filter_sublist (p := fun p ↦ decide (p ∈ E) || decide (p ∈ P))
      (l := n.primeFactorsList)).prod_dvd_prod

private theorem coprime_fullPart {q : ℕ} {S : Finset ℕ}
    (hq : ∀ p ∈ S, q.Coprime p) (n : ℕ) : q.Coprime (fullPart S n) := by
  have hprod (ps : List ℕ) (hs : ∀ p ∈ ps, q.Coprime p) : q.Coprime ps.prod := by
    induction ps with
    | nil => simp
    | cons p ps ih =>
      exact (hs p (List.mem_cons_self ..)).mul_right (ih fun r hr ↦ hs r (List.mem_cons_of_mem _ hr))
  exact hprod _ fun _ hp ↦ hq _ (by simpa using (List.mem_filter.mp hp).2)

/-- Product of the first prefix strictly exceeding `T` in the increasing
prime-factor list, including repeated primes. Defaults to `1` when none crosses. -/
@[expose] public noncomputable def firstCrossingPrefix (T : ℝ) (n : ℕ) : ℕ := by
  classical
  exact if hex : ∃ k, T < ((n.primeFactorsList.take k).prod : ℝ) then
    (n.primeFactorsList.take (Nat.find hex)).prod else 1

private theorem firstCrossingPrefix_spec {T : ℝ} {n X : ℕ}
    (hT : 1 ≤ T) (hn : T < (n : ℝ)) (hX : ∀ p ∈ n.primeFactorsList, p ≤ X) :
    T < (firstCrossingPrefix T n : ℝ) ∧ firstCrossingPrefix T n ∣ n ∧
      (firstCrossingPrefix T n : ℝ) ≤ (X : ℝ) * T := by
  classical
  let ps := n.primeFactorsList
  let crosses : ℕ → Prop := fun j ↦ T < ((ps.take j).prod : ℝ)
  have hn0 : n ≠ 0 := by
    intro hn0
    simp [hn0, not_lt.mpr (hT.trans' zero_le_one)] at hn
  have hlast : crosses ps.length := by
    simpa [crosses, ps, Nat.prod_primeFactorsList hn0] using hn
  have hex : ∃ k, crosses k := ⟨_, hlast⟩
  let k := Nat.find hex
  have hk : k ≤ ps.length := Nat.find_min' hex hlast
  have hcross : crosses k := Nat.find_spec hex
  have hk0 : k ≠ 0 := by
    intro hz
    simp [crosses, hz, not_lt.mpr hT] at hcross
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hk0
  have hjlen : j < ps.length := by omega
  have hprev : ((ps.take j).prod : ℝ) ≤ T :=
    le_of_not_gt (Nat.find_min hex (show j < k by omega))
  have hstep : (ps.take k).prod = (ps.take j).prod * ps[j] := by
    rw [hj, ← List.take_concat_get hjlen, List.concat_eq_append, List.prod_append]
    simp
  have heq : firstCrossingPrefix T n = (ps.take k).prod := dite_eq_left hex
  refine ⟨heq ▸ hcross, ?_, ?_⟩
  · rw [heq]
    simpa only [ps, Nat.prod_primeFactorsList hn0] using (List.take_sublist k ps).prod_dvd_prod
  · rw [heq, hstep, Nat.cast_mul, mul_comm ((X : ℕ) : ℝ)]
    exact mul_le_mul hprev (by exact_mod_cast hX _ (List.getElem_mem hjlen))
      (Nat.cast_nonneg _) (zero_le_one.trans hT)

/-- Keep the whole erased part at or below the threshold, otherwise truncate it
at its first strict crossing. -/
@[expose] public noncomputable def erasedPrefix (T : ℝ) (a : ℕ) : ℕ := by
  classical
  exact if T < (a : ℝ) then firstCrossingPrefix T a else a

/-- Above the threshold the only pivot multiplier is `1`. At or below it, buy
positive `P`-smooth multipliers up to the one-prime overshoot cap `X*T/a`. -/
@[expose] public noncomputable def pivotMenu (X : ℕ) (T : ℝ) (P : Finset ℕ) (a : ℕ) : Finset ℕ := by
  classical
  exact if T < (a : ℝ) then {1} else
    (Finset.Icc 1 ⌊(X : ℝ) * T / (a : ℝ)⌋₊).filter (fun m ↦ ∀ p ∈ m.primeFactorsList, p ∈ P)

private theorem mem_pivotMenu_of_le {X a m : ℕ} {T : ℝ} {P : Finset ℕ} (ha : (a : ℝ) ≤ T) :
    m ∈ pivotMenu X T P a ↔
      1 ≤ m ∧ (m : ℝ) ≤ (X : ℝ) * T / (a : ℝ) ∧ ∀ p ∈ m.primeFactorsList, p ∈ P := by
  rw [pivotMenu, ite_eq_right (not_lt.mpr ha), Finset.mem_filter, Finset.mem_Icc]
  exact ⟨fun ⟨⟨hpos, hcap⟩, hsupp⟩ ↦
    ⟨hpos, (Nat.le_floor_iff' (Nat.ne_of_gt hpos)).mp hcap, hsupp⟩,
    fun ⟨hpos, hcap, hsupp⟩ ↦ ⟨⟨hpos, Nat.le_floor hcap⟩, hsupp⟩⟩

private theorem exists_crossingMultiplier {X a b : ℕ} {T : ℝ} {P : Finset ℕ}
    (hT : 1 ≤ T) (ha : 0 < a) (hb : 0 < b) (hcross : T < ((a * b : ℕ) : ℝ))
    (hXa : ∀ p ∈ a.primeFactorsList, p ≤ X) (hPb : ∀ p ∈ b.primeFactorsList, p ∈ P)
    (hXP : ∀ p ∈ P, p ≤ X) :
    ∃ m ∈ pivotMenu X T P a, T < ((erasedPrefix T a * m : ℕ) : ℝ) ∧ erasedPrefix T a * m ∣ a * b := by
  classical
  by_cases h : T < (a : ℝ)
  · obtain ⟨hgt, hdvd, -⟩ := firstCrossingPrefix_spec hT h hXa
    exact ⟨1, by simp [pivotMenu, h], by simpa [erasedPrefix, h] using hgt,
      by simpa [erasedPrefix, h] using hdvd.trans (dvd_mul_right a b)⟩
  · have haR : (0 : ℝ) < a := by exact_mod_cast ha
    have hsmall : 1 ≤ T / (a : ℝ) := (le_div_iff₀ haR).2 (by simpa using le_of_not_gt h)
    have hbig : T / (a : ℝ) < (b : ℝ) :=
      (div_lt_iff₀ haR).2 (by simpa [Nat.cast_mul, mul_comm] using hcross)
    let m := firstCrossingPrefix (T / (a : ℝ)) b
    obtain ⟨hgt, hdvd, hcap⟩ := firstCrossingPrefix_spec hsmall hbig (fun p hp ↦ hXP p (hPb p hp))
    have hm1 : 1 ≤ m := by exact_mod_cast (hsmall.trans hgt.le)
    have hmm : m ∈ pivotMenu X T P a := by
      exact (mem_pivotMenu_of_le (le_of_not_gt h)).mpr
        ⟨hm1, by simpa only [mul_div_assoc] using hcap,
          fun _ hp ↦ hPb _ (Nat.primeFactorsList_subset_of_dvd hdvd hb.ne' hp)⟩
    refine ⟨m, hmm, ?_, ?_⟩
    · simpa [erasedPrefix, h, Nat.cast_mul, mul_comm] using (div_lt_iff₀ haR).1 hgt
    · simpa [erasedPrefix, h] using Nat.mul_dvd_mul_left a hdvd

private theorem exists_splitCode {X q n₁ n₂ : ℕ} {T : ℝ} {E P : Finset ℕ}
    (hT : 1 ≤ T) (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (hdisj : Disjoint E P)
    (hE : ∀ p ∈ E, p ≤ X ∧ q.Coprime p) (hP : ∀ p ∈ P, p ≤ X ∧ q.Coprime p) :
    let a := fullPart E (n₁ * n₂)
    let b := fullPart P (n₁ * n₂)
    T < ((a * b : ℕ) : ℝ) →
      ∃ m f_h f_Z : ℕ, m ∈ pivotMenu X T P a ∧ f_h ∈ (erasedPrefix T a * m).divisors ∧
        f_h * f_Z = erasedPrefix T a * m ∧ 0 < f_h ∧ 0 < f_Z ∧
        f_h ∣ n₁ ∧ f_Z ∣ n₂ ∧ q.Coprime f_Z ∧ T < (f_h : ℝ) * (f_Z : ℝ) := by
  intro a b hcross
  let n := n₁ * n₂
  obtain ⟨m, hm, hgt, hdvd⟩ := exists_crossingMultiplier hT (fullPart_pos E n) (fullPart_pos P n)
    hcross (fun p hp ↦ (hE p (fullPart_supported E n hp)).1) (fun _ ↦ fullPart_supported P n)
    (fun p hp ↦ (hP p hp).1)
  -- This is a factor split of the whole product, not a partition of its prime support.
  obtain ⟨f_h, f_Z, hdh, hdZ, hsplit⟩ := Nat.dvd_mul.mp
    (hdvd.trans (fullPart_mul_dvd hdisj (Nat.mul_pos hn₁ hn₂).ne'))
  have hh := Nat.pos_of_dvd_of_pos hdh hn₁
  have hZ := Nat.pos_of_dvd_of_pos hdZ hn₂
  have hq : q.Coprime (a * b) :=
    (coprime_fullPart (fun p hp ↦ (hE p hp).2) n).mul_right
      (coprime_fullPart (fun p hp ↦ (hP p hp).2) n)
  have hqZ : q.Coprime f_Z := hq.of_dvd_right ((hsplit ▸ dvd_mul_left f_Z f_h).trans hdvd)
  have hdiv : f_h ∈ (erasedPrefix T a * m).divisors := Nat.mem_divisors.mpr
    ⟨hsplit ▸ dvd_mul_right f_h f_Z, hsplit ▸ (Nat.mul_pos hh hZ).ne'⟩
  exact ⟨m, f_h, f_Z, hm, hdiv, hsplit, hh, hZ, hdh, hdZ, hqZ,
    by simpa only [← hsplit, Nat.cast_mul] using hgt⟩

/-- Exactly the endpoint indices whose combined full erased and pivot parts
strictly exceed `T`. Equality at the threshold is not a crossing. -/
@[expose] public noncomputable def crossingEndpoints (T : ℝ) (E P D : Finset ℕ)
    (h : ℕ → ℤ) (Z : ℕ → ℕ) : Finset ℕ := by
  classical
  exact D.filter (fun d ↦ T < ((fullPart E ((h d).natAbs * Z d) * fullPart P ((h d).natAbs * Z d) : ℕ) : ℝ))

/-- At the one actual input `v`, count distinct crossing endpoints by the full
menu of erased parts, pivot multipliers and divisors of their filter products. -/
public theorem card_crossingEndpoints_le (v c F₂ q X : ℕ) (U H₀ cutoff : ℝ)
    (E P A D : Finset ℕ) (h β : ℕ → ℤ) (Z : ℕ → ℕ)
    (_hX : 2 ≤ X) (_hU : 0 < U) (_hH₀ : 0 < H₀) (hT : 1 ≤ 2 * U * H₀)
    (hdisj : Disjoint E P)
    (hE : ∀ p ∈ E, p.Prime ∧ p ≤ X ∧ q.Coprime p)
    (hP : ∀ p ∈ P, p.Prime ∧ p ≤ X ∧ q.Coprime p)
    (_hA : ∀ a ∈ A, 0 < a)
    (hrows : ∀ d ∈ D, IsActualRow c F₂ q U H₀ cutoff d (h d) (β d) (Z d))
    (hmenu : ∀ d ∈ D, fullPart E ((h d).natAbs * Z d) ∈ A) :
    (crossingEndpoints (2 * U * H₀) E P D h Z).card ≤
      ∑ a ∈ A, ∑ m ∈ pivotMenu X (2 * U * H₀) P a,
        (erasedPrefix (2 * U * H₀) a * m).divisors.card := by
  classical
  let T := 2 * U * H₀
  let S := crossingEndpoints T E P D h Z
  let a (d : ℕ) := fullPart E ((h d).natAbs * Z d)
  have hdD (d : {d // d ∈ S}) : (d : ℕ) ∈ D := (Finset.mem_filter.mp d.property).1
  have hr (d : {d // d ∈ S}) := hrows d (hdD d)
  have hex (d : {d // d ∈ S}) :
      ∃ m f_h f_Z : ℕ, m ∈ pivotMenu X T P (a d) ∧ f_h ∈ (erasedPrefix T (a d) * m).divisors ∧
        f_h * f_Z = erasedPrefix T (a d) * m ∧ 0 < f_h ∧ 0 < f_Z ∧
        f_h ∣ (h d).natAbs ∧ f_Z ∣ Z d ∧ q.Coprime f_Z ∧ T < (f_h : ℝ) * (f_Z : ℝ) := by
    exact exists_splitCode hT (Int.natAbs_pos.mpr (hr d).h_pos.ne')
      (Nat.pos_of_mul_pos_left (hr d).output_pos) hdisj
      (fun p hp ↦ (hE p hp).2) (fun p hp ↦ (hP p hp).2) (Finset.mem_filter.mp d.property).2
  choose m f_h f_Z hm hfh hprod hfhpos hfZpos hdivh hdivZ hq hgt using hex
  let Code := Σ _ : ℕ, Σ _ : ℕ, ℕ
  let codes : Finset Code := A.sigma (fun a ↦ (pivotMenu X T P a).sigma
    (fun m ↦ (erasedPrefix T a * m).divisors))
  let code (d : {d // d ∈ S}) : Code := ⟨a d, m d, f_h d⟩
  have hcard : S.attach.card ≤ codes.card := Finset.card_le_card_of_injOn code
    (fun d _ ↦ Finset.mem_sigma.mpr ⟨hmenu d (hdD d), Finset.mem_sigma.mpr ⟨hm d, hfh d⟩⟩)
    (fun x _ y _ heq ↦ by
      have ha : a x = a y := congrArg (fun z : Code ↦ z.1) heq
      have hmul : m x = m y := congrArg (fun z : Code ↦ z.2.1) heq
      have hh : f_h x = f_h y := congrArg (fun z : Code ↦ z.2.2) heq
      -- The recorded divisor determines the other filter by positive cancellation.
      have hZ : f_Z x = f_Z y := Nat.eq_of_mul_eq_mul_left (hfhpos x) (calc
        f_h x * f_Z x = erasedPrefix T (a x) * m x := hprod x
        _ = erasedPrefix T (a y) * m y := by rw [ha, hmul]
        _ = f_h x * f_Z y := by rw [hh, hprod y])
      apply Subtype.ext
      exact endpoint_eq_of_filters (v := v) (hr x) (hr y) (hdivh x) (hdivZ x)
        (by simpa only [hh] using hdivh y) (by simpa only [hZ] using hdivZ y)
        (hfhpos x) (hfZpos x) (hq x) (hgt x))
  calc
    S.card = S.attach.card := Finset.card_attach.symm
    _ ≤ codes.card := hcard
    _ = _ := by
      dsimp only [codes]
      rw [Finset.card_sigma]
      simp only [Finset.card_sigma, T]

private theorem card_projection_mem_le (S : Finset ℕ) (R : Finset (ℕ × ℕ))
    (π : ℕ × ℕ → ℕ) (L : ℕ) (hL : ∀ d ∈ S, (R.filter (fun p ↦ π p = d)).card ≤ L) :
    (R.filter (fun p ↦ π p ∈ S)).card ≤ S.card * L := by
  calc
    _ ≤ (S.sigma (fun d ↦ R.filter (fun p ↦ π p = d))).card :=
      Finset.card_le_card_of_injOn (fun p ↦ ⟨π p, p⟩)
        (fun p hp ↦ by
          obtain ⟨hpR, hpS⟩ := Finset.mem_filter.mp hp
          exact Finset.mem_sigma.mpr ⟨hpS, Finset.mem_filter.mpr ⟨hpR, rfl⟩⟩)
        (fun _ _ _ _ heq ↦ congrArg Sigma.snd heq)
    _ = ∑ d ∈ S, (R.filter (fun p ↦ π p = d)).card := Finset.card_sigma _ _
    _ ≤ ∑ _d ∈ S, L := Finset.sum_le_sum hL
    _ = S.card * L := by simp

/-- Count ordered pairs incident to a crossing endpoint, given independent bounds
on the two directed partner fibers. A pair with two crossing endpoints is covered
by both filters, so only a union upper bound is taken. -/
public theorem card_incidentCrossingPairs_le (v c F₂ q X : ℕ) (U H₀ cutoff : ℝ)
    (E P A D : Finset ℕ) (h β : ℕ → ℤ) (Z : ℕ → ℕ) (R : Finset (ℕ × ℕ)) (L : ℕ)
    (hX : 2 ≤ X) (hU : 0 < U) (hH₀ : 0 < H₀) (hT : 1 ≤ 2 * U * H₀)
    (hdisj : Disjoint E P)
    (hE : ∀ p ∈ E, p.Prime ∧ p ≤ X ∧ q.Coprime p)
    (hP : ∀ p ∈ P, p.Prime ∧ p ≤ X ∧ q.Coprime p)
    (hA : ∀ a ∈ A, 0 < a)
    (hrows : ∀ d ∈ D, IsActualRow c F₂ q U H₀ cutoff d (h d) (β d) (Z d))
    (hmenu : ∀ d ∈ D, fullPart E ((h d).natAbs * Z d) ∈ A)
    (_hR : R ⊆ D.product D)
    (hLout : ∀ d ∈ D, (R.filter (fun p ↦ p.1 = d)).card ≤ L)
    (hLin : ∀ d ∈ D, (R.filter (fun p ↦ p.2 = d)).card ≤ L) :
    let S := crossingEndpoints (2 * U * H₀) E P D h Z
    (R.filter (fun p ↦ p.1 ∈ S ∨ p.2 ∈ S)).card ≤
      2 * L * (∑ a ∈ A, ∑ m ∈ pivotMenu X (2 * U * H₀) P a,
        (erasedPrefix (2 * U * H₀) a * m).divisors.card) := by
  intro S
  let R₁ := R.filter (fun p ↦ p.1 ∈ S)
  let R₂ := R.filter (fun p ↦ p.2 ∈ S)
  have hSD : S ⊆ D := Finset.filter_subset _ _
  have h₁ : R₁.card ≤ S.card * L := card_projection_mem_le S R Prod.fst L
    (fun d hd ↦ hLout d (hSD hd))
  have h₂ : R₂.card ≤ S.card * L := card_projection_mem_le S R Prod.snd L
    (fun d hd ↦ hLin d (hSD hd))
  calc
    _ ≤ (R₁ ∪ R₂).card := Finset.card_le_card (fun p hp ↦ by
      obtain ⟨hpR, hpS⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_union.mpr (hpS.imp
        (fun h ↦ Finset.mem_filter.mpr ⟨hpR, h⟩) (fun h ↦ Finset.mem_filter.mpr ⟨hpR, h⟩)))
    _ ≤ R₁.card + R₂.card := Finset.card_union_le _ _
    _ ≤ S.card * L + S.card * L := Nat.add_le_add h₁ h₂
    _ = (2 * L) * S.card := by rw [← two_mul]; ac_rfl
    _ ≤ _ := Nat.mul_le_mul_left _
      (card_crossingEndpoints_le v c F₂ q X U H₀ cutoff E P A D h β Z
        hX hU hH₀ hT hdisj hE hP hA hrows hmenu)

end FixedInputCrossingCount
