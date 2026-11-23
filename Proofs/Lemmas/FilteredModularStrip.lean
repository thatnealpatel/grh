module

public import Lemmas.AffineSmoothInterval
public import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# A filtered run in a translated modular graph

Sources: pinned `.godel/alice/modular-complement-bands.md`, “Translated modular bands”;
`77927754:.godel/alice/one-reference-lifts.md`, “Price of a short bracket”;
`40bd789e:.godel/conjectures/closed/selected-reference-short-bracket.md`.

This is the nonsingleton, fixed-filter step for `u ≡ a*c (mod d)`, including composite
`d` and filters sharing factors with `d`. The interval bounds refer to **occupied**
parameters; only these must correspond to points in the strip. The smooth sieve is
per run, not a bound summed over filters, directions, cofactors or denominators.

Owning check session: `01a2095b-3cd7-7c85-a8af-4a73f8cbf3ba`.
-/

namespace FilteredModularStrip

/-- Twice the signed area with anchor `p`, in `(c,u)` coordinates. -/
@[expose] public def det (p q r : ℤ × ℤ) : ℤ :=
  (q.1 - p.1) * (r.2 - p.2) - (r.1 - p.1) * (q.2 - p.2)

private theorem graph_diff {d a : ℤ} {p q : ℤ × ℤ}
    (hp : d ∣ p.2 - a * p.1) (hq : d ∣ q.2 - a * q.1) :
    ∃ w : ℤ, q.2 - p.2 = a * (q.1 - p.1) + d * w := by
  obtain ⟨w, hw⟩ := dvd_sub hq hp
  exact ⟨w, by linear_combination hw⟩

private theorem abs_diff_le {x y : ℤ} {b W : ℝ}
    (hx : |(x : ℝ) - b| ≤ W) (hy : |(y : ℝ) - b| ≤ W) :
    |((x - y : ℤ) : ℝ)| ≤ 2 * W := by
  rw [Int.cast_sub]
  calc
    |(x : ℝ) - (y : ℝ)| ≤ |(x : ℝ) - b| + |b - (y : ℝ)| := abs_sub_le _ _ _
    _ ≤ 2 * W := by rw [abs_sub_comm b]; linarith

private theorem eq_zero_of_dvd_of_abs_lt {m x : ℤ} (hm : 0 < m) (h : m ∣ x)
    (hx : |(x : ℝ)| < (m : ℝ)) : x = 0 := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hnat : (x.natAbs : ℝ) < (m.natAbs : ℝ) := by
    simpa only [Nat.cast_natAbs, Int.cast_abs, abs_of_pos hmR] using hx
  exact Int.eq_zero_of_dvd_of_natAbs_lt_natAbs h (by exact_mod_cast hnat)

/-- The `a` terms cancel. The determinant is a multiple of `e*d`, even when
`e` and `d` share factors. -/
public theorem filter_mul_modulus_dvd_det {d a : ℤ} {e : ℕ} {p q r : ℤ × ℤ}
    (hp : (d ∣ p.2 - a * p.1) ∧ ((e : ℤ) ∣ p.1))
    (hq : (d ∣ q.2 - a * q.1) ∧ ((e : ℤ) ∣ q.1))
    (hr : (d ∣ r.2 - a * r.1) ∧ ((e : ℤ) ∣ r.1)) : (e : ℤ) * d ∣ det p q r := by
  obtain ⟨wq, hwq⟩ := graph_diff hp.1 hq.1
  obtain ⟨wr, hwr⟩ := graph_diff hp.1 hr.1
  obtain ⟨xq, hxq⟩ := dvd_sub hq.2 hp.2
  obtain ⟨xr, hxr⟩ := dvd_sub hr.2 hp.2
  refine ⟨xq * wr - xr * wq, ?_⟩
  rw [det, hwq, hwr, hxq, hxr]
  ring

/-- All triples in a translated rectangle with `8*Z*K < e*d` are collinear. -/
public theorem det_eq_zero {d a : ℤ} {e : ℕ} {bC bU Z K : ℝ}
    {S : Finset (ℤ × ℤ)} (hd : 0 < d) (he : 0 < e)
    (hrect : ∀ p ∈ S, |(p.1 : ℝ) - bC| ≤ Z ∧ |(p.2 : ℝ) - bU| ≤ K)
    (hgraph : ∀ p ∈ S, d ∣ p.2 - a * p.1)
    (hfilter : ∀ p ∈ S, (e : ℤ) ∣ p.1) (hthin : 8 * Z * K < (e : ℝ) * (d : ℝ))
    {p q r : ℤ × ℤ} (hp : p ∈ S) (hq : q ∈ S) (hr : r ∈ S) : det p q r = 0 := by
  have hdiv := filter_mul_modulus_dvd_det ⟨hgraph p hp, hfilter p hp⟩
    ⟨hgraph q hq, hfilter q hq⟩ ⟨hgraph r hr, hfilter r hr⟩
  have hqc := abs_diff_le (hrect q hq).1 (hrect p hp).1
  have hrc := abs_diff_le (hrect r hr).1 (hrect p hp).1
  have hqu := abs_diff_le (hrect q hq).2 (hrect p hp).2
  have hru := abs_diff_le (hrect r hr).2 (hrect p hp).2
  have hZ := (abs_nonneg _).trans hqc
  have hb (x y : ℤ) (hx : |(x : ℝ)| ≤ 2 * Z) (hy : |(y : ℝ)| ≤ 2 * K) :
      |((x * y : ℤ) : ℝ)| ≤ 2 * Z * (2 * K) := by
    rw [Int.cast_mul, abs_mul]
    exact mul_le_mul hx hy (abs_nonneg _) hZ
  have habs : |(det p q r : ℝ)| ≤ 8 * Z * K := by
    rw [det, Int.cast_sub]
    refine (abs_sub _ _).trans ?_
    have h := add_le_add (hb _ _ hqc hru) (hb _ _ hrc hqu)
    linarith
  apply eq_zero_of_dvd_of_abs_lt (mul_pos (by exact_mod_cast he) hd) hdiv
  exact habs.trans_lt (by simpa only [Int.cast_mul, Int.cast_natCast] using hthin)

private theorem first_ne_of_ne {d a : ℤ} {p q : ℤ × ℤ} {b K : ℝ}
    (hd : 0 < d) (hnarrow : 2 * K < (d : ℝ))
    (hp : d ∣ p.2 - a * p.1) (hq : d ∣ q.2 - a * q.1)
    (hpu : |(p.2 : ℝ) - b| ≤ K) (hqu : |(q.2 : ℝ) - b| ≤ K)
    (hne : p ≠ q) : q.1 - p.1 ≠ 0 := by
  intro hc
  obtain ⟨w, hw⟩ := graph_diff hp hq
  rw [hc, mul_zero, zero_add] at hw
  have hu := eq_zero_of_dvd_of_abs_lt hd ⟨w, hw⟩ ((abs_diff_le hqu hpu).trans_lt hnarrow)
  exact hne (Prod.ext (sub_eq_zero.mp hc).symm (sub_eq_zero.mp hu).symm)

-- Factor out the positive gcd of the absolute coordinates, retaining the signs.
private theorem primitive_factor {x y : ℤ} (hx : x ≠ 0) :
    ∃ r s : ℤ, x = (x.gcd y : ℤ) * r ∧ y = (x.gcd y : ℤ) * s ∧ IsCoprime r s := by
  obtain ⟨r, hr⟩ := Int.gcd_dvd_left x y
  obtain ⟨s, hs⟩ := Int.gcd_dvd_right x y
  refine ⟨r, s, hr, hs, Int.isCoprime_iff_gcd_eq_one.mpr ?_⟩
  have heq := congrArg₂ Int.gcd hr hs
  rw [Int.gcd_mul_left, Int.natAbs_natCast] at heq
  exact Nat.eq_of_mul_eq_mul_left (Int.gcd_pos_of_ne_zero_left y hx)
    (heq.symm.trans (Nat.mul_one _).symm)

private theorem multiple_of_primitive {v w x y : ℤ} (hcop : IsCoprime v w)
    (hdet : v * y = x * w) : ∃ t : ℤ, x = t * v ∧ y = t * w := by
  obtain ⟨b, c, h⟩ := hcop
  refine ⟨b * x + c * y, ?_, ?_⟩
  · linear_combination -x * h - c * hdet
  · linear_combination -y * h + b * hdet

private theorem filter_step {e : ℕ} (he : 0 < e) (v : ℤ) :
    let k := e / e.gcd v.natAbs
    0 < k ∧ ((e / k : ℕ) : ℤ) ∣ v ∧
      ∀ t : ℤ, (e : ℤ) ∣ t * v ↔ (k : ℤ) ∣ t := by
  let g := e.gcd v.natAbs
  let k := e / g
  change 0 < k ∧ ((e / k : ℕ) : ℤ) ∣ v ∧ _
  have hgd := Nat.gcd_dvd_left e v.natAbs
  have hg : 0 < g := Nat.gcd_pos_of_pos_left _ he
  have hgZ : (g : ℤ) ≠ 0 := by exact_mod_cast hg.ne'
  have hk : 0 < k := Nat.div_pos (Nat.le_of_dvd he hgd) hg
  have hgk : g * k = e := by rw [mul_comm]; exact Nat.div_mul_cancel hgd
  have hge : (g : ℤ) * (k : ℤ) = (e : ℤ) := by exact_mod_cast hgk
  have hrecover : e / k = g := hgk ▸ Nat.mul_div_cancel g hk
  have hen : (e : ℤ) ≠ 0 := by exact_mod_cast he.ne'
  obtain ⟨r, s, hr, hs, hcop⟩ := primitive_factor (y := v) hen
  simp only [Int.gcd_eq_natAbs_gcd_natAbs, Int.natAbs_natCast] at hr hs
  change (e : ℤ) = (g : ℤ) * r at hr
  change v = (g : ℤ) * s at hs
  have hre : r = k := mul_left_cancel₀ hgZ (hr.symm.trans hge.symm)
  subst r
  refine ⟨hk, hrecover.symm ▸ ⟨s, hs⟩, fun t ↦ ?_⟩
  calc
    (e : ℤ) ∣ t * v ↔ (g : ℤ) * (k : ℤ) ∣ (g : ℤ) * (t * s) := by
      rw [← hge, hs, mul_left_comm t]
    _ ↔ (k : ℤ) ∣ t * s := Int.mul_dvd_mul_iff_left hgZ
    _ ↔ (k : ℤ) ∣ t := ⟨fun h ↦ hcop.dvd_of_dvd_mul_right h, fun h ↦ h.mul_right s⟩

/-- The point of a run at integer parameter `j`, in `(c,u)` coordinates. -/
@[expose] public def linePoint (p : ℤ × ℤ) (k : ℕ) (vc vu j : ℤ) : ℤ × ℤ :=
  (p.1 + ((k : ℤ) * vc) * j, p.2 + ((k : ℤ) * vu) * j)

private theorem linePoint_injective {p : ℤ × ℤ} {k : ℕ} {vc vu : ℤ}
    (hk : 0 < k) (hc : vc ≠ 0) : Function.Injective (linePoint p k vc vu) := by
  have hkZ : (k : ℤ) ≠ 0 := by exact_mod_cast hk.ne'
  intro i j h
  exact mul_left_cancel₀ (mul_ne_zero hkZ hc) (add_left_cancel (congrArg Prod.fst h))

/-- An exact parametrization of the finite filter on one primitive graph direction.
The crop `[lo,hi]` is inclusive; `occupied` need not fill it. The unscaled graph
coordinates `(vc,vw)`, not the ambient pair `(vc,vu)`, are coprime. -/
public structure Run (d a : ℤ) (e : ℕ) (Z K : ℝ) (S : Finset (ℤ × ℤ)) where
  anchor : ℤ × ℤ
  anchor_mem : anchor ∈ S
  vc : ℤ
  vw : ℤ
  vu : ℤ
  primitive : IsCoprime vc vw
  graph : vu = a * vc + d * vw
  vc_ne : vc ≠ 0
  horizontal : vu = 0 → d ∣ vc
  k : ℕ
  k_pos : 0 < k
  k_eq : k = e / e.gcd vc.natAbs
  content_dvd : ((e / k : ℕ) : ℤ) ∣ vc
  filter_iff (t : ℤ) : (e : ℤ) ∣ t * vc ↔ (k : ℤ) ∣ t
  occupied : Finset ℤ
  lo : ℤ
  hi : ℤ
  lo_mem : lo ∈ occupied
  hi_mem : hi ∈ occupied
  lo_lt_hi : lo < hi
  occupied_subset : occupied ⊆ Finset.Icc lo hi
  image_eq : occupied.image (linePoint anchor k vc vu) = S
  card_eq : occupied.card = S.card
  span_c : ((hi - lo : ℤ) : ℝ) * (k : ℝ) * |(vc : ℝ)| ≤ 2 * Z
  span_u : ((hi - lo : ℤ) : ℝ) * (k : ℝ) * |(vu : ℝ)| ≤ 2 * K

private theorem span_bound {lo hi x v : ℤ} {k : ℕ} {b W : ℝ} (hlohi : lo ≤ hi)
    (hlo : |((x + ((k : ℤ) * v) * lo : ℤ) : ℝ) - b| ≤ W)
    (hhi : |((x + ((k : ℤ) * v) * hi : ℤ) : ℝ) - b| ≤ W) :
    ((hi - lo : ℤ) : ℝ) * (k : ℝ) * |(v : ℝ)| ≤ 2 * W := by
  have h := abs_diff_le hhi hlo
  have heq : x + ((k : ℤ) * v) * hi - (x + ((k : ℤ) * v) * lo) =
      ((hi - lo) * (k : ℤ)) * v := by ring
  have hn : 0 ≤ ((hi - lo : ℤ) : ℝ) := by exact_mod_cast sub_nonneg.mpr hlohi
  simpa only [heq, Int.cast_mul, Int.cast_natCast, abs_mul, abs_of_nonneg hn,
    abs_of_nonneg (Nat.cast_nonneg k : 0 ≤ (k : ℝ))] using h

/-- Extract the nonsingleton run from the graph, filter and rectangle conditions.
Strict thinness kills the determinant; the strict `u`-width bound excludes vertical
runs. The unit-slope assumption is used only for horizontal divisibility. -/
public theorem extract_run {d a : ℤ} {e : ℕ} {bC bU Z K : ℝ} {S : Finset (ℤ × ℤ)}
    (hd : 0 < d) (ha : IsCoprime a d) (he : 0 < e) (hS : 1 < S.card)
    (hrect : ∀ p ∈ S, |(p.1 : ℝ) - bC| ≤ Z ∧ |(p.2 : ℝ) - bU| ≤ K)
    (hgraph : ∀ p ∈ S, d ∣ p.2 - a * p.1) (hfilter : ∀ p ∈ S, (e : ℤ) ∣ p.1)
    (hthin : 8 * Z * K < (e : ℝ) * (d : ℝ)) (hnarrow : 2 * K < (d : ℝ)) :
    Nonempty (Run d a e Z K S) := by
  obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp hS
  obtain ⟨wq, hwq⟩ := graph_diff (hgraph p hp) (hgraph q hq)
  have hqc := first_ne_of_ne hd hnarrow (hgraph p hp) (hgraph q hq)
    (hrect p hp).2 (hrect q hq).2 hpq
  obtain ⟨vc, vw, hc, hw, hcop⟩ := primitive_factor (y := wq) hqc
  let g := (q.1 - p.1).gcd wq
  change q.1 - p.1 = (g : ℤ) * vc at hc
  change wq = (g : ℤ) * vw at hw
  have hvc : vc ≠ 0 := by
    intro h
    exact hqc (by rw [hc, h, mul_zero])
  let vu := a * vc + d * vw
  have hhor (h : vu = 0) : d ∣ vc := by
    apply ha.symm.dvd_of_dvd_mul_left
    exact ⟨-vw, by dsimp only [vu] at h; linear_combination h⟩
  let k := e / e.gcd vc.natAbs
  have ⟨hk, hcontent, hstep⟩ := filter_step he vc
  change 0 < k at hk
  change ((e / k : ℕ) : ℤ) ∣ vc at hcontent
  change ∀ t : ℤ, (e : ℤ) ∣ t * vc ↔ (k : ℤ) ∣ t at hstep
  have hpoint (r : ℤ × ℤ) (hr : r ∈ S) : ∃ j : ℤ, linePoint p k vc vu j = r := by
    obtain ⟨wr, hwr⟩ := graph_diff (hgraph p hp) (hgraph r hr)
    have hdet := det_eq_zero hd he hrect hgraph hfilter hthin hp hq hr
    rw [det, hwq, hwr, hc, hw] at hdet
    have hcross : vc * wr = (r.1 - p.1) * vw := by
      have hg : (g : ℤ) ≠ 0 := by
        exact_mod_cast (Int.gcd_pos_of_ne_zero_left wq hqc).ne'
      have hscaled : (d * (g : ℤ)) * (vc * wr - (r.1 - p.1) * vw) = 0 := by
        linear_combination hdet
      exact sub_eq_zero.mp ((mul_eq_zero.mp hscaled).resolve_left (mul_ne_zero hd.ne' hg))
    obtain ⟨t, htC, htW⟩ := multiple_of_primitive hcop hcross
    have htU : r.2 - p.2 = t * vu := by
      dsimp only [vu]
      rw [hwr, htC, htW]
      ring
    have htDiv : (e : ℤ) ∣ t * vc := htC ▸ dvd_sub (hfilter r hr) (hfilter p hp)
    obtain ⟨j, hj⟩ := (hstep t).mp htDiv
    refine ⟨j, Prod.ext ?_ ?_⟩
    · change p.1 + ((k : ℤ) * vc) * j = r.1
      rw [hj] at htC
      linear_combination -htC
    · change p.2 + ((k : ℤ) * vu) * j = r.2
      rw [hj] at htU
      linear_combination -htU
  classical
  let index (r : ℤ × ℤ) : ℤ := if hr : r ∈ S then (hpoint r hr).choose else 0
  have hindex (r : ℤ × ℤ) (hr : r ∈ S) : linePoint p k vc vu (index r) = r := by
    simpa only [index, dite_eq_left hr] using (hpoint r hr).choose_spec
  let T := S.image index
  have himage : T.image (linePoint p k vc vu) = S := by
    ext r
    constructor
    · intro hr
      obtain ⟨j, hj, hjr⟩ := Finset.mem_image.mp hr
      obtain ⟨s, hs, hsj⟩ := Finset.mem_image.mp hj
      rw [← hsj, hindex s hs] at hjr
      exact hjr ▸ hs
    · intro hr
      exact Finset.mem_image.mpr ⟨index r, Finset.mem_image.mpr ⟨r, hr, rfl⟩, hindex r hr⟩
  have hcard : T.card = S.card := by
    rw [← himage, Finset.card_image_of_injective _ (linePoint_injective hk hvc)]
  have hTcard : 1 < T.card := hcard.symm ▸ hS
  have hT : T.Nonempty := Finset.card_pos.mp (by omega)
  let lo := T.min' hT
  let hi := T.max' hT
  have hlo : lo ∈ T := T.min'_mem hT
  have hhi : hi ∈ T := T.max'_mem hT
  have hI : T ⊆ Finset.Icc lo hi := fun j hj ↦
    Finset.mem_Icc.mpr ⟨T.min'_le j hj, T.le_max' j hj⟩
  have hlt : lo < hi := by
    obtain ⟨i, hiT, j, hjT, hij⟩ := Finset.one_lt_card.mp hTcard
    have hiI := Finset.mem_Icc.mp (hI hiT)
    have hjI := Finset.mem_Icc.mp (hI hjT)
    omega
  have hloS : linePoint p k vc vu lo ∈ S :=
    himage ▸ Finset.mem_image.mpr ⟨lo, hlo, rfl⟩
  have hhiS : linePoint p k vc vu hi ∈ S :=
    himage ▸ Finset.mem_image.mpr ⟨hi, hhi, rfl⟩
  exact ⟨{
    anchor := p, anchor_mem := hp, vc := vc, vw := vw, vu := vu, primitive := hcop
    graph := rfl, vc_ne := hvc, horizontal := hhor, k := k, k_pos := hk, k_eq := rfl
    content_dvd := hcontent, filter_iff := hstep, occupied := T, lo := lo, hi := hi
    lo_mem := hlo, hi_mem := hhi, lo_lt_hi := hlt, occupied_subset := hI
    image_eq := himage, card_eq := hcard
    span_c := span_bound hlt.le (hrect _ hloS).1 (hrect _ hhiS).1
    span_u := span_bound hlt.le (hrect _ hloS).2 (hrect _ hhiS).2 }⟩

/-- Bounds on the parameter span from each nonzero coordinate step. In the
horizontal case only the first bound is used. -/
public theorem Run.span_le_width {d a : ℤ} {e : ℕ} {Z K : ℝ} {S : Finset (ℤ × ℤ)}
    (R : Run d a e Z K S) :
    ((R.hi - R.lo : ℤ) : ℝ) ≤ (2 * Z) / ((R.k : ℝ) * |(R.vc : ℝ)|) ∧
    (R.vu ≠ 0 → ((R.hi - R.lo : ℤ) : ℝ) ≤ (2 * K) / ((R.k : ℝ) * |(R.vu : ℝ)|)) := by
  have hk : 0 < (R.k : ℝ) := by exact_mod_cast R.k_pos
  have hpos {v : ℤ} (hv : v ≠ 0) : 0 < (R.k : ℝ) * |(v : ℝ)| :=
    mul_pos hk (abs_pos.mpr (by exact_mod_cast hv))
  exact ⟨(le_div_iff₀ (hpos R.vc_ne)).mpr (by rw [← mul_assoc]; exact R.span_c),
    fun hu ↦ (le_div_iff₀ (hpos hu)).mpr (by rw [← mul_assoc]; exact R.span_u)⟩

/-- Sieve the occupied parameters with positive smooth numerators only. `D ≥ 1`
bounds the endpoint difference `hi - lo`, not the number of integers in the interval.
The full interval is used only as a superset in the affine sieve. -/
public theorem Run.card_smooth_le {d a : ℤ} {e X D : ℕ} {Z K : ℝ} {S : Finset (ℤ × ℤ)}
    (R : Run d a e Z K S) (hX : 2 ≤ X) (hD : 1 ≤ D) (hspan : R.hi - R.lo ≤ (D : ℤ)) :
    (S.filter (fun p ↦ 0 < p.1 ∧ p.1.natAbs ∈ Nat.smoothNumbers (X + 1))).card ≤
      (X + 2) * (Nat.smoothNumbersUpTo D (X + 1)).card := by
  have hk : (R.k : ℤ) ≠ 0 := by exact_mod_cast R.k_pos.ne'
  rw [← R.image_eq, Finset.filter_image,
    Finset.card_image_of_injective _ (linePoint_injective R.k_pos R.vc_ne)]
  refine (Finset.card_le_card (t := (Finset.Icc R.lo R.hi).filter (fun j ↦
    0 < R.anchor.1 + ((R.k : ℤ) * R.vc) * j ∧
      (R.anchor.1 + ((R.k : ℤ) * R.vc) * j).natAbs ∈ Nat.smoothNumbers (X + 1))) ?_).trans
    (AffineSmoothInterval.card_smooth_affine_int_interval_le hX hD (mul_ne_zero hk R.vc_ne) hspan)
  intro j hj
  obtain ⟨hmem, hnum⟩ := Finset.mem_filter.mp hj
  exact Finset.mem_filter.mpr ⟨R.occupied_subset hmem, hnum⟩

/-- The fixed-filter estimate with no prior line hypothesis: Extract the run and bound
its cardinality when every selected numerator is positive and smooth. -/
public theorem exists_run_and_card_le {d a : ℤ} {e X : ℕ} {bC bU Z K : ℝ}
    {S : Finset (ℤ × ℤ)} (hd : 0 < d) (ha : IsCoprime a d) (he : 0 < e) (hX : 2 ≤ X)
    (hS : 1 < S.card)
    (hrect : ∀ p ∈ S, |(p.1 : ℝ) - bC| ≤ Z ∧ |(p.2 : ℝ) - bU| ≤ K)
    (hgraph : ∀ p ∈ S, d ∣ p.2 - a * p.1) (hfilter : ∀ p ∈ S, (e : ℤ) ∣ p.1)
    (hthin : 8 * Z * K < (e : ℝ) * (d : ℝ)) (hnarrow : 2 * K < (d : ℝ))
    (hsmooth : ∀ p ∈ S, 0 < p.1 ∧ p.1.natAbs ∈ Nat.smoothNumbers (X + 1)) :
    ∃ R : Run d a e Z K S, ∀ D : ℕ, 1 ≤ D → R.hi - R.lo ≤ (D : ℤ) →
      S.card ≤ (X + 2) * (Nat.smoothNumbersUpTo D (X + 1)).card := by
  obtain ⟨R⟩ := extract_run hd ha he hS hrect hgraph hfilter hthin hnarrow
  exact ⟨R, fun D hD hspan ↦ by
    simpa only [Finset.filter_eq_self.mpr hsmooth] using R.card_smooth_le hX hD hspan⟩

end FilteredModularStrip
