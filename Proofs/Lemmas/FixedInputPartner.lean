module

public import Lemmas.PrimitiveTwoFilterRow
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Nat.Factors
import Mathlib.Data.Nat.Find

/-!
# A fixed-input code determines its partner triple

Sources: `1bccf007:.godel/alice/fixed-input-erasure.md:92–124` and
`1bccf007:.godel/alice/shared-second-erasure.md:15–27`. The prefix rule is
`fea7eb0b:.godel/alice/prefix-overlap-review.md:3`, with the cutoff convention in
`fea7eb0b:.godel/alice/shared-complement-count.md:9`. The same decode is used before
pair cuts in `aaf7e47:.godel/alice/singleton-erasure.md:59–77`.

At fixed actual reference `(v, e)` and fixed code, the two filters determine the
primitive signed partner row. Its full positive second output is `d * Z`; the
longest sorted prime prefix at the common cutoff determines `d`. The count is of
ordered triples `(v, d, e)`, not of their witnesses. This is the local uniqueness
step only: it does not count codes or use pair cuts or coprimality of the filters.

Owning check session: `01a20ff6-8a18-70ab-866d-9f5902b34d4c`.
-/

namespace FixedInputPartner

/-- `d` is the product of the longest allowed prefix of the increasing prime-factor
list of `n`, including repeated factors. The empty prefix has product `1`. -/
@[expose] public def IsLongestPrimePrefix (cutoff : ℝ) (n d : ℕ) : Prop :=
  let ps := n.primeFactorsList
  ∃ k ≤ ps.length, ((ps.take k).prod : ℝ) ≤ cutoff ∧
    (∀ j ≤ ps.length, ((ps.take j).prod : ℝ) ≤ cutoff → j ≤ k) ∧
    d = (ps.take k).prod

/-- The prefix decoder searches only indices of prefixes of the complete output.
If no prefix fits, `findGreatest` defaults to zero; an actual prefix must satisfy
`IsLongestPrimePrefix`, which still requires its product to fit the cutoff. -/
@[expose] public noncomputable def decodePrefix (cutoff : ℝ) (n : ℕ) : ℕ :=
  let ps := n.primeFactorsList
  (ps.take (Nat.findGreatest (fun k ↦ ((ps.take k).prod : ℝ) ≤ cutoff) ps.length)).prod

/-- The concrete longest-prefix rule recovers the actual divisor from the full output. -/
public theorem eq_decodePrefix {cutoff : ℝ} {n d : ℕ}
    (hd : IsLongestPrimePrefix cutoff n d) : d = decodePrefix cutoff n := by
  obtain ⟨k, hk, hfit, hlongest, hprod⟩ := hd
  let fits : ℕ → Prop := fun j ↦ ((n.primeFactorsList.take j).prod : ℝ) ≤ cutoff
  have hle : k ≤ Nat.findGreatest fits n.primeFactorsList.length :=
    Nat.le_findGreatest hk hfit
  have hge : Nat.findGreatest fits n.primeFactorsList.length ≤ k :=
    hlongest _ (Nat.findGreatest_le _) (Nat.findGreatest_spec (P := fits) hk hfit)
  change d = (n.primeFactorsList.take (Nat.findGreatest fits n.primeFactorsList.length)).prod
  rwa [← le_antisymm hle hge]

/-- An actual ordered triple at reference `(v, e)` fits the code if it has a primitive
signed row in the box, passes both filters, and its second output `d * Z` is positive
and has `d` as its longest prime prefix at the fixed cutoff. -/
@[expose] public def FitsCode (v e c F₂ q : ℕ) (U H₀ cutoff : ℝ) (f_h f_Z : ℕ)
    (t : ℕ × ℕ × ℕ) : Prop :=
  t.1 = v ∧ t.2.2 = e ∧
    ∃ (h β : ℤ) (Z : ℕ),
      let N := (c : ℤ) * (F₂ : ℤ) * h - (q : ℤ) * β
      0 < h ∧ (h : ℝ) ≤ U ∧ |(β : ℝ)| ≤ H₀ ∧ h.gcd β = 1 ∧
      (f_h : ℤ) ∣ h ∧ (f_Z : ℤ) ∣ N ∧
      0 < t.2.1 * Z ∧ ((t.2.1 * Z : ℕ) : ℤ) = N ∧
      IsLongestPrimePrefix cutoff (t.2.1 * Z) t.2.1

/-- At fixed actual reference and fixed code, any two fitting ordered triples coincide. -/
public theorem triple_eq_of_fitsCode {v e c F₂ q : ℕ} {U H₀ cutoff : ℝ} {f_h f_Z : ℕ}
    (hh : 0 < f_h) (hZ : 0 < f_Z) (hq : q.Coprime f_Z)
    (hcross : 2 * U * H₀ < (f_h : ℝ) * (f_Z : ℝ)) {t₁ t₂ : ℕ × ℕ × ℕ}
    (ht₁ : FitsCode v e c F₂ q U H₀ cutoff f_h f_Z t₁)
    (ht₂ : FitsCode v e c F₂ q U H₀ cutoff f_h f_Z t₂) : t₁ = t₂ := by
  obtain ⟨hv₁, he₁, h₁, β₁, Z₁, hp₁, hU₁, hH₁, hprim₁, hdiv₁, hdivZ₁, -, hout₁, hd₁⟩ := ht₁
  obtain ⟨hv₂, he₂, h₂, β₂, Z₂, hp₂, hU₂, hH₂, hprim₂, hdiv₂, hdivZ₂, -, hout₂, hd₂⟩ := ht₂
  have hrow : (h₁, β₁) = (h₂, β₂) :=
    PrimitiveTwoFilterRow.primitiveRow_eq_of_two_filters (F := (c : ℤ) * (F₂ : ℤ))
      (q := (q : ℤ)) (Int.natCast_pos.mpr hh) (Int.natCast_pos.mpr hZ) hp₁ hp₂
      hU₁ hU₂ hH₁ hH₂ hprim₁ hprim₂ hdiv₁ hdiv₂ hdivZ₁ hdivZ₂
      (by simpa only [Int.gcd_natCast_natCast] using hq) (by exact_mod_cast hcross)
  have houtput := congrArg (fun r : ℤ × ℤ ↦ (c : ℤ) * (F₂ : ℤ) * r.1 - (q : ℤ) * r.2) hrow
  have hout : t₁.2.1 * Z₁ = t₂.2.1 * Z₂ := Int.natCast_inj.mp <|
    hout₁.trans (houtput.trans hout₂.symm)
  have hd : t₁.2.1 = t₂.2.1 :=
    (eq_decodePrefix hd₁).trans ((congrArg (decodePrefix cutoff) hout).trans (eq_decodePrefix hd₂).symm)
  exact Prod.ext (hv₁.trans hv₂.symm) (Prod.ext hd (he₁.trans he₂.symm))

/-- A finite family of actual ordered partner triples matching one code contains
at most one triple. No pair cuts or coprimality between the two filters are needed. -/
public theorem card_le_one_of_fitsCode {v e c F₂ q : ℕ} {U H₀ cutoff : ℝ} {f_h f_Z : ℕ}
    (hh : 0 < f_h) (hZ : 0 < f_Z) (hq : q.Coprime f_Z)
    (hcross : 2 * U * H₀ < (f_h : ℝ) * (f_Z : ℝ)) (s : Finset (ℕ × ℕ × ℕ))
    (hs : ∀ t ∈ s, FitsCode v e c F₂ q U H₀ cutoff f_h f_Z t) : s.card ≤ 1 := by
  exact Finset.card_le_one.mpr fun t₁ ht₁ t₂ ht₂ ↦
    triple_eq_of_fitsCode hh hZ hq hcross (hs t₁ ht₁) (hs t₂ ht₂)

end FixedInputPartner
