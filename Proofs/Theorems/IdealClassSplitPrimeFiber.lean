module

public import Theorems.IdealClassQuadraticReduction
import Mathlib.RingTheory.Ideal.Prod

/-!
# Finite places above split primes in ℚ(√-5)

The two projection kernels of the split quotient enumerate the places
in the finite Euler product (3.2.1.7), p. 124, above a split rational prime.
-/

open IsDedekindDomain NumberField

namespace Masullo

local notation "O" => 𝓞 QSqrtNegFive

/-- For a split root `r` at `p ≠ 2, 5`, exactly two finite places lie above `p`.
Their ideals are the kernels of evaluation at `r` and `-r`, respectively. -/
public theorem qSqrtNegFive_heckePrimeFiber_of_split_root (p : Nat.Primes)
    (hp₂ : p.val ≠ 2) (hp₅ : p.val ≠ 5) (r : ZMod p.val) (hr : r ^ 2 = -5) :
    let f := (qSqrtNegFiveSplitQuotientEquiv p hp₂ hp₅ r hr).toRingHom.comp
      (Ideal.Quotient.mk (Ideal.span {(p.val : O)}))
    ∃ v₁ v₂ : heckePrimeFiber QSqrtNegFive p,
      v₁.1.asIdeal = RingHom.ker ((RingHom.fst _ _).comp f) ∧
      v₂.1.asIdeal = RingHom.ker ((RingHom.snd _ _).comp f) ∧
      v₁ ≠ v₂ ∧ ∀ w : heckePrimeFiber QSqrtNegFive p, w = v₁ ∨ w = v₂ := by
  intro f
  let : Fact (Nat.Prime p.val) := ⟨p.2⟩
  let e := qSqrtNegFiveSplitQuotientEquiv p hp₂ hp₅ r hr
  have hf : Function.Surjective f := e.surjective.comp Ideal.Quotient.mk_surjective
  have hker : RingHom.ker f = Ideal.span {(p.val : O)} := by
    exact (RingHom.ker_comp_of_injective _ e.injective).trans Ideal.mk_ker
  have hk (w : heckePrimeFiber QSqrtNegFive p) : RingHom.ker f ≤ w.1.asIdeal := by
    rw [hker, Ideal.span_singleton_le_iff_mem]
    have hw : (p.val : ℤ) ∈ w.1.asIdeal.under ℤ := by
      rw [heckePrimeFiber_under_eq_span p w]
      exact Ideal.subset_span (Set.mem_singleton _)
    simpa using (Ideal.mem_under ℤ w.1.asIdeal).mp hw
  -- Classify the prime ideal in the product, then pull it back to the integer ring.
  have hclass (w : heckePrimeFiber QSqrtNegFive p) :
      w.1.asIdeal = RingHom.ker ((RingHom.fst _ _).comp f) ∨
      w.1.asIdeal = RingHom.ker ((RingHom.snd _ _).comp f) := by
    let P := w.1.asIdeal
    let : P.IsPrime := w.1.isPrime
    have hP : (P.map f).IsPrime := Ideal.map_isPrime_of_surjective hf (hk w)
    have hback : (P.map f).comap f = P := by
      rw [Ideal.comap_map_of_surjective' f hf, sup_eq_left.mpr (hk w)]
    rcases (Ideal.ideal_prod_prime (P.map f)).mp hP with ⟨I, hI, h⟩ | ⟨I, hI, h⟩
    · left
      change P = _
      rw [← hback, h, Ideal.eq_bot_of_prime I]
      ext x
      simp [Ideal.mem_comap, Ideal.mem_prod]
    · right
      change P = _
      rw [← hback, h, Ideal.eq_bot_of_prime I]
      ext x
      simp [Ideal.mem_comap, Ideal.mem_prod]
  have hunder (g : O →+* ZMod p.val) : (RingHom.ker g).under ℤ = Ideal.span {(p.val : ℤ)} := by
    ext x
    rw [Ideal.mem_under, RingHom.mem_ker, Ideal.mem_span_singleton, eq_intCast, map_intCast,
      ZMod.intCast_zmod_eq_zero_iff_dvd]
  have placeOfKer (g : O →+* ZMod p.val) :
      ∃ v : heckePrimeFiber QSqrtNegFive p, v.1.asIdeal = RingHom.ker g := by
    have hp_mem : (p.val : O) ∈ RingHom.ker g := by
      rw [RingHom.mem_ker, map_natCast, ZMod.natCast_self]
    have hne : RingHom.ker g ≠ ⊥ := by
      intro h
      simp [h, p.2.ne_zero] at hp_mem
    let v : HeightOneSpectrum O := ⟨RingHom.ker g, RingHom.ker_isPrime g, hne⟩
    have hv : heckeRationalPrime v = p := by
      apply Subtype.ext
      change ((RingHom.ker g).under ℤ).absNorm = p.val
      rw [hunder g]
      simp
    exact ⟨⟨v, hv⟩, rfl⟩
  obtain ⟨v₁, hv₁⟩ := placeOfKer ((RingHom.fst _ _).comp f)
  obtain ⟨v₂, hv₂⟩ := placeOfKer ((RingHom.snd _ _).comp f)
  refine ⟨v₁, v₂, hv₁, hv₂, ?_, ?_⟩
  · intro h
    have hI := congrArg (fun v : heckePrimeFiber QSqrtNegFive p ↦ v.1.asIdeal) h
    have heq := hv₁.symm.trans (hI.trans hv₂)
    obtain ⟨z, hz⟩ := hf (0, 1)
    have hz₁ : z ∈ RingHom.ker ((RingHom.fst _ _).comp f) := by simp [hz]
    have hz₂ : z ∈ RingHom.ker ((RingHom.snd _ _).comp f) := heq ▸ hz₁
    simp [RingHom.mem_ker, RingHom.comp_apply, hz] at hz₂
  · intro w
    rcases hclass w with h | h
    · exact Or.inl (Subtype.ext (HeightOneSpectrum.ext_iff.mpr (h.trans hv₁.symm)))
    · exact Or.inr (Subtype.ext (HeightOneSpectrum.ext_iff.mpr (h.trans hv₂.symm)))

/-- Each place over a split prime has residue field `ZMod p.val` via the corresponding
projection, compatibly with integer reduction. Its residue degree is one. -/
public theorem qSqrtNegFive_heckePrimeFiber_residue_of_split_root (p : Nat.Primes) (hp₂ : p.val ≠ 2) (hp₅ : p.val ≠ 5)
    (r : ZMod p.val) (hr : r ^ 2 = -5) (v : heckePrimeFiber QSqrtNegFive p) :
    let f := (qSqrtNegFiveSplitQuotientEquiv p hp₂ hp₅ r hr).toRingHom.comp
      (Ideal.Quotient.mk (Ideal.span {(p.val : O)}))
    (∃ e : (O ⧸ v.1.asIdeal) ≃+* ZMod p.val,
      ((∀ x : O, e (Ideal.Quotient.mk _ x) = (f x).1) ∨
        (∀ x : O, e (Ideal.Quotient.mk _ x) = (f x).2)) ∧
      (∀ n : ℤ, e (Ideal.Quotient.mk _ (n : O)) = (n : ZMod p.val))) ∧
    v.1.asIdeal.inertiaDeg ℤ = 1 := by
  intro f
  obtain ⟨v₁, v₂, h₁, h₂, _, hexhaust⟩ :=
    qSqrtNegFive_heckePrimeFiber_of_split_root p hp₂ hp₅ r hr
  have hf : Function.Surjective f := (qSqrtNegFiveSplitQuotientEquiv p hp₂ hp₅ r hr).surjective.comp
    Ideal.Quotient.mk_surjective
  have descend (g : O →+* ZMod p.val) (hg : Function.Surjective g)
      (h : v.1.asIdeal = RingHom.ker g) :
      ∃ e : (O ⧸ v.1.asIdeal) ≃+* ZMod p.val, ∀ x : O, e (Ideal.Quotient.mk _ x) = g x := by
    refine ⟨(Ideal.quotEquivOfEq h).trans (g.quotientKerEquivOfSurjective hg), ?_⟩
    intro x
    rw [RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk, RingHom.quotientKerEquivOfSurjective_apply_mk]
  obtain ⟨e, he⟩ : ∃ e : (O ⧸ v.1.asIdeal) ≃+* ZMod p.val,
      (∀ x : O, e (Ideal.Quotient.mk _ x) = (f x).1) ∨
        (∀ x : O, e (Ideal.Quotient.mk _ x) = (f x).2) := by
    rcases hexhaust v with hv | hv
    · have hs : Function.Surjective (RingHom.fst (ZMod p.val) (ZMod p.val)) :=
        fun x ↦ ⟨(x, 0), rfl⟩
      obtain ⟨e, he⟩ := descend _ (hs.comp hf) (hv ▸ h₁)
      exact ⟨e, Or.inl he⟩
    · have hs : Function.Surjective (RingHom.snd (ZMod p.val) (ZMod p.val)) :=
        fun x ↦ ⟨(0, x), rfl⟩
      obtain ⟨e, he⟩ := descend _ (hs.comp hf) (hv ▸ h₂)
      exact ⟨e, Or.inr he⟩
  refine ⟨⟨e, he, fun n ↦ ?_⟩, ?_⟩
  · rw [map_intCast, map_intCast]
  · let _ : v.1.asIdeal.IsPrime := v.1.isPrime
    have hbase : (v.1.asIdeal.under ℤ).absNorm = p.val := by
      rw [heckePrimeFiber_under_eq_span p v]
      simp
    have hnorm : v.1.asIdeal.absNorm = p.val := by
      rw [Ideal.absNorm_eq_natCard, Nat.card_congr e.toEquiv, Nat.card_zmod]
    have hdeg := Ideal.absNorm_pow_inertiaDeg (v.1.asIdeal.under ℤ) v.1.asIdeal
    rw [hbase, hnorm] at hdeg
    apply Nat.pow_right_injective p.2.two_le
    simpa only [pow_one] using hdeg

-- At 3 with root 1, `1 + √-5` vanishes only under the second projection.
example :
    let f := (qSqrtNegFiveSplitQuotientEquiv ⟨3, by decide⟩ (by decide) (by decide) 1
      (by decide)).toRingHom.comp (Ideal.Quotient.mk (Ideal.span {(3 : O)}))
    let z := qSqrtNegFiveIntegersEquiv.symm ⟨1, 1⟩
    z ∉ RingHom.ker ((RingHom.fst _ _).comp f) ∧ z ∈ RingHom.ker ((RingHom.snd _ _).comp f) := by
  intro f z
  have h : f z = (2, 0) := by
    change qSqrtNegFiveSplitQuotientEquiv ⟨3, by decide⟩ (by decide) (by decide) 1 (by decide)
      (Ideal.Quotient.mk _ (qSqrtNegFiveIntegersEquiv.symm ⟨1, 1⟩)) = _
    exact (qSqrtNegFiveSplitQuotientEquiv_mk ⟨3, by decide⟩ (by decide) (by decide) 1
      (by decide) 1 1).trans (by decide)
  simpa [RingHom.mem_ker, RingHom.comp_apply, h] using (show (2 : ZMod 3) ≠ 0 by decide)

end Masullo
