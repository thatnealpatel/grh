# Single-place adelic norm: Worker candidate

**Status: Independently reviewed against source, not elaborated.** This is a project lemma for the [finite-place support repair](trace-geometric.md#narrowing-the-bridge-project-reasoning-not-a-source-reading), not a claim newly transcribed from Masullo. It is the first algebraic input to comparing the finite-place terms on PDF pp. 514 and 520 of the [pinned edition](../sources/masullo/README.md). It says nothing about the orbital tail, the cutoff limit, or the Mellin corrections.

For a number field $K$, the single-place idele attached to $u\in K_v^\times$ has adelic norm $|u|_v$. All infinite coordinates and finite coordinates away from $v$ are one. The finite product has at most one nontrivial factor, so the argument also works when $|u|_v=1$.

```lean
import Mathlib.NumberTheory.NumberField.AdeleRing

open NumberField IsDedekindDomain
open scoped BigOperators

namespace Masullo

/-- The adelic norm of a single-place idele is the norm of its local unit. -/
theorem norm_idele_ofAdicCompletion {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) (u : (v.adicCompletion K)ˣ) :
    ‖(IdeleGroup.ofAdicCompletion (𝓞 K) K v u : AdeleRing (𝓞 K) K)‖ =
      ‖(u : v.adicCompletion K)‖ := by
  letI := Classical.decEq (HeightOneSpectrum (𝓞 K))
  let x := IdeleGroup.ofAdicCompletion (𝓞 K) K v u
  change ‖(x : AdeleRing (𝓞 K) K)‖ = _
  rw [AdeleRing.norm_apply_of_isUnit x.isUnit]
  let f : HeightOneSpectrum (𝓞 K) → ℝ := fun w ↦ ‖(x : AdeleRing (𝓞 K) K).2 w‖
  change (∏ w : InfinitePlace K, ‖(1 : w.Completion)‖ ^ w.mult) * (∏ᶠ w, f w) = _
  let A := fun p : HeightOneSpectrum (𝓞 K) ↦ p.adicCompletionIntegers K
  have hoff (w : HeightOneSpectrum (𝓞 K)) (hw : w ≠ v) : f w = 1 := by
    change ‖RestrictedProduct.mulSingle A v (u : v.adicCompletion K) w‖ = 1
    rw [RestrictedProduct.mulSingle_eq_of_ne A _ hw, norm_one]
  have hat : f v = ‖(u : v.adicCompletion K)‖ := by
    change ‖RestrictedProduct.mulSingle A v (u : v.adicCompletion K) v‖ = _
    rw [RestrictedProduct.mulSingle_eq_same]
  rw [finprod_eq_single f v hoff, hat]
  simp only [norm_one, one_pow, Finset.prod_const_one, one_mul]

end Masullo
```

The independent Yah review found no definite API mismatch in the draft at Mathlib `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. In particular, `AdeleRing.ofAdicCompletion` uses the constant-one map at infinity, and `FiniteAdeleRing.ofAdicCompletion` uses `RestrictedProduct.mulSingleMonoidHom` with `Classical.decEq`. The review checked the direction of `w ≠ v` and that `finprod_eq_single` needs no assumption about the value at `v`. The draft uses the review's suggested explicit index type for the family `A`. These checks do not establish that the `change` and `rw` steps elaborate.

With a designated worker transport, put the candidate in an isolated proof revision and run `go run ./cmd/godel check <full-candidate-commit-id> Masullo.norm_idele_ofAdicCompletion` before adopting a Lean module. Until then, keep it here. An independent next task is to prepare norm multiplicativity on ideles and descent through the principal quotient; only the evaluation of the descended map on a single-place class needs this lemma.
