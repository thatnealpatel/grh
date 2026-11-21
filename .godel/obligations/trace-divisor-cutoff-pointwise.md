# Uniform cutoff bound: pointwise half

**Status: Lean endpoint `Masullo.cutoff_pointwise_majorant` in [`Lemmas.CutoffMajorant`](../../Proofs/Lemmas/CutoffMajorant.lean).** This is the pointwise half of the [two-scale cutoff repair](trace-divisor-cutoff.md#uniform-weighted-bounds-for-the-cutoff-family). The connection to Masullo is indirect: The provisional reading of (13.3.1.2)–(13.3.1.3), p. 522 of the [pinned edition](../sources/masullo/README.md), supplies the setting for the conditional comparison on zero-mean tests. The cutoff estimate below is a project proof, not a manuscript claim or a proof of that comparison. No new manuscript reading is asserted.

## Interface and estimate

Use a **real** scale `N`. For the family indexed by `n : ℕ`, pass `N := (n : ℝ) + 2`; all divides and interval endpoints below are real. On the closed lower layer `I_N = [1/N, 2/N]`, supply bounds `N*M₁`, `N^2*M₂` for the norms of the first and second derivatives of `L`; off it, supply vanishing of both derivatives. For the upper cutoff supply global bounds `M₁/N`, `M₂/N^2`, and first-derivative vanishing off `[N,2*N]`. Upper second-derivative support is not needed here. Both cutoff values belong to `[0,1]`. These inputs follow from the profile bounds in the parent handoff; in particular the global upper bounds follow by splitting the upper indicator into its `1` and `0` cases. With `N ≥ 2`, `2/N ≤ 1 < N`. Thus on the entire closed lower layer, endpoints included, `U' = 0`; off the layer, `L' = 0`. This proves `L' * U' = 0`, rather than assuming the cross term away.

Let `p = L * U`, `f = p • Δ`, `w = exp(a*x)`, `E = exp(-δ*x)`, and `Wⱼ = w * ‖Δ⁽ʲ⁾ x‖`. Iterated Leibniz gives `f'' = p • Δ'' + (2*p') • Δ' + p'' • Δ`, with `p'' = L''*U + 2*L'*U' + L*U''`. The triangle inequality, `‖p‖ ≤ 1`, `‖p'‖ ≤ ‖L'‖ + M₁`, and `‖p''‖ ≤ ‖L''‖ + M₂` give

$$w(\|f\|+\|f''\|)\le W_0+W_2+2M_1W_1+M_2W_0 + (2\|L'\|W_1+\|L''\|W_0).$$

Use `Wⱼ ≤ Aⱼ*E` for the first four terms. Off the lower layer the parenthesis vanishes. On it, `E ≤ 1` implies `W₁ ≤ A₁`; the separately supplied **weighted** bound `W₀ ≤ B*x` gives `N^2*M₂*W₀ ≤ N^2*M₂*B*(2/N) = (2*M₂*B)*N`. In particular no unweighted linear estimate is substituted. Only `x > 0` is claimed and no sign on `a` is needed.

## Checked interface

The conclusion reduces by its three `let`s to the [integral majorant](trace-divisor-cutoff-integral.md) with exactly `deriv (deriv f)`, the closed `Set.Icc`, and the indicator height `C₁ * N`. The integral lemma also takes `0 < N` (from `hN`), continuity of `f` and `f''`, and compact support of both. This pointwise lemma neither constructs the smooth test profiles nor proves any integral or limit assertion.

An independent Yah reviewer checked the type unchanged from the draft at `55ca1bff1a728a317b177b4575150dc55417431b`, including the separation of derivative supports, the essential weighted linear bound, and the alignment with the integral lemma and smooth profiles. The reviewer also checked the digest-matched extraction of p. 522: The Mellin-jet conditions and capped critical-line formula do not supply these estimates or equality with the full distribution. The source reading remains provisional; no rendered page was reviewed. See the [candidate checks](../../cmd/godel/README.md#checking-a-proof-candidate).

**Next:** Check the [smooth profile specialization](trace-divisor-cutoff-profiles.md), which must prove the layer and exponential hypotheses and give admissible compact tests above zero. No equality of distributions is needed for that step.
