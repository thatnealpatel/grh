# Real S-local theta quotient

[Formalize receipt](46f190df665a53e689d723da789d392de21c39138e2dad9ba3b1c5c58d10626f-d75138886cfe3053184ce3a0ff3815d2fb65d0f08fc53a18d9e9e7b37c24fb9e.json) ·
[Lean module](../../Proofs/Theorems/RationalRealThetaQuotient.lean)

Assigned writer base: `70508bbf859d439bbed02af4b888d7fc76813ad5`.
Owning Yah check session: `01a2052f-9ad6-7901-9858-1209e194d062`.
The owning session records the exact integrated candidate and base IDs,
the independent rendered-source review, and the exact-candidate check reports.
Integration, independent review, and those checks were pending at authoring time.

## Rendered source and scope

I verified the 940-page PDF against the [edition pin](../sources/masullo/README.md),
SHA-256 `e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5`,
and checked the page renders (including the indices in the local sum).
Printed pages and one-based PDF ordinals agree for all locations below.

- **Chapter 1, §1.1.4, first bullet, p. 12.** The unnumbered display is
  \(\Phi_{F,S}(f)(g)=\sum_{\xi\in\mathcal O_{F,S}^{\times}} f(\xi g)\),
  for \(g\in\mathrm{GL}_1(\mathbf A_{F,S})\) and
  \(f\in\mathcal S(\mathbf A_{F,S})\). The bullet identifies the space of
  S-local theta functions with the quotient by the kernel, gives it the
  quotient topology and asserts that it is strict LF by the Structure
  Theorems. The subsequent global sum on the same page has a different
  domain and runs over \(F^\times\), not the S-units.
- **Definition 2.3.1.1, pp. 99–100.** Displays (2.3.1.1)–(2.3.1.2)
  specify the operator into continuous functions and the same S-unit sum;
  here \(F\) is a number field and \(S\) is finite and contains all its
  Archimedean places. **Proposition 2.3.1.2(1), pp. 100–102** asserts
  absolute, compact-uniform convergence, continuity and left S-unit
  invariance for every Schwartz–Bruhat function. The proof reduces to
  finite tensor sums, uses finite-place support to constrain the
  denominators in (2.3.1.4) and applies a lattice majorant at (2.3.1.8)
  with \(N>[F:\mathbb Q]\). The finite sum here does not need that estimate.
- **Definition 5.1.1.1(3), p. 223, display (5.1.1.3).** The right-hand
  quotient is the S-local one; the two quotients carry quotient topologies.
  **Theorem 5.1.1.3(1), pp. 223–224** asserts the two kernels are closed
  complex linear subspaces. The proof on p. 229 uses continuity of the
  S-idelic Mellin transform by Lemma 5.1.3.1(2) and the equality of its
  kernel with the S-local theta kernel by Lemma 5.1.2.2. The real proof below
  uses neither result.
- **Theorem 5.2.1.1(1), p. 230.** The fixed-S claim is a locally convex
  strict inductive limit of nuclear Fréchet spaces (alongside the separate
  global claim). The proof of (1), p. 231, passes to Fréchet quotients of
  the source stages, but does not check that the induced fixed-S quotient
  transitions embed with closed image. Parts (2)–(3), including (5.2.1.1),
  are about enlarging the set of places or mapping into the global space,
  not the stage transitions inside a single fixed-S quotient.

Closedness of the full kernel alone is not a strictness argument. For
example, let \(s\) be the Fréchet space of rapidly decreasing sequences and
let \(T:s\to s\) act by multiplying the \(n\)-th coordinate by \(e^{-n}\).
In the closed inclusion \(s\times 0\subseteq s\times s\), quotient by the
intersection with the closed graph of \(T\) at each stage. The full quotient
is \(s\), via \((x,y)\mapsto y-Tx\), but the smaller quotient maps onto
\(-T(s)\), dense by finite sequences and proper because \((e^{-n})_n\) has
no rapidly decreasing preimage. This tests the inference about the stage
maps, not the adelic assertion or the existence of an alternative strict
presentation.

## What is proved

For \(F=\mathbb Q\) and \(S=\{\infty\}\), the local additive group, local
ideles and S-units identify with \(\mathbb R\), \(\mathbb R^\times\) and
\(\mathbb Z^\times\), respectively. The implementation starts directly with
these standard identifications, not with a general number-field local
adele construction. The only rational numbers integral away from the real
place are integers, since a nontrivial reduced denominator has a prime
divisor. The invertible integers are \(1,-1\), which Lean enumerates.
Thus `Masullo.rationalRealTheta` is the complex linear operator on genuine
complex-valued Schwartz functions with continuous values on the real
ideles, \(f\mapsto(x\mapsto f(x)+f(-x))\). The finite series stabilizes
uniformly on every subset and its norms are summable; multiplying by
\(-1\) swaps the terms. These are the uniform-sum, norm and unit endpoints
in the receipt.

Let \(A f(x)=f(x)+f(-x)\) on the whole line. Reflection is a continuous
Schwartz pullback, so \(A\) is continuous. Equality on the dense complement
of zero implies equality on the whole line. In particular, the kernel of
local theta is **equal** to the kernel of \(A\), not a new definition of
the quotient. The kernel is closed. The even submodule is closed by the
reflection fixed-point condition; averaging is a continuous retraction
onto it.

On `Masullo.RationalRealThetaQuotient`, the actual topological module
quotient, `Masullo.rationalRealThetaEquiv` sends \([f]\) to \(Af\), and
sends an even \(g\) back to \([g/2]\). Both maps are continuous (quotient
descent and inclusion followed by the quotient map), \(A(g/2)=g\), and
\([Af/2]=[f]\) by the kernel equality. Closedness of the even subspace and
`Masullo.completeSpace_schwartzLine` give completeness, transferred using
the canonical additive uniformity of the **quotient** topology. It is also
Hausdorff, metrizable and real locally convex. Complex scalar multiplication
and the equivalence remain complex linear where appropriate. The inverse
equivalence is a closed embedding onto the quotient, so the constant
presentation of this space (identity transition maps) is strict with one
Fréchet stage repeated. No nuclearity is formalized, and the general
fixed-S sum, closed kernel and strict topology are still open here.

## Reproduce the Lean checks

In the workspace, run `lake build --wfail +Theorems.RationalRealThetaQuotient`.
For signatures and transitive axioms of all public endpoints, create a
scratch file with ordinary imports and run it in the pinned Lake environment:

```sh
check=$(mktemp --suffix=.lean)
{
  printf 'import Theorems.RationalRealThetaQuotient\nimport Lemmas.SchwartzLineComplete\n'
  sed -nE 's/^(@\[[^]]+\] )?public ((noncomputable )?(def|abbrev)|theorem) ([A-Za-z0-9_]+).*/\5/p' \
    Proofs/Theorems/RationalRealThetaQuotient.lean |
    while IFS= read -r name; do
      printf '#check @Masullo.%s\n#print axioms Masullo.%s\n' "$name" "$name"
    done
} > "$check"
lake env lean "$check"
```

The writer build and checks passed on the submitted Lean file: all 21
public endpoints report only `propext`, `Classical.choice`, `Quot.sound`.
The ordinary-import client below passed with `lake env lean` on a scratch
copy. It applies the equivalence on genuine quotient representatives,
uses its inverse on an arbitrary even profile and gets the actual local
theta value, uses uniform convergence for a pointwise sum, and uses the
quotient and Fréchet facts.

```lean
import Theorems.RationalRealThetaQuotient

open Masullo
open scoped SchwartzMap

example (f : 𝓢(ℝ, ℂ)) (x : ℝˣ) :
    (rationalRealThetaEquiv (rationalRealTheta.ker.mkQL f)).1 x = rationalRealTheta f x := by
  rw [Submodule.mkQL_apply, rationalRealThetaEquiv_mkQ_apply_unit]

example (f : 𝓢(ℝ, ℂ)) :
    (rationalRealThetaEquiv (rationalRealTheta.ker.mkQ f)).1 0 = f 0 + f 0 := by
  simpa using rationalRealThetaEquiv_mkQ_apply f 0

example (g : 𝓢(ℝ, ℂ)) (hg : ∀ x : ℝ, g (-x) = g x) (x : ℝˣ) :
    rationalRealTheta (((2 : ℂ)⁻¹) • g) x = g x := by
  let e : rationalRealEvenSchwartz := ⟨g, (mem_rationalRealEvenSchwartz g).2 hg⟩
  have h := congrArg (fun a : rationalRealEvenSchwartz ↦ a.1 (x : ℝ))
    (rationalRealThetaEquiv.apply_symm_apply e)
  rw [rationalRealThetaEquiv_symm_apply, rationalRealThetaEquiv_mkQ_apply_unit] at h
  simpa [e] using h

example (f : 𝓢(ℝ, ℂ)) (x : ℝˣ) :
    HasSum (fun u : ℤˣ ↦ f ((u : ℤ) * (x : ℝ))) (rationalRealTheta f x) :=
  (rationalRealTheta_hasSumUniformlyOn f Set.univ).hasSum (Set.mem_univ x)

example : Topology.IsQuotientMap rationalRealTheta.ker.mkQL ∧
    Topology.IsClosedEmbedding rationalRealThetaEquiv.symm :=
  ⟨Submodule.isQuotientMap_mkQL _, rationalRealThetaQuotient_closedStage.1⟩

example : @CompleteSpace RationalRealThetaQuotient
    (IsTopologicalAddGroup.rightUniformSpace RationalRealThetaQuotient) :=
  rationalRealThetaQuotient_frechet.1
```
