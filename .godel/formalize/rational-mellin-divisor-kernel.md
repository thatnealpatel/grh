# §1.2.1 — rational Mellin-divisor kernel, and the full-product obstruction

Formalize key `8d24a7b4b6c038674ad116416b312debc22b39b18d42997d30767a1847fc0040`,
Walk revision `c4e2aa533026da5e44701c36d62b6e10c4408501ba03af0b11a77ff7a5a82efd`.
Writer session `01a205c9-8a7f-7ed5-bb91-44348def2a8e`, accepted base
`0e66f3c9aff0bb84e06868edff24a340b4d14fdb`. This note records the writer's
checks, not adoption or independent review.

## Source reading

Verified the local PDF against the [edition pin](../sources/masullo/README.md):
SHA-256 `e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5`.
Printed page numbers below equal the one-based PDF ordinals. On p. 13, §1.2.1,
read the unnumbered third sequence, just below “The Mellin transform turns the
second exact sequence into (forgetting about the uniformly Schwartz condition
defining Schwartz-Bergman spaces)”. It reads

\[
0\longrightarrow L(s+1/2,\chi)((s+1/2)(s-1/2))^\delta\mathcal O(\mathbb C)
\cap A\mathcal S(\mathbb C) \longrightarrow A\mathcal S(\mathbb C)
\longrightarrow \prod_{z:L(z,\chi)=0}\mathbb C^{N(z)}\longrightarrow 0.
\]

The immediately following paragraph defines the multiplicity and sets
\(\delta=0\) for nontrivial norm-one restriction, and \(\delta=1\) otherwise.
It invokes the Structure Theorems, convexity and horizontal segments on which
\(1/L_f\) is defined and of polynomial growth in the absolute ordinate. These
are estimates about the **finite** factor: §1.2 p. 12 distinguishes it from
completed \(L\); compare Prop. B.1.1.3, (B.1.1.12), p. 591, and Cor. B.6.1.8,
(B.6.1.45), p. 643, for an Euler product outside a finite set. They do not
produce a uniformly Schwartz interpolant for an arbitrary full jet array.
The subsequent Stein-sheaf display compares a sequence for the **entire**
space. It does not prove the displayed surjectivity for the Schwartz subspace.
The parenthetical may signal an intended entire-function comparison; replacing
both occurrences of \(A\mathcal S\) by \(\mathcal O\) is a change to the
literal display, not a consequence of overlooking the topology.

For the domain read the bottom of p. 800 and the top of p. 801, Definition
D.3.1.3 including its displayed seminorms: the underlying functions are
holomorphic, Schwartz uniformly on bounded-width vertical strips. Lemma
D.3.1.1, pp. 797–798 and displays (D.3.1.1)–(D.3.1.4), explains the weighted
derivative bounds from the weighted function bounds by shrinking strips. For
\(I=\mathbb R\), each bounded closed strip lies inside a larger bounded open
one, so all the bounds in `schwartzBergmanEntire` describe precisely this
underlying set. We do not use the selected-line \(L^p\) topology. Theorem
D.3.3.13, (D.3.3.11)–(D.3.3.12), pp. 812–813, concerns the ambient Mellin
transform; Theorem 6.3.2.1(1), (6.3.2.3)–(6.3.2.4), pp. 304–309, claims the
**theta** image range (the first arrow), not arbitrary joint interpolation
(the last arrow). See the [accepted weighted-stage handoff](rational-theta-weighted-stage.md)
for its still-open comparison with the actual theta image.

For \(F=\mathbb Q\), choose \(\chi=1\), \(w=s+1/2\). Read the Euler and
real gamma factors (3.2.1.2)–(3.2.1.4) and Prop. 3.2.1.3(2)–(4), p. 123:
\(L(w,1)=\pi^{-w/2}\Gamma(w/2)\zeta(w)\), with simple poles at 0 and 1
(\(t_0=0\)). The generator in the display is the **entire extension** of
\(w(w-1)L(w,1)\), not pointwise multiplication by the totalized Lean value
of `completedRiemannZeta` at either pole. `entireZeta` takes value one at
both points. The gamma factor is holomorphic and nonzero in the open strip,
so the completed zeros there have exactly the analytic orders of \(\zeta\).
Outside the strip, the already checked
`completedZeta_eq_zero_iff_mem_criticalStripZetaZeros` uses nonvanishing of
\(\zeta\) on \(\Re w\ge1\), the completed functional equation, and the same
gamma comparison in the right half-plane. In particular the negative-even
trivial zeros are not part of the completed divisor. Translation takes
\(\rho\) to \(\rho-1/2\), preserves ordinate and multiplicity, and places all
these locations inside \(|\Re(s)|<1/2\). The Taylor coordinates are the local
jets of the displayed divisor (the arrow is not spelled out coordinatewise on
p. 13); compare the derivative coordinates in Theorem 7.1.4.2(2)–(4),
(7.1.4.6)–(7.1.4.8), pp. 326–327.

## Checked middle exactness

`Lemmas.EntireDivisorDivision` proves that for nonzero entire \(g\) and entire
\(f\), the equations \(f^{(k)}(z)=0\) at every zero of \(g\) for all
\(k<\operatorname{ord}_z(g)\) are equivalent to \(f=gq\) with \(q\) entire.
The identity theorem gives finite order for nonzero entire functions; the
jet condition is precisely the pointwise order inequality, automatically
true off the divisor. At each point the meromorphic quotient has nonnegative
order (subtract the finite denominator order), so its meromorphic normal
form is analytic there. Near any point in a punctured neighborhood the
normal form agrees with the ordinary quotient and the denominator is nonzero;
continuity extends the product identity to the point. The zero numerator is
handled separately. The converse adds analytic orders. There is no estimate
on the quotient.

`Theorems.RationalMellinDivisorKernel` instantiates the generator, proves the
identity off the poles, identifies its exact zeros and orders, and defines
its jets with the usual \(1/k!\) normalization. Its middle kernel statement
is equality of subsets of `ℂ → ℂ`; it is not a claim about the theta image,
a quotient topology, or any completed Sobolev space. The accepted inputs
are `Lemmas.ShiftedZetaZeros`, `Lemmas.RationalCompletedZetaZeros`,
`Lemmas.ZetaZeroOrders` and `Lemmas.CompletedZetaOrders` at the base above.

## Right arrow: classical input versus Lean

**Classical input from the pinned source, not checked in Lean.** In the
proof of Theorem 7.1.4.2(1), p. 327, (7.1.4.9) immediately after the definition
of \(\Lambda(s,\chi)\) invokes Barner, *On A. Weil's explicit formula*, Thm. 2
(the manuscript's [Bar]). For the rational trivial character it states
\(\Lambda(w,1)=\Lambda(0,1)\prod'_{\rho:L(\rho,1)=0}(1-w/\rho)\), where
\(\Lambda(w,1)=\tfrac12 w(w-1)L(w,1)\), and the product is the compact-locally
uniform limit of the height-truncated products over conjugate pairs, counting
multiplicity. Only this factorization is used here, not the quotient or
cohomological argument on the next page. If there were finitely many
*distinct* completed zeros, all their orders would be finite because the
entire generator is not identically zero. None is zero. The truncated
products would stabilize to a polynomial. But for integers \(n\ge 1\),
\(\Lambda(2n,1)=n(2n-1)\pi^{-n}(n-1)!\,\zeta(2n)\). The Dirichlet series
has \(\zeta(2n)\ge 1\); the factorial divided by \(\pi^n\) outgrows every
polynomial (e.g. retain the factors \(j\ge\lceil n/2\rceil\)). This proves
classical infinitude of precisely the distinct open-strip zeros used here.
Compact subsets contain finitely many zeros, so their shifted ordinates are
unbounded in absolute value.

**Checked obstruction.** `rationalMellinDivisorJet_ne_one` takes `Infinite
criticalStripZetaZeros` explicitly. Every zero has positive order, so the
array with all entries one would force \(f(\rho-1/2)=1\) at each zero. The
bound on \(|sf(s)|\) on the closed strip \([-1/2,1/2]+i\mathbb R\) would put
all shifted zeros in one closed ball. The accepted compact-preimage
finiteness then contradicts infinitude. This disproves unrestricted product
surjectivity with the classical infinitude input even before choosing a
product topology. An unconditional Lean obstruction requires formal distinct
zero infinitude. Any Schwartz–Bergman replacement target needs an actual
interpolation theorem specifying which arrays are reached, and separate
topology checks; the whole jet product is not such a target. The entire-space
comparison (classically, Cartan B for the coherent ideal sheaf on the Stein
plane) has no such strip constraint, but its surjectivity is not proved
here. Neither general Hecke cases nor the preceding theta topology are
claimed.

## Rerunnable writer checks

From the exact writer workspace:

```sh
lake build --wfail +Lemmas.EntireDivisorDivision +Theorems.RationalMellinDivisorKernel
lake env lean /tmp/RationalMellinClient.lean
```

Both passed at the writer. Place the block below in that scratch path (or
use another fresh path). Each of the ten axiom reports is exactly
`[propext, Classical.choice, Quot.sound]`. The examples use ordinary imports
and apply the endpoints to compute an off-divisor quotient, obtain a derivative
at a multiple zero, and refute surjectivity under the explicit infinitude
input.

```lean
import Lemmas.EntireDivisorDivision
import Theorems.RationalMellinDivisorKernel

open Masullo Set

#check @schwartzBergmanEntire
#print axioms schwartzBergmanEntire
#check @rationalMellinDivisorGenerator
#print axioms rationalMellinDivisorGenerator
#check @rationalMellinDivisorJet
#print axioms rationalMellinDivisorJet
#check @entire_mul_iff_vanishing_jets
#print axioms entire_mul_iff_vanishing_jets
#check @rationalMellinDivisorGenerator_eq_mul
#print axioms rationalMellinDivisorGenerator_eq_mul
#check @rationalMellinDivisorGenerator_eq_zero_iff
#print axioms rationalMellinDivisorGenerator_eq_zero_iff
#check @rationalMellinDivisorGenerator_order
#print axioms rationalMellinDivisorGenerator_order
#check @rationalMellinDivisorJet_eq_zero_iff
#print axioms rationalMellinDivisorJet_eq_zero_iff
#check @rationalMellinDivisorJet_kernel
#print axioms rationalMellinDivisorJet_kernel
#check @rationalMellinDivisorJet_ne_one
#print axioms rationalMellinDivisorJet_ne_one

-- Abandon the raw quotient at zeros: obtain a genuine entire quotient and
-- compute it by ordinary division at any point off the divisor.
example {f : ℂ → ℂ} (hf : f ∈ schwartzBergmanEntire)
    (hjets : ∀ ρ k, rationalMellinDivisorJet f ρ k = 0) :
    ∃ q : ℂ → ℂ, AnalyticOnNhd ℂ q univ ∧
      ∀ s, rationalMellinDivisorGenerator s ≠ 0 → q s = f s / rationalMellinDivisorGenerator s := by
  have hker : f ∈ {g ∈ schwartzBergmanEntire | rationalMellinDivisorJet g = 0} :=
    ⟨hf, funext fun ρ ↦ funext fun k ↦ hjets ρ k⟩
  rw [rationalMellinDivisorJet_kernel] at hker
  obtain ⟨_, q, hq, hmul⟩ := hker
  refine ⟨q, hq, fun s hs ↦ ?_⟩
  apply (eq_div_iff hs).mpr
  simpa [Pi.mul_apply, mul_comm] using (congrFun hmul s).symm

-- At a multiple zero the first derivative of any visible ideal member vanishes.
example {f q : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f univ)
    (hq : AnalyticOnNhd ℂ q univ) (hmul : f = rationalMellinDivisorGenerator * q)
    (ρ : criticalStripZetaZeros) (hρ : 1 < zetaZeroOrder ρ) : deriv f (shiftedZetaZero ρ) = 0 := by
  have h := congrFun (congrFun ((rationalMellinDivisorJet_eq_zero_iff hf).mpr ⟨q, hq, hmul⟩) ρ)
    (⟨1, hρ⟩ : Fin (zetaZeroOrder ρ))
  change iteratedDeriv 1 f (shiftedZetaZero ρ) / ((1 : ℕ).factorial : ℂ) = 0 at h
  simpa using h

-- The full jet product is too large if the actual distinct divisor is infinite.
example (hinf : Infinite criticalStripZetaZeros) :
    ¬ Function.Surjective (fun f : schwartzBergmanEntire ↦ rationalMellinDivisorJet f.1) := by
  intro hsurj
  obtain ⟨f, h⟩ := hsurj 1
  exact rationalMellinDivisorJet_ne_one hinf f.property h
```
