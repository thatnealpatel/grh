# Radial singleton Hardy–Sobolev density

Chapter 01 passage `98d513f4f4f68d774d92fbf6a72433d0169263942d8673c7f11b1ad4bd39e08d`,
revision `ec1c9c8b4db67718ad8b0b2bd9e0e09806bc0d484851e14d2fe9a6ee71bfae2d`.
[Receipt](98d513f4f4f68d774d92fbf6a72433d0169263942d8673c7f11b1ad4bd39e08d-ec1c9c8b4db67718ad8b0b2bd9e0e09806bc0d484851e14d2fe9a6ee71bfae2d.json).
The writer base was `585aec3b6fa21341f3c9f6b16d0356714f2e3ca6`,
which differs from the request's accepted tip
`198b80a26562ac7e97db2c38a75ddb6200e388fe` only in `cmd/companion/nodes.go`.
The owning check/review session is `01a20506-84db-7d32-9f57-557f8f19c2a8`.
The checks below are writer checks, not a claim of integration or adoption.

## What the printed passage says

The writer checked the 940-page PDF against the [edition pin](../sources/masullo/README.md):
SHA-256 `e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5`.
The locators below use printed pages, which coincide here with one-based
PDF ordinals. `pdftotext -layout` located the passages; the checks used
page renders with OCR, and higher-resolution display crops to distinguish
order signs and the dual hats.

- **Claim, pp. 11–12, §1.1.3.** The introduction uses a second-countable
  Hausdorff locally compact abelian group with proper surjective module
  \(|\cdot|_G:G\to\mathbb R_{>0}\). The unnumbered p. 11 display defines
  the squared norm on \(S_E(G)\) with the weight
  \(\max(|g|_G^{2a},|g|_G^{2b})(1+|\log |g|_G|^2)^{s/2}\) against fixed
  Haar. The preceding definition has \(a<b\), so it does not define the
  singleton. The p. 12 sentence after naming the space asserts without
  proof that for \(I=\{0\}\) it agrees with \(W^{s,2}(G)\).
  Section 1.1.2, p. 11, (1.1.2.1) and the all-weight bullet specify the
  exponential membership condition \(|\cdot|_G^a\phi\in S(G)\) for every
  \(a\in\mathbb R\).
- **Singleton definition, pp. 416–417.** Definition 9.2.2.9 (9.2.2.31)
  completes \(S_E(G)\) for nonempty closed \(I\) and real \(s\ge0\).
  Its supremum is over \(a\le b\) with \([a,b]\subseteq I\), with
  canonical Haar. For \(I=\{0\}\) the only interval is \([0,0]\):
  the maximum in Lemma 9.2.2.10(2), (9.2.2.34), is \(1\).
  The squared singleton norm is therefore
  \(\int_G |\phi(g)|^2(1+|\log|g|_G|^2)^{s/2}\,d\mu_{\rm can}(g)\).
  The radial counterparts on p. 412, Definition 9.2.2.1 (9.2.2.3) and
  Lemma 9.2.2.2(2) (9.2.2.4), likewise allow equality of endpoints
  and use \(dt/t\).
- **Sobolev realization, pp. 396–397, 399.** Definition 9.1.2.1
  (9.1.2.2) says \(W^{s,2}(G)=H_w^s(\widehat G,\mu_{\widehat G})\),
  not \(H_w^s(G,\mu_G)\), for real \(s\ge0\). Here (9.1.2.1) sets
  \(w(g)=|\log |g|_G|\). In Definition 9.1.1.1, (9.1.1.1)–(9.1.1.3),
  the integrand is the Fourier transform squared, with the weight and
  Plancherel measure on the **dual of the input group**. Lemma 9.1.1.2
  realizes the resulting space as weighted \(L^2\) on that dual (the
  continuous positive density gives a Radon measure); the Plancherel
  calculation in the proof of Proposition 9.1.1.3(1) on p. 397 confirms
  the variable convention. The printed phrase “completion of
  \(C_c(\widehat G)\)” in Definition 9.1.1.1 should not be read as saying
  that the Fourier transform in (9.1.1.3) acts on those very functions
  and integrates back on \(\widehat G\). Nor does arbitrary compactness
  of **input-side** support imply a finite weighted Fourier norm:
  for instance the triangular function on \(\mathbb R\) has Fourier
  transform \((\sin(\pi\xi)/(\pi\xi))^2\), which is not in the weighted
  target for \(w(\xi)=|\xi|\), \(s=4\). The comparison here uses the
  weighted realization, not a literal completion of all input-side
  \(C_c\) in the Fourier-weighted norm.
  For (9.1.2.2) the input group is \(\widehat G\), so the weighted
  Fourier variable belongs to \(\widehat{\widehat G}\cong G\).
  Under this identification the Plancherel measure for
  \(\mu_{\widehat G}\) is \(\mu_G\), by Fourier inversion and uniqueness
  (pp. 746–747, Theorem D.1.1.1 (D.1.1.2)–(D.1.1.3), (D.1.1.4),
  and Lemma D.1.1.2(4)–(5) (D.1.1.9)–(D.1.1.11)). This is the
  physical-variable norm (9.1.2.3), with exactly the same polynomial
  weight as the singleton norm and with the chosen Haar \(\mu_G\).
- **Haar matters independently of density.** At p. 400, first
  paragraph after the definition, a supplied continuous homomorphic
  section gives the split \(G\cong\mathbb R_{>0}\times G^1\), with Haar
  \(dt/t\otimes\mu_1\); the second factor absorbs the Haar scalar.
  The following dual paragraph uses the basic character \(t^{2\pi i}\).
  At p. 793, Definition D.2.1.1 (D.2.1.3)–(D.2.1.4) defines canonical
  normalization by module-window mass \(2\log \Lambda+O(1)\).
  Remarks D.2.1.2–3 (D.2.1.5) discuss the section and take mass one
  on \(G^1\) and \(dt/t\) in the surjective case. In that product the
  interval has mass exactly \(2\log\Lambda\), so the same asymptotic
  forces the compact factor to have mass one. Multiplying Haar by
  \(c>0\) multiplies the norm by \(\sqrt c\); the identity on functions
  is isometric for matched Haar, and multiplication by \(c^{-1/2}\)
  is the isometry from the original weighted \(L^2\) to the rescaled one.
  The log-coordinate change of variables below fixes the
  radial normalization; it does not prove this arbitrary-Haar bridge.

Thus direct substitution proves equality of the two test-function norms
with matched Haar, not that the original tests are dense in the ambient
weighted space. In particular the [accepted radial common-completion
proof](radial-hardy-sobolev-completion.md) only identified two image closures.

## Checked radial result

[`Theorems.RadialSingletonSobolev`](../../Proofs/Theorems/RadialSingletonSobolev.lean)
uses \(G=\mathbb R_{>0}\) with identity module and normalized \(dt/t\).
At \(x=\log t\), the underlying measure is Lebesgue measure and the
weighted measure is exactly \((1+|x|^2)^{s/2}\,dx\). The existing
[`Theorems.RadialHardySobolevCompletion`](../../Proofs/Theorems/RadialHardySobolevCompletion.lean)
provides `logSobolevToLp_injective`, `norm_logSobolevToLp`,
`logSobolevToLp_positiveIntegral`, and `logSobolevAllToLp_ae_eq`, using
`Masullo.map_volume_exp_eq_restrict_realMultiplicative` for the
positive-real integral. The complex-linear all-weight map is the
composition of the original inclusion into closed-interval profiles
with this norm-preserving, faithful embedding. At the singleton this
is the printed metric on the test functions. The pointwise all-weight
condition is not replaced by a new space: p. 593 before Definition
B.2.1.1 has Schwartz seminorms in \(x=\log t\) and
\(t\partial_t=\partial_x\); p. 801, Definition D.3.2.1 (D.3.2.1)
and Lemma D.3.2.3(6), prescribe the actual Schwartz condition after
multiplication by every real power. Example D.3.3.4, p. 805, identifies
the identity-module case with this radial construction.

For any proposed target \(Y\) in weighted \(L^2\), continuity of the
density gives a locally finite (and regular) measure. The Mathlib
compact-support approximation theorem on that measure gives a continuous
compactly supported \(g\) within \(\varepsilon/2\) of \(Y\).
Convolving \(g\) on the log line with a Lebesgue-normalized smooth bump
of radius \(r\le1\) gives smooth \(u\). The bump mass is one with
respect to **Lebesgue** measure; the approximation error is measured
in the **weighted** measure \(\mu\). Both supports are contained in the
fixed compact unit thickening \(K\) of the support closure of \(g\).
Uniform continuity lets the uniform error be at most
\(\eta=(\varepsilon/2)/(1+\sqrt{\mu(K)})\); its weighted \(L^2\) norm
is at most \(\eta\sqrt{\mu(K)}<\varepsilon/2\). The weighted measure
of \(K\) is finite by local finiteness. For each \(a\in\mathbb R\),
\(e^{ax}u(x)\) is smooth and compactly supported, so has a pointwise
`SchwartzMap` representative, giving membership in the original
`logWeightedProfiles univ`. The a.e. representative lemma identifies
its image with \(u\) in this same `Lp`; the triangle inequality gives
the asserted approximation at arbitrary \(Y\).

The three exported results are `Masullo.logSobolevWeight_singleton`,
`Masullo.exists_logSobolevAllToLp_singleton_dist_lt`, and
`Masullo.logSobolevAllToLp_denseRange_singleton`. The latter, together
with the accepted faithful norm embedding and completeness of the
ambient \(L^2\), gives a concrete completion. Lean works for all real
\(s\), extending the printed range \(s\ge0\). There is no assertion here
of an equivalence with an abstract Lean `Completion` type, a formal
Fourier comparison on the abstract dual, or density in the test-space
LF topology.

## Remaining general obligations

For general \(G\) formalize the continuous homomorphic split, or work
from a supplied one first, then normalize Haar. The accepted
[`Masullo.logVolume_prod_of_split_haar`](../../Proofs/Lemmas/HaarLogSplit.lean)
checks a Haar product pushforward **conditional on** such an equivalence;
it does not construct the split or force the compact factor to have mass
one. On a split log product \(\mathbb R\times K\), with \(K=G^1\),
a radial test of smooth compact support times a continuous character
\(\chi\) on \(K\) descends through \(\ker\chi\) to the elementary Lie
quotient \(\mathbb R\times(K/\ker\chi)\): the compact image in the
circle is either a finite cyclic group or the circle. The annihilator
of \(\ker\chi\) in \(\widehat G\) is the dual of that quotient and is
compactly generated, as required by the actual stage condition.
Check that the descended tests are smooth and of rapid decay after
multiplying by *every* real exponential weight (p. 750,
Definition D.1.3.1 (D.1.3.6)–(D.1.3.7); p. 762, Definition D.1.5.3(2)
(D.1.5.3); pp. 804–805, Definitions D.3.3.1 and D.3.3.3
(D.3.3.1)–(D.3.3.2)). The same stage condition must hold for finite
sums, using a common kernel if needed. A proposed density proof uses
the span of characters dense in compact-fiber \(L^2\) and the product
of this dense span with the weighted radial test space, under the
matched split Haar. One must also prove finiteness for arbitrary
all-weight stages using their log-polynomial Schwartz decay. Neither
the genuine stage construction nor the product-density argument has
been checked in Lean here. The change from a fixed to canonical Haar
and the dual realization are separate normalization/representation
obligations, not consequences of the radial approximation lemma.

## Replay

In Lean 4.36.0 the build below passed with `--wfail` and the ordinary-import
client compiled. Every reported transitive axiom list was exactly
`[propext, Classical.choice, Quot.sound]`. The first client example
checks the literal measure, the second uses the dense range at an
arbitrary element of that ambient space, and the third uses the
approximation lemma to obtain a nearby class with an original compact
pointwise profile.

```sh
lake build --wfail +Theorems.RadialSingletonSobolev +Theorems.RadialHardySobolevCompletion +Theorems.RadialWeightedSchwartzStage +Theorems.RealMultiplicativeMeasure &&
probe=$(mktemp /tmp/grh-radial-singleton-XXXXXX.lean) &&
sed -n '/^```lean$/,/^```$/{ /^```/d; p; }' .godel/formalize/radial-singleton-sobolev.md > "$probe" &&
lake env lean "$probe"
```

```lean
import Theorems.RadialSingletonSobolev
import Theorems.RadialHardySobolevCompletion
import Theorems.RealMultiplicativeMeasure

open Masullo MeasureTheory Set
open scoped ENNReal

#check @Masullo.logSobolevWeight_singleton
#check @Masullo.exists_logSobolevAllToLp_singleton_dist_lt
#check @Masullo.logSobolevAllToLp_denseRange_singleton
#print axioms Masullo.logSobolevWeight_singleton
#print axioms Masullo.exists_logSobolevAllToLp_singleton_dist_lt
#print axioms Masullo.logSobolevAllToLp_denseRange_singleton

-- The actual measure of the endpoint, not just an equality of profile norms.
example (s : ℝ) : logSobolevMeasure 0 0 s = (volume : Measure ℝ).withDensity
    (fun x ↦ ENNReal.ofReal ((1 + |x| ^ 2) ^ (s / 2))) := by
  simp only [logSobolevMeasure, logSobolevWeight_singleton]
  rfl

-- Use the dense range at an arbitrary weighted L² element to get a profile.
example (s : ℝ) (Y : Lp ℂ 2 (logSobolevMeasure 0 0 s)) (ε : ℝ) (hε : 0 < ε) :
    ∃ u : logWeightedProfiles univ,
      ‖Y - logSobolevAllToLp (le_refl (0 : ℝ)) s u‖ < ε := by
  obtain ⟨u, hu⟩ := Metric.mem_closure_range_iff.mp
    (logSobolevAllToLp_denseRange_singleton s Y) ε hε
  exact ⟨u, by simpa only [dist_eq_norm] using hu⟩

-- Obtain a compactly supported pointwise representative of a nearby L² class.
example (s : ℝ) (Y : Lp ℂ 2 (logSobolevMeasure 0 0 s)) (ε : ℝ) (hε : 0 < ε) :
    ∃ Z : Lp ℂ 2 (logSobolevMeasure 0 0 s), ∃ u : logWeightedProfiles univ,
      HasCompactSupport u.1 ∧ ((Z : ℝ → ℂ) =ᵐ[logSobolevMeasure 0 0 s] u.1) ∧
        dist Y Z < ε := by
  obtain ⟨u, hc, hu⟩ := exists_logSobolevAllToLp_singleton_dist_lt s Y hε
  exact ⟨_, u, hc, logSobolevAllToLp_ae_eq (le_refl (0 : ℝ)) s u, hu⟩
```
