# Closed-interval radial Hardy–Sobolev completion

Passage `c070557c8c29efcae22c255908ae05ebf50c3fdbe72a0a82ee30890ec2388db6`,
revision `a986b35a4a779b2280e466f8106655ae3d3b73df0d364c4dac988b6c9a1a9a6f`.
Writer base `6f1d672bc14e2f53d6fc17f45019bf1b61e64e8b`.
The owning check and review session is `01a204ee-bc52-78f5-a2a5-5d30667df70c`.
After integration, that session records the full candidate and base IDs,
check outputs, and independent review. The writer checks below do not
establish that the integrated candidate passed.
See the [receipt](c070557c8c29efcae22c255908ae05ebf50c3fdbe72a0a82ee30890ec2388db6-a986b35a4a779b2280e466f8106655ae3d3b73df0d364c4dac988b6c9a1a9a6f.json).

## Printed claim and proof route

The writer verified the PDF against SHA-256
`e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5`
in the [edition pin](../sources/masullo/README.md), used `pdftotext -layout`
for navigation, and read the relevant page renders, using OCR on the images
and checking the order signs in the exponent-range prose. Printed pages
and one-based PDF ordinals coincide at all locators below.

- **Claim:** p. 11, §1.1.3, first paragraph and unnumbered norm display.
  For a second-countable locally compact Hausdorff abelian group with
  a proper surjective module to \(\mathbb R_{>0}\) and \(a<b\), the
  weighted norm completions of \(S_E(G)\) and \(S_{[a,b]}(G)\) coincide.
  The squared norm integrates
  \(|\phi(g)|^2\max(|g|_G^{2a},|g|_G^{2b})(1+|\log |g|_G|^2)^{s/2}\)
  against the fixed Haar measure. No range for \(s\) is stated here.
  Section 1.1.2, (1.1.2.1) and the following bullet define closed-interval
  membership by all weights in \([a,b]\) and \(E=\mathbb R\) membership
  by all real weights. Definition D.2.1.1 (D.2.1.3), p. 793, defines
  modulation by a proper homomorphism; §D.3.3, first paragraph, p. 804,
  uses “\(\mathbb R_{>0}\)-modulated” for the surjective case.
- **Companion statements:** p. 412, Definition 9.2.2.1 and Lemma 9.2.2.2,
  (9.2.2.3)–(9.2.2.4), treat real \(s\ge0\) with \(dt/t\) and
  include \(a=b\) in the compact-interval formula. The supremum over
  subintervals reduces to the endpoint formula since each subinterval's
  maximum weight is bounded by that of \([a,b]\) and \([a,b]\) itself
  is included. The split at \(t=1\) in (9.2.2.10)–(9.2.2.11), p. 413,
  gives the relevant endpoint reduction on closed-interval profiles. The
  general formulation at pp. 416–417, Definition 9.2.2.9 (9.2.2.31) and
  Lemma 9.2.2.10(2) (9.2.2.34), uses canonical Haar and again \(s\ge0\).
  The equal-completion statements in the two lemmas' parts (1) use a
  nonempty **open** interval \(J\) containing \(I\). The radial statement
  (Lemma 9.2.2.2(1), p. 412, PDF ordinal 412) prints
  \(J\subset\mathbb R_{>0}\), apparently a typo for a weight interval in
  \(\mathbb R\). Neither open-interval statement by itself gives the
  closed-endpoint claim in §1.1.3.
- **Density route:** §1.1.3 gives no proof. Lemma D.3.6.1, pp. 819–821,
  attempts a stronger compact-support density theorem via a tensor
  reduction (D.3.6.1) and a cutoff. In (D.3.6.2), the top derivative
  retains a factor \(\psi(x/m)\), rather than the printed factor 1.
  Therefore (D.3.6.3)–(D.3.6.4) miss the corresponding cutoff tail
  (for \(k=0\), their sum is empty). The displayed radial seminorms
  also omit the polynomial weights from the ordinary Schwartz topology.
  The proof below does not invoke this density theorem or the tensor
  reduction.

## Checked radial repair

[`Theorems.RadialHardySobolevCompletion`](../../Proofs/Theorems/RadialHardySobolevCompletion.lean)
uses \(G=\mathbb R_{>0}\) with identity module. The ordinary Schwartz
seminorm display before Definition B.2.1.1, p. 593, uses \(x=\log t\)
and \(t\partial_t=\partial_x\). Definition D.3.2.1 (D.3.2.1), p. 801,
and Example D.3.3.4, p. 805, give the weighted membership and its
radial specialization. The existing `logWeightedProfiles I` consists of
smooth functions for which every \(e^{cx}f(x)\) with \(c\in I\) has an
actual `SchwartzMap ℝ ℂ` representative. This is not a larger space
specified by unweighted smoothness alone or a smaller space requiring
exponential decay past the endpoints.

With `hab : a ≤ b`, both endpoints belong to `Icc a b`. Bounding the
log-polynomial by a fixed ordinary polynomial and the maximum by the
sum, integrability reduces to polynomially weighted squared norms of
these two Schwartz maps. One factor is bounded by the zeroth Schwartz
seminorm; the other is integrable with arbitrary polynomial weights.
Both parameter extensions (`a = b` and real `s < 0`) are allowed by the
proof, not hypotheses of the printed p. 11 statement. The theorem does
not assume that 0 belongs to the interval. A reversed interval would
have no endpoint Schwartz controls, so it is excluded.

The density is positive everywhere, so the weighted `L²` a.e. quotient
is injective on continuous profiles. The two embeddings are complex-linear;
the all-weight map factors through interval membership. The change of
variables is checked using the accepted
`Masullo.map_volume_exp_eq_restrict_realMultiplicative`: against the
positive restriction of `dt/|t|`, the expression is exactly the one on
p. 11 for this normalized Haar, with `t ↦ f (log t)`. The norm of a
difference follows by linearity and the norm formula. Thus the induced
metric is the one from the printed norm, not the profile-stage topology.

A smooth radial bump evaluated at \(x/(n+1)\) lies in \([0,1]\), has
compact support, and is eventually 1 at each \(x\). Its product with
any closed-interval profile is smooth and compactly supported even after
multiplication by \(e^{cx}\) for **every** real \(c\). The squared-norm
error integrand is bounded by the already integrable squared-norm
integrand of \(f\) and tends to zero pointwise. Dominated convergence
and the square-root norm formula give convergence in `L²`. Consequently
the closure of the image of either space is the same complete metric
subspace of the weighted `L²`; this models a common isometric completion
via the original norm and original inclusions. It is not a claim that
the closure fills `L²` or a construction of an equivalence between
abstract `Completion` types.

**Remaining obligation:** general \(G\) and arbitrary fixed Haar. A route
not requiring LF density is to derive uniform inverse-polynomial
log-module bounds for the two endpoint-weighted profiles in actual
Schwartz–Bruhat stages, push fixed Haar along the proper surjective
log-module to \(c\,dx\) with \(0<c<\infty\), and prove stage membership
in \(S_E(G)\) for the products by the pulled-back smooth cutoffs with
compact support by properness. None of these nonradial stage/measure
bridges is asserted by the present module. No fine-topology density or
Mellin/strip claim is established.

## Replay

Writer checks in Lean 4.36.0: the three targets below built with `--wfail`;
the ordinary-import file below checked all public signatures and applied
the results to singleton finiteness, the literal positive-real distance,
compact-support approximation within arbitrary positive error, and
completeness on the all-weight side. Every `#print axioms` reported
exactly `propext`, `Classical.choice`, `Quot.sound`.

From the project root, copy the Lean block into a fresh scratch file, or
extract it with the command below:

```sh
lake build --wfail +Theorems.RadialWeightedSchwartzStage +Theorems.RealMultiplicativeMeasure +Theorems.RadialHardySobolevCompletion
probe=$(mktemp /tmp/grh-radial-sobolev-XXXXXX.lean)
sed -n '/^```lean$/,/^```$/{ /^```/d; p; }' .godel/formalize/radial-hardy-sobolev-completion.md > "$probe"
lake env lean "$probe"
```

```lean
import Theorems.RadialHardySobolevCompletion
import Theorems.RadialWeightedSchwartzStage
import Theorems.RealMultiplicativeMeasure

open Filter MeasureTheory Set
open scoped Topology
open Masullo

#check @logSobolevWeight
#check @logSobolevMeasure
#check @integrable_logSobolevWeight_mul_norm_sq
#check @memLp_logSobolevMeasure
#check @logSobolevToLp
#check @logSobolevToLp_ae_eq
#check @logSobolevToLp_injective
#check @norm_logSobolevToLp
#check @logSobolevToLp_positiveIntegral
#check @logSobolevAllToLp
#check @logSobolevAllToLp_ae_eq
#check @exists_logSobolevAllToLp_tendsto
#check @logSobolev_commonCompletion
#print axioms logSobolevWeight
#print axioms logSobolevMeasure
#print axioms integrable_logSobolevWeight_mul_norm_sq
#print axioms memLp_logSobolevMeasure
#print axioms logSobolevToLp
#print axioms logSobolevToLp_ae_eq
#print axioms logSobolevToLp_injective
#print axioms norm_logSobolevToLp
#print axioms logSobolevToLp_positiveIntegral
#print axioms logSobolevAllToLp
#print axioms logSobolevAllToLp_ae_eq
#print axioms exists_logSobolevAllToLp_tendsto
#print axioms logSobolev_commonCompletion

-- A closed interval need not contain zero. A singleton needs only one endpoint.
example (f : logWeightedProfiles (Icc (3 : ℝ) 3)) :
    Integrable (fun x : ℝ ↦ Real.exp (6 * x) * (1 + x ^ 2) ^ (-(1 : ℝ) / 2) * ‖f.1 x‖ ^ 2) := by
  have h := integrable_logSobolevWeight_mul_norm_sq (s := -1) (le_refl (3 : ℝ)) f.property
  norm_num [logSobolevWeight] at h ⊢
  exact h

-- Recover the printed squared-norm expression on a genuine two-ended interval.
example (f g : logWeightedProfiles (Icc (1 : ℝ) 2)) :
    let μ := (((volume : Measure ℝ).restrict ({0}ᶜ)).withDensity
      (fun t ↦ ENNReal.ofReal |t|⁻¹)).restrict (Ioi 0)
    ‖logSobolevToLp (by norm_num : (1 : ℝ) ≤ 2) 3 f -
        logSobolevToLp (by norm_num : (1 : ℝ) ≤ 2) 3 g‖ =
      Real.sqrt (∫ t, max (t ^ (2 : ℝ)) (t ^ (4 : ℝ)) *
        (1 + |Real.log t| ^ 2) ^ ((3 : ℝ) / 2) *
          ‖f.1 (Real.log t) - g.1 (Real.log t)‖ ^ 2 ∂μ) := by
  dsimp only
  rw [← map_sub]
  have h := (logSobolevToLp_positiveIntegral (by norm_num : (1 : ℝ) ≤ 2) 3 (f - g)).2
  norm_num at h ⊢
  simpa using h

-- Use the approximants to get compactly supported all-weight functions within ε.
example (a b s : ℝ) (hab : a ≤ b) (f : logWeightedProfiles (Icc a b)) (ε : ℝ) (hε : 0 < ε) :
    ∃ u : logWeightedProfiles univ, HasCompactSupport u.1 ∧
      dist (logSobolevAllToLp hab s u) (logSobolevToLp hab s f) < ε := by
  obtain ⟨u, hs, hu⟩ := exists_logSobolevAllToLp_tendsto hab s f
  obtain ⟨n, hn⟩ := (Metric.tendsto_atTop.mp hu ε hε)
  exact ⟨u n, hs n, hn n le_rfl⟩

-- Apply completeness on the interval image to the closure on the all-weight side.
example (a b s : ℝ) (hab : a ≤ b) :
    IsComplete (closure (range (logSobolevAllToLp hab s))) := by
  obtain ⟨heq, hc⟩ := logSobolev_commonCompletion hab s
  rwa [heq]
```
