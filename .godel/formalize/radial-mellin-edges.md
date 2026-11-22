# The radial two-edge Mellin seminorms

Passage `58469615efdbe7e33adee9fe3aa2d6d79d5efa230a561354c926c7dffbbb34ba`, revision
`c43d404f6e8e356bfae391287d8802991fb1da30df617d0f834407a282e9ecd4`.
Writer base `a3d043374c9100cb74a3da3b70caf679d74de556`.
Owning Yah check/review session: `01a20517-597e-7d5f-8b44-81b6684debda`.
The checks below are writer-workspace checks. The owning session records
exact-integrated checks and independent review, including the full candidate
and base IDs, check results, and reviewer verdict.
[Receipt](58469615efdbe7e33adee9fe3aa2d6d79d5efa230a561354c926c7dffbbb34ba-c43d404f6e8e356bfae391287d8802991fb1da30df617d0f834407a282e9ecd4.json).

## Printed scope and the compact character

The writer verified the PDF bytes against the [edition pin](../sources/masullo/README.md),
SHA-256 `e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5`, located
text with layout extraction, and checked rendered pages, including tight pixel
crops for the derivative range, measures and transform displays. Printed page
numbers equal the one-based PDF ordinals at the locators below.

- **Claim, not proof:** Chapter 1, §1.1.3, p. 11 and the unnumbered edge
  display and following sentence on p. 12. The carried-over setting is
  a second-countable Hausdorff locally compact abelian \(\mathbb R_{>0}\)-modulated
  \(G\), fixed Haar measure, \(I=[a,b]\), \(a<b\); the completion of
  \(S_E(G)\) is in the weighted norm of p. 11. The edge display says that the
  seminorms \(\|\partial_z^k M(\phi)(z)\|_{L^2(\alpha+i\mathbb R,dx)}\)
  generate its topology for \(\alpha=a,b\) and \(0\le k\le s/2\) with
  \(s\) even. It shows neither an isotype restriction nor a compact-dual norm.
- **Contextual vector reading:** p. 403, (9.2.0.1) and the unnumbered integral
  following the identification of \(c\) with \((s,\omega)\); p. 416, the
  unnumbered \(M(\phi)((s,\omega))\) integral before Definition 9.2.2.9.
  Both integrals label the output by \(\omega\) but omit its factor from the
  inner integration over \(G^1\). The former explicitly says the map is a
  compact Fourier transform tensored with the radial Mellin transform. The
  latter includes a choice of unitary base point, and a radial factor
  \(t^{ix_0(\chi)+s}\); an ordinate shift does not replace the compact factor.
  The actual full transform is \(c\mapsto\int_G\phi(g)c(g)\,d\mu(g)\) in
  Theorem D.3.3.13, p. 812, with the inversion-twisted compact Fourier
  factor in (D.3.3.12) and explicit \(c(\tau(t)g^1)\) in (D.3.3.13), p. 813.
  Thus the compact character is not optional under that convention.
- **Later norms:** Lemma 9.2.2.10(1), pp. 416–417, (9.2.2.32)–(9.2.2.33),
  prints the \(L^2(\widehat{G^1},\widehat{\mu}_1)\) tensor factor in both
  targets; \(\mu_1\) is the probability Haar measure on \(G^1\), not the
  dual measure. Its ensuing topology description says “finitely many” but
  ranges over countably many lines with finite boundary points as limit
  points. That is not a statement of uniform endpoint control. Part (2),
  p. 417 (9.2.2.34), gives the weighted maximum, in the canonical Haar
  measure of Definition 9.2.2.9, p. 416. Definition D.2.1.1 and Remarks
  D.2.1.2–3, p. 793, identify the compact kernel, claim a continuous
  homomorphic section, and describe probability Haar on the kernel times
  \(dt/t\) in the surjective case.

**Counterexample to scalar collapse, not to the vector reading.** Let
\(G=\mathbb R_{>0}\times C_2\), \(|(t,\epsilon)|_G=t\), with product Haar
\(dt/t\) times probability on \(C_2=\{1,-1\}\). This is a proper surjective
module and the product has the displayed continuous section \(t\mapsto(t,1)\).
For a nonzero \(f\in C_c^\infty(\mathbb R)\), set
\(\phi(t,\epsilon)=\epsilon f(\log t)\). The trivial subgroup is an
admissible elementary stage: the full annihilator is the compactly generated
\(\mathbb R\times\widehat{C_2}\) (the compact-factor dual is finite), and each
radial weight gives a finite tuple of smooth compactly supported functions in
the log coordinate. This checks the all-weight condition of §1.1.2,
(1.1.2.1) and following bullet, p. 11, and the stage in Lemma D.3.3.2,
p. 804 and Definition D.3.3.3, p. 805, (D.3.3.1)–(D.3.3.2).
The latter begins with *compactly* generated orthogonals, as do p. 11
and Lemma D.3.3.2; its subsequent “finitely generated” would exclude
this stage and even the full radial dual, contrary to Example D.3.3.4.
The scalar integral with \(|g|_G^z\) and every derivative vanish since
\(\frac12(1-1)=0\). The weighted norm is strictly positive because
\(|\epsilon|^2=1\), the weight is positive, and \(f\) is continuous and
nonzero on an open set. In the full transform, the nontrivial character
\(\epsilon\mapsto\epsilon\) instead multiplies the integrand by a second
\(\epsilon\): that coefficient is the radial Mellin transform of \(f\),
which is nonzero in \(L^2\) on each edge by radial Plancherel. This
witness is a source audit, not a separate Lean endpoint.

## Corrected radial identity and implementation

For the identity module on \(G=\mathbb R_{>0}\) and \(dt/t\), write
\(f(x)=\phi(e^x)\). Proposition D.3.2.5, p. 802, (D.3.2.2) and the
integral defining its map use \(t^z\), no prefactor. Thus
\(M_f(z)=\int f(x)e^{zx}\,dx\). At \(z=\alpha+iu\) the tilt is
\(e^{\alpha x}\) on **both** edges, with a different value of \(\alpha\).
The actual complex derivative under the integral has multiplier \(x^k\),
not \((ix)^k\). The latter differentiates in the ordinate \(u\), so the
ordinate derivative is \(i^k\partial_z^k M_f(\alpha+iu)\). Equivalently,
for the rotated convention \(F(w)=M_f(iw)=\int f(x)e^{iw x}\,dx\),
\(w=u+iv\) has tilt \(e^{-vx}\), the edge is \(v=-\alpha\), and
\(F^{(k)}(w)=i^k M_f^{(k)}(iw)\). The unit factor does not affect the norm.

With the unscaled integral and the \(e^{-2\pi i x\xi}\) Fourier kernel,
\(M_f^{(k)}(\alpha+iu)=\widehat{[x^k e^{\alpha x}f]}(-u/(2\pi))\).
The negative sign is from the kernel; \(d\xi\) changes to positive
\(du/(2\pi)\) as a measure. In particular,

\[
  \int |M_f^{(k)}(\alpha+iu)|^2\,du
   = 2\pi\int e^{2\alpha x}|x|^{2k}|f(x)|^2\,dx .
\]

This is the correction to p. 413 (9.2.2.17), where Plancherel is invoked
for equality of norms with no \(\sqrt{2\pi}\). The measure in (9.2.2.5),
p. 412, is \(|dz|\), ordinary ordinate measure, agreeing with the
literal \(dx\) in the p. 12 edge display in that coordinate. One can instead
make (9.2.2.17) exact with normalized ordinate measure. The constant has
no effect on topology. The argument does not assume the literal preliminary
weight comparisons in (9.2.2.12)–(9.2.2.16), p. 413.

For \(s=2n\), \(n\in\mathbb N\) (the nonnegative range of Lemma 9.2.2.2,
p. 412, and Lemma 9.2.2.10, p. 416), write \(E_{\alpha,k}\) for the ordinate integral divided
by \(2\pi\). Then \(\sum_{k=0}^n {n\choose k}E_{\alpha,k}\) equals the
right-hand integral of (9.2.2.18) **before** its square root, with weight
\(e^{2\alpha x}(1+x^2)^n\). The ordinary sum of the printed, unweighted
squared seminorms after normalization is \(S=\sum_{k=0}^n(E_{a,k}+E_{b,k})\).
If \(W\) is the square of the p. 11 norm, the binomial two-edge sum \(B\)
satisfies \(W\le B\le2W\) by max versus sum of two positive endpoint
weights. Since \(1\le{n\choose k}\le2^n\), one gets
\(W\le2^n S\) and \(S\le2W\), equivalence rather than isometry. The
case \(n=0\) keeps the zeroth derivative; the Lean bounds also work when
\(a=b\) (the sum then uses two copies of the same edge).

[Theorems.RadialMellinEdges](../../Proofs/Theorems/RadialMellinEdges.lean)
uses the accepted `Masullo.logWeightedProfiles univ`, whose underlying
functions are smooth and each real exponential twist is an actual Schwartz
function. The two further twists at \(\operatorname{Re}z\pm3\) bound each
moment at \(z\) by a constant times \(e^{-3|x|}\), separately on the
two half-lines. The accepted `Masullo.hasDerivAt_logMellin_of_decay`
provides the dominated differentiation step; iterating for all moments
proves the assertion for the actual `iteratedDeriv`, without making a
derivative hypothesis. Schwartz Plancherel applies to the moment and the
ordinate change of variables gives both actual integrability and equality.

| `Masullo` endpoint | Content |
|---|---|
| `logMellin` | Positive-sign Mellin integral for an all-weight radial profile. |
| `iteratedDeriv_logMellin` | Integrable moment and derivative equality, any \(k\in\mathbb N\), \(z\in\mathbb C\). |
| `logMellin_edge_parseval` | Integrability and raw-ordinate Parseval for the actual squared derivative, any real line and any \(k\). |
| `logMellinEdgeEnergy` | That squared ordinate integral divided by \(2\pi\). |
| `sum_choose_logMellinEdgeEnergy` | Exact weighted one-line equality over `Finset.range (n+1)`. |
| `logMellin_edgeEnergy_equivalent` | Two-sided squared-norm estimates with the accepted `logSobolevAllToLp hab (2*n)` for `hab : a ≤ b`. |
| `logMellinCompletion` | Topological closure of the range of that weighted image inside the same weighted `Lp`. |
| `exists_logMellin_edgeTrace` | For `hab : a ≤ b`, `c = a ∨ c = b`, `k ≤ n`, a contractive complex continuous linear map from this closure to `Lp ℂ 2 volume`. On the actual test image it equals `iteratedDeriv k (logMellin f)` at the point `c + (-2πξ)*I` almost everywhere in frequency coordinate `ξ`. |

The completion here is the accepted weighted-image closure, using
[`logSobolev_commonCompletion`](radial-hardy-sobolev-completion.md) for
the prior common completion of all-weight and closed-interval tests.
On the dense all-weight image, the trace is the Fourier Schwartz-to-`Lp`
map on the appropriate moment; the pointwise weight bound at \(k\le n\)
gives contractivity and the continuous extension is obtained with
`LinearMap.extendOfNorm`. The norm equivalence is stated on tests; the
trace theorem gives actual maps on the closure, not pointwise edge values
of arbitrary representatives or a theorem on their interior limits.
In particular, the [accepted interior-line counterexample][interior]
uses a sequence of cutoffs of a smooth tail at \(I=[-1,1],s=2\): the
sequence is Cauchy on each strictly interior vertical line, but the limit
has a non-\(L^2\) right-edge singularity. This obstruction is not removed
by calling an interior-line completion a weighted completion.

## Residual obligation

For the full vector formulation, with a verified or supplied homomorphic
section, realize the Fourier–Mellin integral on the actual modulated
Schwartz–Bruhat tests and prove the Plancherel bridge on
\((\mathbb R,du/(2\pi))\times(\widehat{G^1},\widehat{\mu}_1)\):
the squared edge norm must integrate \(|\phi(g)|^2 |g|_G^{2\alpha}
|\log |g|_G|^{2k}\) in the matching Haar measure. Then the binomial and
max-versus-sum comparisons give the full norm estimates, and boundedness
on the actual weighted test image is the input for extending the vector
edge maps. The fixed-Haar scaling in §1.1.3 must also be tracked if it is
not the canonical Haar measure. `continuousMulEquivOfSection` and the
conditional Haar splitting in `Lemmas.HaarLogSplit` are not this transform
identity or the existence of a section for every group. Neither the full
vector result nor a replacement for the interior-line isomorphism in
(9.2.2.33) is claimed here.

[interior]: ../obligations/boundary-trace-interior-lines.md

## Reproduce the writer checks

Pinned toolchain `leanprover/lean4:v4.36.0`; mathlib manifest revision
`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. On the writer workspace the
warning-failing build below succeeded (6491 jobs), and the ordinary-import
scratch client succeeded on the same Lean source. All eight declarations'
transitive reports were exactly `propext`, `Classical.choice`, `Quot.sound`.
The last example constructs the embedded test input, extracts an edge map,
and applies it to obtain both the norm bound and a.e. derivative identity.
To repeat in the exact candidate workspace:

```sh
lake build --wfail +Theorems.RadialMellinEdges
probe=$(mktemp /tmp/grh-mellin-edge-client-XXXXXX.lean)
sed -n '/^```lean$/,/^```$/{ /^```/d; p; }' .godel/formalize/radial-mellin-edges.md > "$probe"
lake env lean "$probe"
```

```lean
import Theorems.RadialMellinEdges
import Theorems.RadialHardySobolevCompletion

open MeasureTheory Set Masullo
open scoped Topology

#check @Masullo.logMellin
#check @Masullo.iteratedDeriv_logMellin
#check @Masullo.logMellin_edge_parseval
#check @Masullo.logMellinEdgeEnergy
#check @Masullo.sum_choose_logMellinEdgeEnergy
#check @Masullo.logMellin_edgeEnergy_equivalent
#check @Masullo.logMellinCompletion
set_option pp.funBinderTypes true in
#check @Masullo.exists_logMellin_edgeTrace
#print axioms Masullo.logMellin
#print axioms Masullo.iteratedDeriv_logMellin
#print axioms Masullo.logMellin_edge_parseval
#print axioms Masullo.logMellinEdgeEnergy
#print axioms Masullo.sum_choose_logMellinEdgeEnergy
#print axioms Masullo.logMellin_edgeEnergy_equivalent
#print axioms Masullo.logMellinCompletion
#print axioms Masullo.exists_logMellin_edgeTrace

-- Apply order-one differentiation at a point with nonzero real part.
example (f : logWeightedProfiles univ) :
    deriv (logMellin f) (1 + Complex.I) =
      ∫ x : ℝ, (x : ℂ) * f.1 x * Complex.exp ((1 + Complex.I) * x) := by
  simpa using (iteratedDeriv_logMellin f 1 (1 + Complex.I)).2

-- Recover the raw right-edge ordinate integral at order zero.
example (f : logWeightedProfiles univ) :
    (∫ u : ℝ, ‖logMellin f ((1 : ℂ) + (u : ℂ) * Complex.I)‖ ^ 2) =
      2 * Real.pi * (∫ x : ℝ, Real.exp (2 * x) * ‖f.1 x‖ ^ 2) := by
  simpa using (logMellin_edge_parseval f 1 0).2

-- Expanding the binomial at degree four gives the coefficient two at order one.
example (f : logWeightedProfiles univ) :
    logMellinEdgeEnergy f 1 0 + 2 * logMellinEdgeEnergy f 1 1 +
      logMellinEdgeEnergy f 1 2 = ∫ x : ℝ, Real.exp (2 * x) * (1 + x ^ 2) ^ 2 * ‖f.1 x‖ ^ 2 := by
  simpa [Finset.sum_range_succ, Nat.choose] using sum_choose_logMellinEdgeEnergy f 1 2

-- The first two energies at each endpoint control the degree-two weighted norm.
example (f : logWeightedProfiles univ) (a b : ℝ) (hab : a ≤ b) :
    ‖logSobolevAllToLp hab 2 f‖ ^ 2 ≤
      2 * ((logMellinEdgeEnergy f a 0 + logMellinEdgeEnergy f b 0) +
        (logMellinEdgeEnergy f a 1 + logMellinEdgeEnergy f b 1)) := by
  have h := (logMellin_edgeEnergy_equivalent hab 1 f).1
  have hd : (2 : ℝ) * ((1 : ℕ) : ℝ) = 2 := by norm_num
  have hdeg := congrArg (fun d : ℝ ↦ ‖logSobolevAllToLp hab d f‖ ^ 2) hd
  rw [hdeg] at h
  simpa only [pow_one, Finset.sum_range_succ, Finset.sum_range_zero, zero_add] using h

-- Embed an actual test profile and apply the contractive right-edge trace.
example (f : logWeightedProfiles univ) (a b : ℝ) (hab : a ≤ b) :
    ∃ v : Lp ℂ 2 (volume : Measure ℝ),
      ‖v‖ ≤ ‖logSobolevAllToLp hab (2 * ((1 : ℕ) : ℝ)) f‖ ∧
      (v : ℝ → ℂ) =ᵐ[volume] fun ξ ↦
        deriv (logMellin f) ((b : ℂ) + ((-(2 * Real.pi) * ξ : ℝ) : ℂ) * Complex.I) := by
  let Y : logMellinCompletion hab 1 :=
    ⟨logSobolevAllToLp hab (2 * ((1 : ℕ) : ℝ)) f, subset_closure ⟨f, rfl⟩⟩
  obtain ⟨T, hT, hTest⟩ := exists_logMellin_edgeTrace hab (Or.inr rfl : b = a ∨ b = b) 1 1 le_rfl
  exact ⟨T Y, hT Y, by simpa only [iteratedDeriv_one] using hTest f Y rfl⟩
```
