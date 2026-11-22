# Radial Fréchet prerequisite for the weighted Schwartz LF claim

Passage `72132543387b6a142c4b542c851375de7d7ce2fb43c1df23ad2c1a0a49cf418b`,
revision `c2cf074414f1dc9129351343cc1f7f23d03067d4b6765e93493a178235369913`.
The Lean implementation was checked against base
`13312c6fecc55eac87813b997d87393863993235`. See the [receipt](72132543387b6a142c4b542c851375de7d7ce2fb43c1df23ad2c1a0a49cf418b-c2cf074414f1dc9129351343cc1f7f23d03067d4b6765e93493a178235369913.json)
for the assigned claim and remaining work.

## Source and scope

Edition: Masullo, *The Music of the Primes*, SHA-256
`e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5`.
The [pin](../sources/masullo/README.md) specifies the bytes, not merely the URL.
The page references below refer both to printed pages and one-based PDF ordinals.
The writer checked the local PDF digest and read page renders (using OCR to read
text on the renders; the extraction was a locator).

- **Printed claim.** Chapter 1, §1.1.2 fourth bullet, p. 11, says that under the
  preceding conditions the full space is strict LF, nuclear, complete and Montel.
  The preceding display (1.1.2.1) and surrounding text are important: for every
  weight \(a\) in the nonempty interval \(I\), the component of the stage map is
  \(\phi\mapsto |\cdot|_G^a\phi\); the stage has the induced product topology.
  The claim is for the locally convex inductive limit of such stages, not the
  uncountable product and not just the case of one radial stage. The bullet has
  no proof. Its applications to boundedness do not assert that every quotient
  of a nuclear space lifts bounded sets.
- **Printed proof route.** Definition D.2.1.1, display (D.2.1.3), p. 793 uses a
  proper module; the remark immediately following sketches splitting in the
  surjective setting. Section D.3.3, p. 804 assumes surjectivity and describes
  the product splitting with a chosen continuous homomorphic section; Theorem
  D.3.3.7, p. 806 explicitly includes that section in its hypothesis. The full
  proof of item (2), p. 810, uses Example D.3.3.5, pp. 805–806, for nuclear
  Fréchet stages and countable strictness, and cited permanence results.
  Example D.3.3.5 uses the continuous stage maps (D.3.3.2) on p. 805 and
  endpoint control on compact intervals, then countably many compact
  intervals, and inherits the unweighted transition embeddings. This proof
  route does not invoke item (1)'s stage tensor identification, whose issues
  are flagged separately in footnote 21 on p. 810.
- **Indexing discrepancy.** Definition D.3.3.3, p. 805, opens with compactly
  generated annihilator in the full dual but says *finitely* generated in its
  inductive-limit paragraph. The full annihilator contains the pulled-back
  radial dual, isomorphic to \(\mathbb R\): the module is surjective and trivial
  on every compact subgroup. Thus it cannot literally be finitely generated.
  As the discussion before Definition D.3.3.1, p. 804, explains, it is the
  annihilator in the *discrete dual of the compact norm-one kernel* that is to
  be finitely generated, equivalent to compact generation in the full dual.
- **Radial comparison.** Example D.3.3.4, p. 805, identifies the topology for
  the identity module on \(\mathbb R_{>0}\) with Definition D.3.2.1,
  (D.3.2.1), p. 801. The exponential-coordinate display just before
  Definition B.2.1.1, p. 593, identifies ordinary real-line Schwartz seminorms
  using \(x=\log t\) and \(t\partial_t=\partial_x\). The weight \(t^a\)
  becomes \(e^{ax}\). Proof of Lemma D.3.2.3(1), pp. 801–802, first uses
  compatibility to obtain a closed all-weight product image, then separates
  the two half-lines in the normalized range \(0\le c\le1\) to control an
  intermediate weight and countably reduce the topology. Remark D.3.2.4,
  p. 802, separately refers to nuclearity of the ordinary factors and its
  inheritance in products and subspaces.

## New proof and limitations

The implementation in
[`Theorems.RadialWeightedSchwartzFrechet`](../../Proofs/Theorems/RadialWeightedSchwartzFrechet.lean)
uses the existing `logWeightedStage I`, the range of the weighted linear map
into the product of actual `SchwartzMap ℝ ℂ` factors. On that range all
coordinates come from one smooth profile. Thus for any two weights
\(a,c\) one has the **global** identity \(F_c=e^{(c-a)x}F_a\). Leibniz gives
for \(a\le c\le b\), with \(p_{kn}\) the Schwartz seminorm,

\[
p_{kn}(F_c)\le
\sum_{j=0}^n\binom nj |c-a|^j p_{k,n-j}(F_a)+
\sum_{j=0}^n\binom nj |c-b|^j p_{k,n-j}(F_b).
\]

Indeed, use the differentiated identity with \(a\) on \(x\le0\) and with
\(b\) on \(x\ge0\); the selected exponential has norm at most one there.
The estimate has no profile-dependent constants and works for equal weights
or intervals missing zero. It addresses the topology of *existing* stage
profiles, not the separate forward existence assertion from endpoint data.

By the seminorm bound, convergence to zero in any bracketing subproduct
implies convergence in every original coordinate. The proof makes the
projection an additive uniform embedding for the original uniformity,
not just an injective function. A countable dense subset of the weight
subspace and its attained extrema suffice to bracket every weight: if a
weight is not the minimum, the open subset of weights strictly below it
meets the dense subset, and similarly at the top. This alternative to the
printed compact-interval exhaustion also works for arbitrary subsets of
\(\mathbb R\), including singletons. For empty \(I\) the metrizability
statement is about the empty-product range, not an identification with all
smooth profiles. Nonemptiness is assumed for the closed countable embedding
and when combining with the existing completeness theorem. The compatible
metric is obtained from countable generation of the *same* uniformity.
Real local convexity is the inherited one on this complex stage.

New endpoints in namespace `Masullo` (exact signatures are checked below):

| Endpoint | Hypotheses and conclusion |
| --- | --- |
| `logWeightedStage_seminorm_le_endpoints` | Weights `a c b : I` with `a ≤ c ≤ b`, indices `k n : ℕ`, and an actual stage tuple; the inequality above. |
| `isUniformEmbedding_logWeightedStage_restrict` | `J : Set I` brackets every `c : I`; coordinate restriction `F ↦ (fun j : J ↦ F.1 j.1)` is a uniform embedding. |
| `exists_countable_logWeightedStage_closedEmbedding` | `I.Nonempty`; some countable `J : Set I` gives a closed embedding by that same restriction. |
| `uniformity_logWeightedStage_isCountablyGenerated` | Any `I : Set ℝ`; the stage uniformity is countably generated. |
| `metrizableSpace_logWeightedStage` | Any `I : Set ℝ`; the inherited topology is metrizable. |
| `locallyConvexSpace_logWeightedStage` | Any `I : Set ℝ`; the complex stage is locally convex over `ℝ`. |

For `I.Nonempty`, `completeSpace_logWeightedStage` from
[`Theorems.RadialWeightedSchwartzStage`](../../Proofs/Theorems/RadialWeightedSchwartzStage.lean)
completes the radial Fréchet argument. This does **not** prove a nuclearity,
Montel, nonradial stage, transition strictness, cofinality or inductive-limit
result. The prior completeness proof does not itself give countable generation.
See the receipt's `retry` for a route to the remaining results.

## Replay the checks

In the candidate workspace, build the three relevant modules and extract
and check each of the following two ordinary-import Lean blocks:

```sh
lake build --wfail +Lemmas.SchwartzLineComplete +Theorems.RadialWeightedSchwartzStage +Theorems.RadialWeightedSchwartzFrechet
scratch=$(mktemp -d)
awk '/^```lean$/{n++; p=1;next} /^```$/{p=0} p{print > (d "/Check" n ".lean")}' \
  d="$scratch" .godel/formalize/radial-weighted-frechet.md
lake env lean "$scratch/Check1.lean" && lake env lean "$scratch/Check2.lean"
```

The writer build completed without warnings; all six new endpoints and the
existing completeness endpoint below depend only on `propext`,
`Classical.choice`, and `Quot.sound`. The second block applies the results
to the actual stage with positive, nonzero weights; it does not just import
or reprint the statements.

```lean
import Theorems.RadialWeightedSchwartzFrechet
#check @Masullo.logWeightedStage_seminorm_le_endpoints
#print axioms Masullo.logWeightedStage_seminorm_le_endpoints
#check @Masullo.isUniformEmbedding_logWeightedStage_restrict
#print axioms Masullo.isUniformEmbedding_logWeightedStage_restrict
#check @Masullo.exists_countable_logWeightedStage_closedEmbedding
#print axioms Masullo.exists_countable_logWeightedStage_closedEmbedding
#check @Masullo.uniformity_logWeightedStage_isCountablyGenerated
#print axioms Masullo.uniformity_logWeightedStage_isCountablyGenerated
#check @Masullo.metrizableSpace_logWeightedStage
#print axioms Masullo.metrizableSpace_logWeightedStage
#check @Masullo.locallyConvexSpace_logWeightedStage
#print axioms Masullo.locallyConvexSpace_logWeightedStage
#check @Masullo.completeSpace_logWeightedStage
#print axioms Masullo.completeSpace_logWeightedStage
```

```lean
import Theorems.RadialWeightedSchwartzFrechet

open Filter Masullo Set Topology
open scoped BigOperators SchwartzMap Topology Uniformity

local notation "K" => Set.Icc (1 : ℝ) 3

private def left : K := ⟨1, by norm_num⟩
private def middle : K := ⟨2, by norm_num⟩
private def right : K := ⟨3, by norm_num⟩

-- A derivative bound on an interval that does not contain zero.
example (F : logWeightedStage K) (k : ℕ) :
    SchwartzMap.seminorm ℂ k 1 (F.1 middle) ≤
      (SchwartzMap.seminorm ℂ k 1 (F.1 left) + SchwartzMap.seminorm ℂ k 0 (F.1 left)) +
      (SchwartzMap.seminorm ℂ k 1 (F.1 right) + SchwartzMap.seminorm ℂ k 0 (F.1 right)) := by
  have hl : left ≤ middle := by change (1 : ℝ) ≤ 2; norm_num
  have hr : middle ≤ right := by change (2 : ℝ) ≤ 3; norm_num
  have h := logWeightedStage_seminorm_le_endpoints hl hr k 1 F
  norm_num [left, middle, right, Finset.sum_range_succ] at h ⊢
  exact h

-- Convergence of the two endpoint coordinates implies convergence in the whole stage.
example {L : Filter (logWeightedStage K)} {F : logWeightedStage K}
    (h : Tendsto (fun (G : logWeightedStage K) (j : ({left, right} : Set K)) ↦ G.1 j.1)
      L (𝓝 (fun (j : ({left, right} : Set K)) ↦ F.1 j.1))) : Tendsto id L (𝓝 F) := by
  have hJ (c : K) : ∃ a b : ({left, right} : Set K), a.1 ≤ c ∧ c ≤ b.1 :=
    ⟨⟨left, by simp⟩, ⟨right, by simp⟩, c.2.1, c.2.2⟩
  exact (isUniformEmbedding_logWeightedStage_restrict hJ).isEmbedding.isInducing.tendsto_nhds_iff.2 h

-- For a nonempty open interval the closed range is in a countable product.
example :
    ∃ J : Set (Set.Ioo (1 : ℝ) 3), J.Countable ∧
      IsClosed (range (fun (F : logWeightedStage (Set.Ioo (1 : ℝ) 3)) (j : J) ↦ F.1 j.1)) := by
  obtain ⟨J, hJ, h⟩ := exists_countable_logWeightedStage_closedEmbedding
    (I := Set.Ioo (1 : ℝ) 3) ⟨2, by norm_num⟩
  exact ⟨J, hJ, h.isClosed_range⟩

-- At a nonzero singleton the original complete uniformity is induced by a metric.
example :
    ∃ m : MetricSpace (logWeightedStage ({(2 : ℝ)} : Set ℝ)),
      m.toUniformSpace = (inferInstance : UniformSpace (logWeightedStage ({(2 : ℝ)} : Set ℝ))) ∧
        @CompleteSpace _ m.toUniformSpace := by
  let := uniformity_logWeightedStage_isCountablyGenerated ({(2 : ℝ)} : Set ℝ)
  exact ⟨UniformSpace.metricSpace _, rfl, completeSpace_logWeightedStage ⟨2, by simp⟩⟩

example : FirstCountableTopology (logWeightedStage (Set.Ioo (1 : ℝ) 3)) := by
  let := metrizableSpace_logWeightedStage (Set.Ioo (1 : ℝ) 3)
  infer_instance

example (U : Set (logWeightedStage K)) (hU : U ∈ nhds 0) :
    ∃ V ∈ nhds (0 : logWeightedStage K), Convex ℝ V ∧ V ⊆ U :=
  let := locallyConvexSpace_logWeightedStage K
  (LocallyConvexSpace.convex_basis_zero ℝ (logWeightedStage K)).mem_iff.1 hU |>.imp
    fun _ ⟨⟨hm, hc⟩, hs⟩ ↦ ⟨hm, hc, hs⟩
```
