# Single-place adelic norm

**Status: Accepted Lean declaration at `86e7bc6226470fa02a846bcee274758402491e09`.** This is a project lemma for the [finite-place support repair](trace-geometric.md#narrowing-the-bridge-project-reasoning-not-a-source-reading), not a claim newly transcribed from Masullo. It is the first algebraic input to comparing the finite-place terms on PDF pp. 514 and 520 of the [pinned edition](../sources/masullo/README.md). It says nothing about the orbital tail, the cutoff limit, or the Mellin corrections.

For a number field $K$, the single-place idele attached to $u\in K_v^\times$ has adelic norm $|u|_v$. All infinite coordinates and finite coordinates away from $v$ are one. The finite product has at most one nontrivial factor, so the argument also works when $|u|_v=1$.

The proof is in [`Lemmas.SinglePlaceNorm`](../../Proofs/Lemmas/SinglePlaceNorm.lean), as `Masullo.norm_idele_ofAdicCompletion`.

The independent Yah review found no definite API mismatch in the draft at Mathlib `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. In particular, `AdeleRing.ofAdicCompletion` uses the constant-one map at infinity, and `FiniteAdeleRing.ofAdicCompletion` uses `RestrictedProduct.mulSingleMonoidHom` with `Classical.decEq`. The review checked the direction of `w ≠ v` and that `finprod_eq_single` needs no assumption about the value at `v`. The draft uses the review's suggested explicit index type for the family `A`.

The [idele-class support lemma](finite-place-support.md) uses this result to evaluate the descended norm on a single-place class.

## Archimedean log section on ideles and classes

[`Theorems.IdeleLogSection`](../../Proofs/Theorems/IdeleLogSection.lean)
implements Definition A.2.2.5, (A.2.2.10), and Lemma A.2.2.6, PDF p. 547,
on the actual ideles. At any specified infinite place $v$, it inserts
$\exp(x/v.\mathrm{mult})$ into $K_v^\times$ and leaves every other coordinate
one. The statement uses $x\in\mathbb R$ in multiplicative notation, so
$t=\exp x$ is the manuscript's positive radial variable. At a complex
place the local norm is the square of the ordinary complex absolute
value. The project follows the root in the definition and in the
proof's complex case, rather than the intermediate equality on p. 547
that writes the insertion with $t$ and no root.

The continuity proof uses the real and complex isometries of the
completion to put that positive real scalar in the chosen place. The
norm calculation keeps just that place in the product and cancels the
multiplicity. The class-level section is the composition with the
quotient map; `ideleClassNorm_mk` gives its norm law, as required in
(A.1.3.6), p. 542. No compactness, class group topology beyond what the
section uses, or Haar normalization is established here. The locators
were checked in pinned Markdown and numbered PDF layout, not on rendered
pages; the readings are provisional.

Independent Yah statement review: Session
`01a20275-afc8-7bdd-b643-280835b8b1ff`, child `review-section`
(agent `gnKPebv`, read-only output `85984ffbc5104228f714d29c02ed749556a39092`).
The review confirmed the arbitrary infinite place, both coordinate
formulas, the ordinary complex norm squared, the quotient by principal
ideles, and the logarithmic reparameterization. The signatures express
sections in that reparameterization, not a new isomorphism API for
$\mathbb R_{>0}$.

```sh
go run ./cmd/godel audit-local "$CANDIDATE" \
  Lemmas.ArchimedeanLogRadius Theorems.IdeleLogSection -- \
  Masullo.ideleLogSection Masullo.ideleLogSection_infinite \
  Masullo.ideleLogSection_finite Masullo.ideleNorm_ideleLogSection \
  Masullo.ideleClassLogSection Masullo.ideleClassLogSection_apply \
  Masullo.ideleClassNorm_logSection
```

## Log-norm product splittings

[`Theorems.IdeleLogSplit`](../../Proofs/Theorems/IdeleLogSplit.lean)
gives a continuous multiplicative equivalence
$(\mathbb R \times G^1) \simeq G$ for actual ideles and idele classes
of every number field. Here the first factor is the additive log radius,
viewed as `Multiplicative ℝ`, and $G^1$ is the subgroup where the positive
norm is one. The formulas are $(x,k)\mapsto s(x)k$ and
$g\mapsto(n(g),s(n(g))^{-1}g)$, where $n$ is the log norm. The right-inverse
law for $s$ puts the second inverse coordinate in $G^1$. The equivalence
is instantiated by the sections at any infinite place. On those products
the quotient map to classes acts on the norm-one coordinate and preserves
the log radius, as checked by `ideleClassLogSplit_mk`.

Masullo gives the multiplication formula in Lemma A.2.2.9, (A.2.2.12),
PDF p. 547. The literal hypothesis of continuity alone gives a homeomorphism,
not a group isomorphism: Restricting to $(x,1)$ recovers $s$ itself. The
Lean equivalence explicitly requires the section to be homomorphic, as in
Lemma A.2.2.6, p. 547, and §A.3.3.1, p. 561. The class-level statements use
the norm descent of (A.1.3.6) and the map in (A.1.4.3), p. 542. The
commuting square does not itself prove strict exactness or compactness.
These readings are provisional: Pinned Markdown and numbered PDF layout,
not rendered pages.

Independent Yah review, session `01a2027a-7a02-74cb-918f-2b3bfb3310df`:
`review-split-control` (`kaNwokQ`, read-only output
`4ffe31e0eadc15d4e874f0bb2257d86a54aea2c9`) checked the idelic splitting,
the repair to the section hypothesis, and both maps. The general norm
law formerly named `ideleNorm_logSection` is renamed, with its signature
unchanged, so the general and rational modules can be imported together.

```sh
go run ./cmd/godel audit-local "$CANDIDATE" \
  Lemmas.ContinuousNormSplit Theorems.IdeleLogSection Theorems.IdeleLogSplit \
  Theorems.RationalIdeleLogSection -- \
  Masullo.ideleNorm_ideleLogSection Masullo.ideleNorm_logSection \
  Masullo.ideleClassLogNorm Masullo.ideleClassLogNorm_apply \
  Masullo.ideleLogNorm Masullo.ideleLogNorm_apply Masullo.ideleClassLogNorm_mk \
  Masullo.ideleNormOne Masullo.ideleClassNormOne \
  Masullo.mem_ideleNormOne Masullo.mem_ideleClassNormOne \
  Masullo.ideleLogSplit Masullo.ideleLogSplit_apply Masullo.ideleLogSplit_symm \
  Masullo.ideleClassLogSplit Masullo.ideleClassLogSplit_apply Masullo.ideleClassLogSplit_symm \
  Masullo.ideleLogNorm_section Masullo.ideleClassLogNorm_section Masullo.ideleClassLogSplit_mk
```

## Fractional ideal of a finite idele

[`Theorems.FiniteIdeleIdeal`](../../Proofs/Theorems/FiniteIdeleIdeal.lean)
constructs the algebraic map before the principal quotient in Proposition
A.2.3.9, (A.2.3.23), PDF p. 552. Masullo states the strict exact sequence
and invokes the classical quotient description in §A.1.5, pp. 544–545;
the manuscript does not give the fractional-ideal lift used here. The
lift is a project proof, not a claim of strict exactness in Lean.

`finiteIdeleIdeal` sends a finite idele to the product of fractional
prime powers. The exponent at $v$ is the negative of the logarithm
in Mathlib's value monoid $\mathbb Z^{\mathrm{m},0}$: A uniformizer has
value $\exp(-1)$ in this monoid and gives exponent $+1$. A finite idele
and its inverse have integral coordinates away from finitely many places,
so only finitely many exponents are nonzero. Unique factorization proves
the exponent law and multiplicativity. The field and local valuations
agree on diagonal coordinates; writing the diagonal element as a quotient
of integers then gives its principal fractional ideal. To lift any
fractional ideal, prescribe its finitely supported exponents by local
valuation surjectivity, and take the resulting finite idele. The kernel
before quotienting is the all-valuation-one condition, equivalently an
integral unit at each place. These source readings are provisional:
Pinned Markdown and numbered PDF layout, without visual verification.

Independent Yah statement review: Session
`01a2028c-784f-7239-86c7-e9cadd56ef88`, child `review-finite-ideal`
(`mDkPtHS`). It checked the sign against the uniformizer, the exact
five endpoints for arbitrary number fields, and the distinction between
the finite-idele lift and the manuscript's strict exact sequence.

```sh
go run ./cmd/godel audit-local "$CANDIDATE" \
  Lemmas.FiniteIdeleIdealCoordinates Theorems.FiniteIdeleIdeal -- \
  Masullo.finiteIdeleIdeal Masullo.count_finiteIdeleIdeal \
  Masullo.finiteIdeleIdeal_unitEmbedding Masullo.finiteIdeleIdeal_eq_one_iff \
  Masullo.finiteIdeleIdeal_surjective
```

## The ideal class of an idele

[`Theorems.IdeleIdealClass`](../../Proofs/Theorems/IdeleIdealClass.lean)
proves algebraic exactness in (A.2.3.23) and (A.2.3.24), PDF p. 552,
for every number field. Masullo states the strict sequences and recalls the
classical restricted-product quotient in §A.1.5.3, pp. 544–545. The project
constructs the arrow as the composite of the finite projection, the checked
fractional-ideal map, and `ClassGroup.mk K`. A trivial ideal class means the
finite ideal is principal, so cancelling its diagonal generator leaves an
idele with integral units at every finite place. Conversely such a product
has principal finite ideal. Surjectivity uses a finite-idele lift of each
nonzero fractional ideal, with infinite part one.

For the norm-one kernel, the product formula keeps the remaining factor
of norm one after cancelling the diagonal. On the integral-unit subgroup
the norm is the normalized Archimedean product, as shown by
`ideleNorm_of_mem_ideleFiniteUnits`. For surjectivity, multiplying by the
inverse of the checked single-place section at the log norm gives a
norm-one representative with the same finite part. This uses (A.2.2.10),
p. 547, and supplies the representatives in (A.2.3.12), p. 549. The map
also descends to actual idele classes. Its restriction to norm-one classes
is surjective and has kernel the **image** of the norm-one ideles with
integral finite units, not that subgroup itself.

Independent Yah statement and source review: Session
`01a20292-6f1d-701f-ba87-a23ec8386e8d`, child `review-class-map`
(`UkOYlNL`, read-only output `2ff77f980cd5055ce68c290c4310833ed5ba465c`).
Both readers used pinned Markdown and numbered PDF layout, not rendered
pages. The source readings remain provisional.

```sh
go run ./cmd/godel audit-local "$CANDIDATE" Theorems.IdeleIdealClass -- \
  Masullo.ideleFinitePart Masullo.ideleFiniteUnits Masullo.mem_ideleFiniteUnits \
  Masullo.ideleNorm_of_mem_ideleFiniteUnits Masullo.ideleIdealClass \
  Masullo.ideleIdealClass_apply Masullo.ideleIdealClass_diagonal \
  Masullo.ideleIdealClass_eq_one_iff Masullo.ideleIdealClass_surjective \
  Masullo.ideleIdealClass_normOne_eq_one_iff Masullo.ideleIdealClass_normOne_surjective \
  Masullo.ideleClassIdealClass Masullo.ideleClassIdealClass_mk \
  Masullo.ideleClassIdealClass_surjective Masullo.ideleClassIdealClass_normOne_surjective \
  Masullo.ideleClassIdealClass_normOne_eq_one_iff
```

The topological step is now in [Strict exactness of the ideal-class sequences](#strict-exactness-of-the-ideal-class-sequences).

## Strict exactness of the ideal-class sequences

[`Theorems.IdeleIdealClassStrict`](../../Proofs/Theorems/IdeleIdealClassStrict.lean)
proves (A.2.3.23) and (A.2.3.24) of Proposition A.2.3.9, PDF p. 552.
Masullo states strict exactness and recalls the restricted-product quotient in
§A.1.5.3, pp. 544–545. `Theorems.IdeleIdealClass` supplies the placewise
construction, the kernel descriptions, and the two surjections. The project
supplies the topology as follows: `range_ideleFiniteStageEmbedding_empty`
identifies the finite-integral-unit subgroup with the empty open stage of
Lemma A.1.3.3, p. 541. For a local coordinate and its inverse, the two
valuations multiply to one, so both are at most one exactly when both equal
one. The containing ideal-class kernel is then open, and the norm-one
kernel is its preimage under the subgroup inclusion. An open kernel gives
continuity to the discrete class group, and discreteness also makes both
surjections open. The left arrows are the inclusions of the algebraically
identified kernels with their induced topologies, and are closed embeddings.
The ideles are locally compact by the compact calibration box with nonempty
interior; the norm-one ideles are closed therein. These source readings are
provisional: Pinned Markdown and numbered PDF layout, not rendered pages.
Independent Yah statement review: Session
`01a2029d-7302-7bdc-8eca-a95b34f7c42e`, child `review-strict-ideal`.

```sh
go run ./cmd/godel audit-local "$CANDIDATE" Theorems.IdeleIdealClassStrict -- \
  Masullo.topologicalSpace_idealClassGroup Masullo.discreteTopology_idealClassGroup \
  Masullo.locallyCompact_ideleGroup Masullo.locallyCompact_ideleNormOne \
  Masullo.range_ideleFiniteStageEmbedding_empty Masullo.ideleIdealClassNormOne \
  Masullo.ideleIdealClassNormOne_apply Masullo.ideleIdealClass_strictExact \
  Masullo.ideleIdealClassNormOne_strictExact
```

## Hausdorff idele classes

[`Theorems.IdeleClassSeparation`](../../Proofs/Theorems/IdeleClassSeparation.lean)
proves the discreteness and closedness of the principal ideles in the
induced idelic topology, and the Hausdorff assertion for their actual
quotient, for every number field. These are the separation assertions
of Lemma A.1.3.4(1)–(2), PDF p. 542. The project supplies the open
identity neighborhood: Intersect the empty stage of Lemma A.1.3.3,
p. 541, with the strict Archimedean product bound for the difference
from one. For a principal idele of a field element other than one,
its nonzero difference has finite factors at most one by the
valuation inequality and Archimedean product less than one by the
window. This contradicts the product formula for the norm of
(A.1.3.3), p. 541. Hence the principal subgroup is discrete, then
closed in the Hausdorff ideles. In particular the actual norm-one
subtype of the quotient is Hausdorff, independently of compactness.
The source readings are provisional (pinned Markdown and numbered PDF
layout, not rendered pages). Independent Yah statement review:
Session `01a202a6-4063-74b7-99da-31335e5b3f4f`, child
`review-compactness` (`gRumDYP`).

```sh
go run ./cmd/godel audit-local "$CANDIDATE" Theorems.IdeleClassSeparation -- \
  Masullo.discreteTopology_principalIdeles Masullo.isClosed_principalIdeles \
  Masullo.t2Space_ideleClassGroup
```

## Compact Hausdorff norm-one classes

[`Theorems.IdeleClassCompactHausdorff`](../../Proofs/Theorems/IdeleClassCompactHausdorff.lean)
proves Theorem A.1.4.3(1), PDF p. 542: For every number field, the norm-one
subgroup of the actual idele class group is compact Hausdorff in its
induced topology. There is no compact-cover hypothesis at this endpoint.
The subgroup is the kernel of the continuous class log norm in
`Theorems.IdeleLogSplit`, so it is closed independently of compactness.

* `archimedean_compact_cover` follows the weighted log coordinates and
  lattice reduction (A.2.3.3)–(A.2.3.10), pp. 548–549. To obtain the
  compact-cover consequence of Lemma A.2.3.8(1)–(2), pp. 550–551, the
  project takes the **closed** log window and keeps the entire angular
  fiber. `isCompact_preimage_archimedeanDroppedLog` supplies the required
  compactness in the units topology, rather than assuming properness:
  Restore the omitted log by the zero-sum relation and bound both the
  value and the inverse at each place.
* `compactSpace_ideleClassNormOne_of_archimedean_cover` implements the
  finite union (A.2.3.14), p. 549, and the coverage step of Proposition
  A.2.3.10(1)–(2), p. 552, using the compact empty-stage finite-unit block.
  The kernel step (A.2.3.28) leaves a **norm-one** residual after removing
  the norm-one class lift and a principal idele. The Archimedean unit
  correction preserves the finite integral-unit stage. The quotient image
  of the finite union is exactly the norm-one class subgroup.
* The endpoint erases the Archimedean subtype by continuous inclusion,
  matches the two embeddings of an integral unit, and uses
  `t2Space_ideleClassGroup` for the Hausdorff part.

Independent Yah statement review: Session
`01a202a6-4063-74b7-99da-31335e5b3f4f`, children `review-compactness`
(`gRumDYP`) and `review-full-compact` (`hzrzCgv`, read-only output
`e1852db3a62de62ce132c5902c92bbd7a048ffeb`). Source readings are
provisional: Pinned Markdown and numbered PDF layout, not rendered pages.

```sh
go run ./cmd/godel audit-local "$CANDIDATE" \
  Lemmas.IdeleArchimedeanCover Theorems.IdeleArchimedeanCover \
  Theorems.IdeleClassCompact Theorems.IdeleClassCompactHausdorff -- \
  Masullo.archimedeanNorm Masullo.archimedeanNorm_apply \
  Masullo.archimedeanNormOne Masullo.mem_archimedeanNormOne \
  Masullo.archimedeanDiagonalUnit Masullo.coe_archimedeanDiagonalUnit \
  Masullo.archimedeanDroppedLog Masullo.archimedeanDroppedLog_apply \
  Masullo.archimedeanDroppedLog_diagonalUnit Masullo.archimedeanDroppedLog_inv_mul \
  Masullo.isCompact_preimage_archimedeanDroppedLog Masullo.archimedean_compact_cover \
  Masullo.ideleInfinitePart Masullo.ideleInfinitePart_integralUnit \
  Masullo.compactSpace_ideleClassNormOne_of_archimedean_cover \
  Masullo.compactHausdorff_ideleClassNormOne
```

## Checked complex log-polar Haar

The compact cover is not a disjoint fundamental domain and gives no Haar
mass. Definition A.3.2.1, pp. 559–560, prescribes the quotient volume, and
Lemma A.3.2.4, p. 560, identifies the same measure with the restricted
product by citation. §A.3.3.1, p. 561, uses the prescribed volume in the
strip mass, not as an independent calculation. The outstanding comparison
is from the **checked upstairs local normalizations**, divided by counting
measure on principal ideles and by Lebesgue measure in the log-norm
coordinate, to the mass $2^{r_1}(2\pi)^{r_2}h_FR_F/(\sqrt{|d_F|}w_F)$
on the actual norm-one quotient. The standalone presentation (A.2.3.22),
the measurable disjoint domain, and the quotient comparison remain open.

`Theorems.ComplexMultiplicativeHaarLogPolar` proves the local measure
identity `Masullo.complexTamagawaDensity_map_logPolar`, using the density
from `Lemmas.ArchimedeanCompletionHaar`:

```lean
MeasureTheory.Measure.map (fun z : ℂ ↦ (2 * Real.log ‖z‖, Complex.arg z))
    Masullo.complexTamagawaDensity =
  (MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
    (MeasureTheory.volume.restrict (Set.Ioo (-Real.pi) Real.pi))
```

Definitions A.3.1.2(2), p. 556, and A.3.2.2(1), p. 560, give the
Cartesian density. Lean supplies the change of variables needed to use
the sector of (A.2.3.21), p. 551. The pinned
`Complex.lintegral_comp_polarCoord_symm` supplies the radial Jacobian and
removes the null cut ray. In the positive radial integral, the factor
$2$ in additive Haar cancels the factor $1/2$ in $dr/r=dx/2$ via
`MeasureTheory.lintegral_image_eq_lintegral_abs_deriv_mul` applied to
$r=\exp(x/2)$. The open principal-argument interval is a measure chart,
not the manuscript's half-open torsion sector $[0,2\pi/w_F)$. The theorem
`Masullo.complexCompletionHaar_map_logPolar` transfers the identity to
actual complex completion units by `complexCompletionHaar_map` and
isometry of the chosen complex embedding.

Independent Yah statement review: Session
`01a202a6-4063-74b7-99da-31335e5b3f4f`, child `review-log-polar` (`NtmwSRX`,
read-only output `1b0f978e4adc52ebec87b6c4ba002c781457028a`). The source
reading is provisional, from pinned Markdown and numbered PDF layout.

```sh
go run ./cmd/godel audit-local "$CANDIDATE" \
  Theorems.ComplexMultiplicativeHaarLogPolar -- \
  Masullo.complexTamagawaDensity_map_logPolar \
  Masullo.complexCompletionHaar_map_logPolar
```

## Checked signed real log Haar

[`Theorems.RealMultiplicativeHaarLogSign`](../../Proofs/Theorems/RealMultiplicativeHaarLogSign.lean)
proves that `(log |y|, sign y)` sends the real density `dy / |y|` to
Lebesgue measure times counting measure on the two signs. Definitions
A.3.1.2(1), PDF p. 556, and A.3.2.2(1), p. 560, supply the density.
Lean supplies the local coordinate calculation: Remove the null origin,
substitute $y=\exp(x)$ and $y=-\exp(x)$ separately, and cancel the
absolute derivative with the density on each half-line. The isometric
real completion embedding transports the result to the actual units:

```lean
MeasureTheory.Measure.map
    (fun u : v.Completionˣ ↦
      (Real.log ‖u.val‖, if 0 < extensionEmbeddingOfIsReal hv u.val then true else false))
    (Masullo.realCompletionHaar hv) =
  (MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
    (MeasureTheory.Measure.count : MeasureTheory.Measure Bool)
```

The distinguished real branch of (A.2.3.20), p. 550, restricts the sign
to `true`; other real places keep both signs. Each sign has counting
mass one. This local formula does not build the lattice window or
calculate the global quotient volume.

Independent Yah statement review: Session
`01a202bc-2ba8-70d7-b4f9-c09af87cba45`, child `review-real-log`
(`kUgMXOk`, read-only output `2e09f91865d96d1f7b6f50605b48e26268545245`).
The source reading is provisional, from pinned Markdown and numbered
PDF layout, not rendered pages.

```sh
go run ./cmd/godel audit-local "$CANDIDATE" \
  Theorems.RealMultiplicativeHaarLogSign -- \
  Masullo.realMultiplicativeDensity_map_logSign Masullo.realCompletionHaar_map_logSign
```

## Checked separation of the Archimedean log measure

[`Theorems.ArchimedeanLogMeasure`](../../Proofs/Theorems/ArchimedeanLogMeasure.lean)
proves that $x\mapsto (\sum_v x_v,(x_v)_{v\ne w_0})$ sends product
Lebesgue measure to Lebesgue measure in the norm coordinate times
product Lebesgue measure on `logSpace K`, without a scalar. This includes
unit rank zero: The empty product of retained coordinates has mass one.
Masullo gives the weighted logs and their sum-zero hyperplane in
(A.2.3.3)–(5), PDF p. 548. Definition A.3.2.1, pp. 559–560, specifies
$dt/t$ in the norm direction and prescribes the norm-one quotient mass.
Lean supplies the missing product-measure calculation: Separate the
omitted singleton, then translate it by the sum of the retained logs,
using `MeasurePreserving.skew_product`. The retained measure is not
Euclidean surface measure on the embedded hyperplane.

Independent Yah statement review: Session
`01a202c5-7d6d-78ac-987c-b7b39fef0e27`, child `review-arch-log-split`
(`zONMBFj`, read-only output `151efcc182f2aceda0b505c3cff76917cc9457d8`).
Source readings are provisional: Pinned Markdown and numbered PDF layout,
not rendered pages.

```sh
go run ./cmd/godel audit-local "$CANDIDATE" Theorems.ArchimedeanLogMeasure -- \
  Masullo.measurePreserving_archimedeanLogSplit
```

## Checked Archimedean product Haar coordinates

[`Theorems.ArchimedeanHaarCoordinates`](../../Proofs/Theorems/ArchimedeanHaarCoordinates.lean)
uses the weighted logs of (A.2.3.3)–(5), PDF p. 548, and the local
normalizations of Definitions A.3.1.2(1)–(2), p. 556, and A.3.2.2(1),
p. 560. For the Archimedean factor of (A.3.2.5), p. 560, Lean proves the
additional coordinate calculation: `measurePreserving_archimedeanHaarCoordinates`
sends the product of actual completion-unit Haar measures under
$(u_v)_v \mapsto (\sum_v x_v,(x_v)_{v\ne w_0},(a_v)_v)$ to
`volume.prod (volume.prod (Measure.pi archimedeanAngularMeasure))`.
Here $x_v=v.\mathrm{mult}\log\|u_v\|$. The angular coordinate is the sign
with counting measure (mass one per sign), or `Complex.arg` with Lebesgue
measure on $(-\pi,\pi)$ (total mass $2\pi$). The retained logs use
product Lebesgue measure, not hyperplane surface measure.

`measurePreserving_archimedeanLocalCoordinates` packages the checked local
identities. `measurePreserving_piProd` proves the interchange of finite
products and pairs on measurable rectangles. The main proof applies the
checked log split to the reordered product, leaving the angular factor
fixed. `measurePreserving_infiniteAdeleHaarCoordinates` transports the
result to `(InfiniteAdeleRing K)ˣ` with the comap of precisely that local
product measure. It does not identify an independently normalized Haar
measure or give a pointwise angular fundamental domain.

Independent Yah statement review: Session
`01a202d2-0b9c-7544-b307-83c5a1a823a5`, child `review-arch-product`
(`MvwPSWE`). Source readings are provisional: Pinned Markdown and numbered
PDF layout, not rendered pages.

```sh
go run ./cmd/godel audit-local "$CANDIDATE" \
  Lemmas.ArchimedeanAngularChart Lemmas.MeasurePreservingPiProd \
  Theorems.ArchimedeanHaarCoordinates -- \
  Masullo.measurePreserving_archimedeanLocalCoordinates \
  Masullo.measurePreserving_piProd \
  Masullo.measurePreserving_archimedeanHaarCoordinates \
  Masullo.measurePreserving_infiniteAdeleHaarCoordinates
```

## Checked half-open regulator box

[`Theorems.RegulatorBox`](../../Proofs/Theorems/RegulatorBox.lean) realizes
Masullo's half-open parallelotope $P$ in (A.2.3.8)–(11) and Lemma
A.2.3.5(2), p. 549, as `regulatorBox K` in the retained weighted log
coordinates. It is Borel. Every point has a unique translation into it
by an element of `NumberField.Units.unitLattice K`, pointwise, not just
almost everywhere. This uses Mathlib's unit-log basis and the equality
of its integer span with the unit lattice.

For the factor $R_F$ in (A.3.2.1), pp. 559–560, Lean supplies the
product-Lebesgue calculation `volume_regulatorBox` using the covolume of
this particular fundamental domain. `NumberField.Units.regulator_eq_det`
identifies it with the absolute determinant of the weighted log matrix
with a place omitted. The preceding `measurePreserving_archimedeanLogSplit`
is what gives this product measure from the full Archimedean measure;
no hyperplane surface measure enters. The proofs include unit rank zero.

Independent Yah statement review: Session
`01a202d9-c7ac-71f6-a674-b86e8a264530`, child `review-regulator-box`
(`cPhHGXS`). Source readings are provisional: Pinned Markdown and
numbered PDF text, not rendered pages.

```sh
go run ./cmd/godel audit-local "$CANDIDATE" Theorems.RegulatorBox -- \
  Masullo.regulatorBox Masullo.measurableSet_regulatorBox \
  Masullo.existsUnique_unitLattice_vadd_mem_regulatorBox Masullo.volume_regulatorBox
```

## Archimedean torsion sector and angular mass

Definition A.2.3.6, (A.2.3.13), PDF p. 549, and (A.2.3.20)–(21),
pp. 550–551, specify a positive sign or a half-open sector at one place.
The proof of Lemma A.2.3.8(2), p. 551, invokes this as a pointwise torsion
fundamental domain. Lean supplies the reduction in
[`Lemmas.ArchimedeanTorsionOrbit`](../../Proofs/Lemmas/ArchimedeanTorsionOrbit.lean):
at a real place torsion embeds injectively into the two signs, and at a
complex embedding it maps onto the $w_F$-th roots of unity. The complex
proof shifts by an integer number of sector widths, checks the reduced
angle in the principal range, and proves uniqueness by comparing the
two scaled angles in $[0,2\pi)$. It includes the negative-real ray and
keeps the upper endpoint excluded.

[`Theorems.ArchimedeanTorsionOrbit`](../../Proofs/Theorems/ArchimedeanTorsionOrbit.lean)
then gives, for every norm-one Archimedean unit and every chosen place,
`existsUnique_archimedeanTorsion_translate` for the raw completion-unit
condition. [`Theorems.ArchimedeanTorsionMass`](../../Proofs/Theorems/ArchimedeanTorsionMass.lean)
identifies that condition pointwise with a measurable angular cylinder
and proves `measure_archimedeanAngularTorsionSlice`: Its product angular
mass is $\omega(\mathrm{univ})/w_F$, where
$\omega=\bigotimes_v\mathrm{archimedeanAngularMeasure}(v)$. This computes
the angular share in the Archimedean product for Lemma A.3.2.4,
(A.3.2.5), p. 560, used towards (A.3.2.1), pp. 559–560. It does not
identify the Haar measure on the global quotient.

Independent Yah statement review: Session
`01a202df-79e7-7751-a8af-ca4e1bab8ed7`, child `review-torsion-slice`
(`JmaKYxE`). Source readings are provisional: Pinned Markdown and
numbered PDF layout, not rendered-page inspection.

## Checked Archimedean unit fundamental domain

[`Theorems.ArchimedeanUnitDomain`](../../Proofs/Theorems/ArchimedeanUnitDomain.lean)
defines Masullo's $E_0$ from (A.2.3.13), PDF p. 549, on the actual
norm-one Archimedean units. The domain is Borel, and every element has
exactly one left multiplier in $(\mathcal O_F)^\times$ sending it into
$E_0$. This is the pointwise cover and disjointness of Lemma A.2.3.8(2),
(A.2.3.17), p. 550. The proof on p. 551 uses lattice reduction and torsion
reduction, then splits off torsion. Lean instead lifts the unique lattice
translation arbitrarily. `logEmbedding_eq_zero_iff` puts the ratio of
any competing lift to the chosen lift in torsion, and the pointwise
sector result identifies the two multipliers. The chosen sector place
need not be the place omitted in the regulator coordinates.

Membership in $E_0$ is pointwise equivalent to membership in the
rectangle in retained-log and angular coordinates. Lean supplies its
mass $R_F(\omega(\mathrm{univ})/w_F)$ in the product coordinate measure,
including unit rank zero. This uses the separate box and angular
calculations and `measurePreserving_infiniteAdeleHaarCoordinates` for
the logarithmic and angular coordinates of the Archimedean product.
The global restricted product identity (A.3.2.5), p. 560, is separate.
This gives the Archimedean factors needed in (A.3.2.1), pp. 559–560.
It is not a restriction of full Haar to a null norm-one fiber and does
not yet identify the quotient measure.

Independent Yah statement review: Session
`01a202ea-d804-7798-a956-9f29875456f6`, child `review-e0` (`nUVrgjW`).
Source readings are provisional: Pinned Markdown and numbered PDF text,
not rendered pages.

```sh
go run ./cmd/godel audit-local "$CANDIDATE" Theorems.ArchimedeanUnitDomain -- \
  Masullo.archimedeanUnitDomain Masullo.existsUnique_archimedeanUnit_translate \
  Masullo.archimedeanUnitDomainCoordinates Masullo.mem_archimedeanUnitDomain_iff_coordinates \
  Masullo.measurableSet_archimedeanUnitDomain Masullo.measure_archimedeanUnitDomainCoordinates
```

## Global Borel fundamental domain for the principal action

`Theorems.IdeleFundamentalDomain` constructs Masullo's union of norm-one
ideal-class translates, (A.2.3.12)–(16), pp. 549–550. It takes any section
of `ideleIdealClassNormOne`, supplied by `ideleIdealClass_normOne_surjective`.
The manuscript chooses the identity lift to be one; the Lean result does
not require this convention. The window, each translated piece, and the
union are Borel in the actual norm-one subgroup, and the pieces are
pairwise disjoint by their ideal classes.

`existsUnique_idelePrincipal_translate` proves the coverage and
pointwise disjointness in Proposition A.2.3.10(2), (A.2.3.25)–(26), p. 552:
For every norm-one idele `g`, exactly one `a : Kˣ` has `d a * g` in the
union, where `d` is the actual diagonal by `coe_idelePrincipalNormOne`.
The coverage reduction in the extracted proof after (A.2.3.28) drops the
norm-one superscript. Lean retains the norm-one infinite factor from
(A.2.3.24), (28), and Lemma A.2.3.8(2), as checked by
`ideleInfinitePart_mem_archimedeanNormOne`. In the disjointness argument,
`idelePrincipalNormOne_mem_finiteUnits_iff` proves the integral-unit test
used in the manuscript: The field multiplier and its inverse have unit
principal fractional ideal, so both lift and multiply to one over the
ring of integers. `isFundamentalDomain_ideleFundamentalDomain` packages
the exact partition for the opposite principal subgroup acting by right
multiplication, for any Borel measure. It does not establish relative
compactness, nonempty interior, local finiteness, or Haar normalization.

Independent Yah statement review: Session
`01a202f7-5de6-7fa9-a643-b500a1879bcf`, child `review-global-domain`
(`DAVCUPC`). Source readings are provisional: Pinned Markdown and numbered
PDF text, not rendered pages.

```sh
go run ./cmd/godel audit-local "$CANDIDATE" Theorems.IdeleClassCompact \
  Lemmas.IdeleUnitWindow Theorems.IdeleFundamentalDomain -- \
  Masullo.ideleInfinitePart_val Masullo.continuous_ideleInfinitePart \
  Masullo.integralUnit_mem_ideleFiniteUnits Masullo.coe_idelePrincipalNormOne \
  Masullo.idelePrincipalNormOne_injective Masullo.idelePrincipalNormOne_mem_finiteUnits_iff \
  Masullo.ideleInfinitePart_mem_archimedeanNormOne Masullo.ideleUnitWindow \
  Masullo.measurableSet_ideleUnitWindow Masullo.ideleFundamentalDomain \
  Masullo.measurableSet_ideleFundamentalDomain_piece Masullo.measurableSet_ideleFundamentalDomain \
  Masullo.ideleFundamentalDomain_piece_subset Masullo.pairwiseDisjoint_ideleFundamentalDomain_pieces \
  Masullo.existsUnique_idelePrincipal_translate Masullo.isFundamentalDomain_ideleFundamentalDomain
```

### Compute the local-product mass of the strip

Section A.3.3.1, p. 561, states the strip mass using the quotient
volume in (A.3.2.1), pp. 559–560. `Theorems.IdeleUnitWindowMass`
computes the upstairs mass without using that quotient volume, from
the local product in (A.3.2.5), p. 560. `image_ideleLogSplit_unitWindow`
identifies the actual window with the Archimedean strip times all
finite integral units; `ideleFiniteStageProduct_unitRectangle` gives
the measure of this Borel rectangle using one stage containing the
different support. The inactive factors are probabilities, and the
active product gives the inverse square root of the absolute
discriminant. `measure_archimedeanUnitWindowStrip` uses the retained
weighted logs and angular coordinates, not hyperplane surface
measure. The canonical radial section at `w₀` leaves those
coordinates fixed; the independently chosen torsion-sector place
need not be `w₀`.

`measure_ideleLogSplit_unitWindow` applies to arbitrary Borel log sets.
`measure_ideleLogSplit_unitWindow_Icc` uses the closed log interval
`[0, log T]`, of mass `ENNReal.ofReal (Real.log T)`. For `T ≥ 1` this
is the positive-radius interval `[1,T]`, including zero mass at `T=1`.
`Theorems.IdeleClassStrip` proves the class-number factor for any
homomorphic continuous section by summing disjoint Borel left
translates of the unit strip. The combined
`measure_ideleLogSplit_fundamentalDomain` uses the canonical section
and the single admissible stage equality, plus left invariance and
any ideal-class section. The stage equalities from
`exists_discriminantNormalizedIdeleHaar` supply that premise; a
single stage equality alone is not a global Haar uniqueness result.

Independent statement review: Yah session
`01a20302-ad3d-7d7c-bccb-90cd7c861684`, child `review-strip`
(`IZffZrz`). Manuscript readings are provisional: Pinned Markdown
and numbered PDF text, not rendered pages.

```sh
go run ./cmd/godel audit-local "$CANDIDATE" Lemmas.IdeleFiniteStageMeasure \
  Lemmas.IdeleUnitWindowCoordinates Theorems.IdeleClassStrip \
  Theorems.IdeleUnitWindowMass -- \
  Masullo.stageUnitRectangle Masullo.image_ideleStageUnitRectangle \
  Masullo.ideleFiniteStageProduct_unitRectangle \
  Masullo.image_ideleLogSplit_unitWindow Masullo.measure_archimedeanUnitWindowStrip \
  Masullo.measure_ideleFundamentalDomain_strip_eq_classNumber_mul \
  Masullo.measure_ideleLogSplit_unitWindow Masullo.measure_ideleLogSplit_unitWindow_Icc \
  Masullo.measure_ideleLogSplit_fundamentalDomain
```

### Checked log-Haar decomposition and fundamental-domain mass

`Theorems.IdeleLogHaar` checks the Haar decomposition used in §A.3.3.1,
p. 561. For any continuous homomorphic section, `ideleLogSplit_haar`
transports upstairs Haar to `logVolume.prod ν` with `ν` Haar on
`ideleNormOne`: The norm-one factor absorbs the positive scalar from
Haar uniqueness. No ambient measure is restricted to the norm-one fibre.
For the canonical section at the omitted place, evaluate on the product
of `[0,1]` (in log coordinates) and `ideleFundamentalDomain v r`.
`measure_ideleFundamentalDomain_of_logSplit` then gives `ν`-mass

$$
h_F R_F\,(\omega(\mathrm{univ})/w_F)\,|d_F|^{-1/2}
$$

for every ideal-class section `r` and torsion-sector place `v`. Here
`ω` is the checked product of real counting and complex angular
measures, and the upstream normalization is the one-stage restriction
from (A.3.2.5), supplied by `exists_discriminantNormalizedIdeleHaar`.
The theorem uses left invariance of `μ` and an `SFinite` second factor
with the exact product equality; in particular it applies to the Haar
factor just constructed. This computes the mass of the fundamental
domain in the norm-one ideles, not the Haar mass of the class group in
(A.3.2.1). Source reading is provisional (Markdown and numbered PDF
text, not rendered pages).

Independent statement review: Yah session
`01a20315-7831-7273-a051-683329eec269`, child `review-log-haar`
(`JiwXbAi`). Exact-candidate replay:

```sh
go run ./cmd/godel audit-local "$CANDIDATE" \
  Lemmas.LogVolume Lemmas.HaarLogSplit Theorems.IdeleLogHaar -- \
  Masullo.isHaarMeasure_logVolume_prod Masullo.logVolume_prod_of_split_haar \
  Masullo.ideleLogSplit_haar Masullo.measure_ideleFundamentalDomain_of_logSplit
```

### Checked counting-normalized Haar on the norm-one classes

[`Theorems.IdeleClassQuotientNormOne`](../../Proofs/Theorems/IdeleClassQuotientNormOne.lean)
restricts the actual principal quotient to `q₁ : ideleNormOne →*
ideleClassNormOne` on the inherited subgroup topologies, using the norm
descent in (A.1.3.6), p. 542. It is surjective and open; a fibre is exactly
one orbit for `x ↦ d a * x`, `a : Kˣ`, with `d = idelePrincipalNormOne`.
The diagonal is discrete, so `q₁` is locally injective. This relates the
pointwise partition of Proposition A.2.3.10(2), (A.2.3.25)–(26), p. 552,
to the actual class group, without assigning it an auxiliary topology.

[`Theorems.IdeleClassQuotientHaar`](../../Proofs/Theorems/IdeleClassQuotientHaar.lean)
implements the restriction-pushforward prescription in Remark A.5.2.7,
p. 571: For an ideal-class section `r` and infinite sector place `v`,
let `D = ideleFundamentalDomain v r` and `η = (ν.restrict D).map q₁`.
For `ν` Haar and `ν D < ∞`, `η` is Haar. Its open positivity uses the
countable principal cover of every saturated preimage, not just the
invariance of `η`. The nonnegative and complex Borel versions of the
Weil identity (D.1.2.1), p. 747, fix its scale: Their inner sum is over
`Kˣ` with one count per element, reindexed by the bijection
`idelePrincipalIndex` to the opposite principal subgroup acting on the
fundamental domain. The complex formula assumes a Borel `L¹(ν)` function
and gives an `L¹(η)` periodization with absolute summability for every
representative of almost every class. The pointwise Lean `tsum` uses its
usual convention on exceptional fibres. This is not an implementation of
the theorem for arbitrary functions measurable only in the completion.

The project supplies the Borel descent needed for these exact formulas:
[`Lemmas.IdelePrincipalPeriodization`](../../Proofs/Lemmas/IdelePrincipalPeriodization.lean)
uses the fibre characterization and continuous inverse charts on the
compact target to prove that every orbit-constant Borel function has a
Borel lift to the classes. The partition alone does not imply that
measurability, and the generic periodization lemma takes it as a hypothesis.

`measure_ideleClassNormOne_univ_of_logSplit` computes the mass prescribed
by Definition A.3.2.1, pp. 559–560, from the upstairs local product
(A.3.2.5), p. 560, and the length-one strip of §A.3.3.1, p. 561. The
angular factor is now explicitly $2^{r_1}(2\pi)^{r_2}$, from the two
normalized local angular masses. Thus the mass is
$h_K R_K 2^{r_1}(2\pi)^{r_2}/(w_K\sqrt{|d_K|})$.
`exists_discriminantNormalizedIdeleClassNormOneHaar` discharges the
upstream existence and normalization premises: It produces the upstairs
Haar with every admissible stage restriction, its norm-one Haar factor
in the exact Lebesgue log split, and the Haar predicate and numerical
mass of `η`. Its parameters are any infinite sector place and any
ideal-class section (available by `ideleIdealClass_normOne_surjective`).
This construction does not restrict upstairs Haar to the norm-one fibre.
The full-class transport below uses its norm-one factor.

Independent Yah statement review: Session
`01a20321-beae-7d49-8fe9-5c1015370cb1`, child `review-norm-one-quotient`
(`uJQsEiS`, read-only output `6633108634fb76da161e26f1ea8a4d70318efb69`).
Pinned Markdown and numbered PDF layout support the locators; the visual
reading remains provisional. `lake --wfail build Proofs` and
`lake env leanchecker Theorems.IdeleClassQuotientHaar` passed in the proof
workspace. Built signatures and transitive axioms were checked with
`#check` and `#print axioms`; the endpoints use only `propext`,
`Classical.choice`, and `Quot.sound`. Exact-candidate replay:

```sh
go run ./cmd/godel audit-local "$CANDIDATE" \
  Theorems.IdeleClassQuotientNormOne Lemmas.FundamentalDomainQuotientMeasure \
  Lemmas.IdelePrincipalPeriodization Lemmas.ArchimedeanAngularMass \
  Theorems.IdeleClassQuotientHaar -- \
  Masullo.ideleClassQuotientNormOne Masullo.coe_ideleClassQuotientNormOne \
  Masullo.isOpenQuotientMap_ideleClassQuotientNormOne Masullo.ideleClassQuotientNormOne_eq_iff \
  Masullo.exists_open_injOn_ideleClassQuotientNormOne Masullo.idelePrincipalIndex \
  Masullo.measurable_comp_ideleClassQuotientNormOne_iff \
  Masullo.exists_measurable_ideleClassQuotientNormOne_lift \
  Masullo.ideleClassNormOneQuotientMeasure Masullo.ideleClassNormOneQuotientMeasure_univ \
  Masullo.ideleClassNormOneQuotientMeasure_isHaarMeasure \
  Masullo.lintegral_ideleClassNormOne_Weil Masullo.integral_ideleClassNormOne_Weil \
  Masullo.measure_archimedeanAngular_univ Masullo.measure_ideleClassNormOne_univ_of_logSplit \
  Masullo.exists_discriminantNormalizedIdeleClassNormOneHaar
```

### Full-class counting Weil and the absolutely integrable weighted pairing

[`Theorems.IdeleClassWeil`](../../Proofs/Theorems/IdeleClassWeil.lean)
uses the full-class measure `ηC = (logVolume.prod η₁).map τ`, where `τ`
is the matching class log split and `η₁` the norm-one counting quotient.
It is Haar under the norm-one Haar and domain-finiteness hypotheses
above. The norm quotient has `dt/t` **relative to** `η₁`, not by direct
pushforward of `ηC` along the norm. The source normalization is Definition
A.3.2.1 and (A.3.2.1), pp. 559–560, with the split (A.2.2.12), p. 547.
The canonical single-place section is homomorphic, as required for the
group split.

If `μ` has that same split with factor `ν`, the Lean bridge identifies
`ηC` with the pushforward of `μ` restricted to `E = σ '' (univ ×ˢ D)`.
This is the restriction prescription of Proposition D.1.2.4,
(D.1.2.5), p. 748, on the actual ideles. The principal action fixes the
log coordinate and acts by the known norm-one translations. Thus `E`
is an actual Borel fundamental domain, not a restriction of `μ` to one
norm fibre. Open quotient charts crossed with the log line give Borel
descent by a countable cover. The manuscript's pointwise domain and
cited Weil formula do not alone give this descent in Lean.

`lintegral_ideleClass_Weil` and `integral_ideleClass_Weil` give the
counting specialization of (D.1.2.1), p. 747, on the full classes, for
Borel nonnegative and complex inputs respectively. They give a Borel
periodization at every representative using `tsum`, with absolute
summability for all representatives of almost every class in the
complex `L¹` case. `integral_ideleClass_Weil_weighted` applies the complex
formula to `f * (c ∘ q)` and factors out the class weight. It proves
(3.2.2.11), p. 127, at the level of Borel weighted `L¹`: The integral of
the weighted periodization equals the upstairs weighted integral. The
weighted series is absolutely summable for all representatives of
almost every class; this does not assert unweighted convergence where
`c` vanishes. To match the manuscript's continuous Schwartz periodization,
use (2.2.3.1), pp. 81–82, and its absolute convergence premise, Lemma
2.2.2.1, p. 77. Do not infer integrability upstairs from integrability of
the signed sum downstairs. These results neither establish the full
Schwartz test-class convergence hypotheses nor prove continuation.

Independent Yah statement review: Session
`01a20333-c7b0-7d23-8abe-9c3a178e97d6`, child `review-full-weil`
(`POrGJML`, read-only output `75240b93cca96c7448c530b01b679a91306dfcd4`).
Both readers used Markdown and numbered layout, without rendering;
source readings remain provisional. Exact-candidate replay:

```sh
go run ./cmd/godel audit-local "$CANDIDATE" \
  Lemmas.FundamentalDomainQuotientMeasure Lemmas.IdeleFullPeriodization \
  Theorems.IdeleClassWeil -- \
  Masullo.measurable_of_comp_openQuotientMap Masullo.ideleFullQuotient_split \
  Masullo.ideleFullPrincipal_split Masullo.ideleFullPrincipalIndex \
  Masullo.ideleFullPrincipalIndex_tsum Masullo.ideleFullFundamentalDomain \
  Masullo.measurable_ideleFullQuotient Masullo.measurableSet_ideleFullFundamentalDomain \
  Masullo.isFundamentalDomain_ideleFullFundamentalDomain \
  Masullo.measurable_comp_ideleFullQuotient_iff \
  Masullo.exists_measurable_ideleFullQuotient_lift \
  Masullo.ideleClassQuotientMeasure Masullo.ideleClassQuotientMeasure_isHaarMeasure \
  Masullo.ideleClassQuotientMeasure_eq_map_restrict Masullo.lintegral_ideleClass_Weil \
  Masullo.integral_ideleClass_Weil Masullo.integral_ideleClass_Weil_weighted
```

### Checked radial Mellin and norm-one pairing

[`Theorems.IdeleClassRadialMellin`](../../Proofs/Theorems/IdeleClassRadialMellin.lean)
proves the integral identity used in (3.2.2.5), pp. 125, 127, on the
absolute-integrability domain. The section is the canonical single-place
choice of (A.2.2.10), p. 547; log Lebesgue represents `dt/t`. The slice
`ideleClassRadialPairing` uses the unbarred character restriction in
(2.2.5.2), p. 95. `integral_ideleClass_radial` pulls back the integrable
class product, factors the character, and applies Bochner Fubini. Since
the radial scalar is nonzero, the norm-one slice is integrable for
almost every log radius. The weighted radial integrand is integrable.
`integral_ideleClass_Weil_radial` composes this with (3.2.2.11) and gives
both the integrable class product and equality to the upstairs weighted
integral. It requires Borel `f`, a continuous multiplicative `c`, and
upstairs weighted `L¹`; it does not prove everywhere convergence of
the principal sum or the norm-one slice.

Independent Yah statement review: Session
`01a2033f-4f26-7818-ba40-b5b998cbbbc7`, child `review-radial`
(`ZwliDlo`, read-only outputs `cf1d6d943de561629bce80aaa975843f3e298a6a`
and `e772aafd9334e7dd46c2a655dcc2366440961a36`). The review confirms
that the class-only endpoint needs no separate continuity of the
character or Borel hypothesis on the unweighted function: The weighted
product supplies the needed a.e. strong measurability. It used pinned
Markdown and numbered layout, not rendered pages, so source readings
remain provisional. Exact-candidate replay:

```sh
go run ./cmd/godel audit-local "$CANDIDATE" \
  Theorems.IdeleClassRadialMellin -- \
  Masullo.ideleClassRadialPairing Masullo.integral_ideleClass_radial \
  Masullo.integral_ideleClass_Weil_radial
```

### Normalized Gaussian radial integral above one

[`exists_discriminantNormalizedIdeleHeckeGaussian_radialMellin`](../../Proofs/Theorems/IdeleClassGaussianRadial.lean)
implements (3.2.2.5), pp. 125, 127, for the corrected Gaussian tensor
of Definition 3.4.3.2, p. 152. One exceptional set, one upstairs Haar,
one norm-one Haar, and one Borel principal periodization work for all
`Re s > 1`. The principal formula holds as a totalized `tsum` at every
representative, while norm-one slice integrability holds almost
everywhere. This does not assert everywhere absolute summability.

At (3.2.2.11), p. 127, the upstairs measure in Weil must be the one in
the Euler calculation. `exists_discriminantNormalizedIdeleHaar`
identifies the two witnesses by their exact stage comaps, using the
local normalization of (A.3.2.5), p. 560. The proof retains the exact
arithmetic quotient mass of (A.3.2.1), pp. 559–560, and separately
carries the factor `|disc K|⁻¹ᐟ²` on the raw Euler evaluation. The
complex Gaussian uses the opposite angular weight to (3.4.3.5)–(6),
p. 152, as required by the bilinear pairing (3.3.1.7), p. 130.
`measurable_ideleHeckeGaussian` proves the actual tensor Borel, not just
an a.e. representative of the weighted density. The continuous norm
twist reduces to the original character on norm-one classes. Its
section factor is `χ(τ(u,1)) * exp(u.toAdd * s)`; the unitary hypothesis
does not make `χ(τ(u,1))` trivial. The measure in the inner pairing is
the counting-normalized quotient Haar, and the character in (2.2.5.2),
p. 95, is unbarred.

Independent Yah statement review: Session
`01a20347-5831-7f22-8938-a9ad4bd56a26`, child `review-gaussian-radial`
(`vROsXvP`, read-only output `44afca6f261a5ef5a2aa234f5709e7267f100aab`).
The source comparison used pinned Markdown and numbered PDF layout;
no rendered pages were independently inspected, so it is provisional.
Exact-candidate replay:

```sh
go run ./cmd/godel audit-local "$CANDIDATE" \
  Lemmas.IdeleHeckeGaussianMeasurable Theorems.IdeleClassGaussianRadial -- \
  Masullo.measurable_ideleHeckeGaussian \
  Masullo.exists_discriminantNormalizedIdeleHeckeGaussian_radialMellin
```

### Checked scalar norm section for the large-norm repair

[`ideleScalarLogSection`](../../Proofs/Theorems/IdeleScalarLogSection.lean)
constructs Lemma A.2.2.4, p. 547, directly on the ideles. In the log
parameter `x`, `ideleScalarLogSection_infinite` gives one ordinary
radius `exp(x/[K:ℚ])` at every infinite place, and `_finite` gives
`1` at all finite places. `ideleNorm_ideleScalarLogSection` multiplies
the weighted local norms using `∑ w, w.mult = [K:ℚ]`, and
`ideleLogNorm_scalarSection` makes it a right inverse of `ideleLogNorm`.

Use this section for estimates, not to change the section or measures
in the existing Mellin identity. Masullo supplies the scalar section
in Lemma A.2.2.4, but the proof of Theorem 2.2.3.4(1) uses the different
section (A.2.2.11) and asserts dilation by `t` in (2.2.3.10), p. 84.
The new section has ordinary dilation `t^(1/[K:ℚ])`. A majorant still
needs a uniform lower bound for multiplication by the compact
representative's infinite part and a decay exponent at least `[K:ℚ] * N`
and strictly larger than the lattice rank. This step alone proves
neither those bounds nor any uniform periodization estimate.

Independent Yah statement review: Session
`01a20350-96e4-7bfd-a9ef-8a2f45d5a914`, child `review-scalar-section`
(`nJGikRf`, read-only output `4af503ff5c002de15974354bd355ffae92ad20ce`).
The reading compared Markdown and numbered PDF layout, not rendered
pages, and remains provisional. Exact-candidate replay:

```sh
go run ./cmd/godel audit-local "$CANDIDATE" Theorems.IdeleScalarLogSection -- \
  Masullo.ideleScalarLogSection Masullo.ideleScalarLogSection_infinite \
  Masullo.ideleScalarLogSection_finite Masullo.ideleNorm_ideleScalarLogSection \
  Masullo.ideleLogNorm_scalarSection
```

### Next: Uniform large-norm bound for the Gaussian periodization

Theorem 2.2.3.4(1), (2.2.3.4), p. 83, calls for a bound uniform
over classes. For the corrected Gaussian and its fixed finite set `T`,
aim to prove absolute summability of `a ↦ f(d a * x)` for `ideleNorm x ≥ 1`
and, for each `N : ℕ`, a constant `C > 0` independent of `x` such that
`∑' a : Kˣ, ‖f(d a * x)‖ ≤ C * ideleNorm x ^ (-(N : ℤ))` there.
Use any representative after reindexing by the principal group. This
will bound the norm-one average by that majorant times the finite
quotient mass. It is not yet a small-norm estimate.

The compact support step is supplied by
[`exists_compact_cover_ideleClassNormOne_gaussian_denominator`](../../Proofs/Theorems/IdeleClassGaussianSupport.lean)
(the exact-module proof was first checked at writer output
`99bc23d445178a1d76c08405429bb43e52521528`). One positive integer `m`
clears all indices `a` with `f(d a * b) ≠ 0` for `b` in a compact set
of actual norm-one ideles covering every norm-one class. Since the
scalar section has finite part `1`, the same denominator applies
when `f(d a * σ(x) * b) ≠ 0`: First use
`norm_finite_le_one_of_ideleHeckeGaussian_ne_zero`, then the finite
coordinate version `exists_compact_cover_ideleClassNormOne_uniform_denominator`.

Masullo supplies the fractional-ideal support reduction in Lemma
2.2.2.1(3) and (2.2.2.3), pp. 77–78. The uniformizer prescription on
pp. 79–80 does not bound radii greater than one with nonnegative
powers. `exists_uniform_denominator_of_isCompact` replaces it by the
finite image of the idele-to-ideal map on a compact set and one
integer clearing all inverse ideals. The compact representative set
is lifted by a finite open cover; no choice of a continuous section
of the principal quotient is asserted. Independent exact-statement
review: Child `ItiKqaM`, output `bfcab7af98deab3f567a5d4ca5aaf101ea9c8f47`,
in Yah session `01a20350-96e4-7bfd-a9ef-8a2f45d5a914`. The source reading
is provisional (Markdown and numbered PDF layout, not rendered pages).

**Next Lean obligation:** For the fixed `χ`, `T`, and for each `N : ℕ`,
choose `C > 0` and a natural `k > Module.finrank ℤ (mixedEmbedding.integerLattice K)`.
Show that on the compact representatives `b`, for `x.toAdd ≥ 0` and
contributing indices `a`,

```text
‖f(d a * σ(x) * b)‖ ≤
  C * Real.exp (-(N : ℝ) * x.toAdd) * ‖mixedEmbedding K ((m : K) * ↑a)‖⁻¹ ^ k.
```

Here `σ := ideleScalarLogSection`. Bound the finite test factors by one
using `‖χ‖ = 1`; derive polynomial decay for the product of local Gaussian
monomials in the maximum ordinary infinite-place radius. Obtain a positive
uniform lower bound on the ordinary radius of each `b` coordinate by
compactness (or bound the norms of the inverse coordinates from above).
This gives a lower bound by a positive constant times
`exp(x.toAdd/[K:ℚ]) * ‖mixedEmbedding K ((m : K) * ↑a)‖`. Take the decay
power at least `[K:ℚ] * N` plus the lattice exponent, using a weight
`1 + ‖·‖` before separating the factors, or take it at least the maximum
of the two and use the lattice minimum. Apply
`ZLattice.summable_norm_rpow` to the injection of contributing indices
into the nonzero points of `mixedEmbedding.integerLattice K`. The bound
reindexes by the principal group, so it does not replace the single-place
section used for the Haar identity.

**Small-norm obligation:** On the provisional text reading, the use of
Theorem 2.2.3.4(3), p. 83, on pp. 126–127 requires both zero modes to
vanish. A nontrivial norm-one character cannot suppress the term
`t⁻¹ f̂(0)` in the absolute value of the *unaveraged* class integrand.
Prove inversion with both zero modes and show that they cancel after
integration against a nontrivial norm-one character, as required by
Theorem 2.2.5.4(2), (4), pp. 97–98. For a trivial norm-one restriction,
retain the two terms and compute their Mellin contributions instead.
Analytic agreement must start on the common domain `Re s > 1`.
