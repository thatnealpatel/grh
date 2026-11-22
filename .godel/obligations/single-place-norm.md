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

### Next normalization step: Compute the local-product mass of the unit-window strip

For the Haar `μ` from `exists_discriminantNormalizedIdeleHaar`, compute
`μ (σ '' (J ×ˢ ideleUnitWindow v))`, where `σ` is `ideleLogSplit` for the
single-place section and `J` is the log interval corresponding to
`[1,T]`, `1 ≤ T`. The target is the interval length times the checked
Archimedean coordinate mass of `E₀` times
`ENNReal.ofReal ((Real.sqrt ((discr K).natAbs : ℝ))⁻¹)`. This is the
identity-class contribution to the strip in § A.3.3.1, p. 561. The finite
coordinates of the section are one. Use the stage restriction at a
finite set containing the different's support, not the existing
positive-compact calibration-box formula on an arbitrary Borel set. In
that stage the strip has the Archimedean strip as its infinite factor
and the full integral-unit subgroup at each finite place. Combine the
Archimedean split and coordinate mass with the finite unit-mass product.

The disjoint translated pieces then give the class-number factor by
Haar invariance. Separately show that the log-split Haar factor on the
norm-one ideles pushes from the Borel domain to the quotient Haar
with counting measure on principal ideles, to compare with (A.3.2.1),
pp. 559–560. Do not restrict full Haar to the null norm-one fibre.
