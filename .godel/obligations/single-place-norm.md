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
representative. Norm-one slice integrability holds almost everywhere on
the full log line and at every nonnegative log radius by the
[large-norm slice bound](#checked-pointwise-large-norm-gaussian-slices).
This does not assert everywhere absolute summability below norm one.

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

The preceding compact-support audit remains a checked prerequisite: `exists_compact_cover_ideleClassNormOne_gaussian_denominator` and the associated uniform-denominator lemmas were audited on accepted revision `00d93f83469610f817c3727f8e386b8f7ef278b5`; the five reviewed signatures and kernel replay passed, using only the permitted axioms.

### Checked uniform large-norm bound for the Gaussian periodization

[`ideleHeckeGaussian_periodization_rapidDecay`](../../Proofs/Theorems/IdeleClassGaussianRapidDecay.lean)
proves absolute summability of the principal Gaussian series for every
actual idele of norm at least one, over every number field. For each
`N : ℕ` a positive constant, independent of the idele `g`, bounds the
sum of norms by `C * ideleNorm g ^ (-(N : ℤ))`. The test uses a fixed
unitary Hecke character and any fixed finite set `T`. Ramification
coverage is needed for the Euler pairing, not for the estimate.

This is the corrected fixed-Gaussian case of Theorem 2.2.3.4(1), p. 83,
and the absolute-sum argument (2.2.3.8)–(13), pp. 83–84. The printed
endpoint bounds the absolute value of the periodization for a broader
class of tests, not the sum of norms for this fixed test. Recovery
reviewer `biWMteQ` checked this distinction and the scalar dilation on
rendered crops of pp. 83–84 and 547; the original writer used PDF layout.
The compact cover and uniform denominator replace the finite-radius
prescription of Lemma 2.2.2.1(3), pp. 77–80. The scalar section of
Lemma A.2.2.4, p. 547, gives radius `t^(1/[K:ℚ])`, not the `t` dilation
used in (2.2.3.10). The new Archimedean bound gives a coordinate at least
a fixed positive multiple of this radius times the norm of the
integral-lattice vector. The weighted Gaussian bound controls that
coordinate to any fixed power `p`. Taking `p` greater than the lattice
rank and at least `[K:ℚ] * N` gives both summability and the rate.
Only nonzero terms enter the lattice injection. Principal reindexing
returns the estimate to the original idele, with no change to Haar,
discriminant mass, or the single-place section in the radial identity.

Independent Yah statement review: Session
`01a2035d-857a-7830-b586-e74c4e7a0366`, child `review-rapid`
(`STjFuEh`, read-only output `eaa6bc1c0085ead1a3feaec7a97ccf5ffe01bc89`).
The review covers the endpoint, the weighted Gaussian bound, and the
compact-coordinate bound. Recovery session `01a203d3-a354-7089-ae50-bcb5f1d71d4d`
reviewed the final three-file assembly (`biWMteQ`) and adopted
`c18f5d2f78a8d8df37b6c69129c8c021dcd10fca` after its `audit-local`
passed: Warning-as-error `Proofs` build, joint import, and separate
kernel replays of all three modules. The five built signatures matched
the reviewed statements and used only `propext`, `Classical.choice`,
and `Quot.sound`. To repeat on that proof revision:

```sh
go run ./cmd/godel audit-local "$CANDIDATE" \
  Lemmas.IdeleHeckeGaussianDecay Lemmas.IdeleScalarArchimedeanBound \
  Theorems.IdeleClassGaussianRapidDecay -- \
  Masullo.norm_finiteHeckeGaussian_le_one \
  Masullo.exists_archimedeanHeckeGaussian_norm_mul_pow_le \
  Masullo.exists_ideleHeckeGaussian_norm_mul_pow_le \
  Masullo.exists_infinite_coordinate_ge_scaled_mixedEmbedding \
  Masullo.ideleHeckeGaussian_periodization_rapidDecay
```

### Checked pointwise large-norm Gaussian slices

[`ideleHeckeGaussian_radialPairing_rapidDecay`](../../Proofs/Theorems/IdeleClassGaussianRadial.lean)
implements the large-norm half of Theorem 2.2.5.4(2), (2.2.5.9), PDF
p. 97. Masullo's proof on p. 98 uses compactness, finite Radon Haar,
and the unaveraged estimate. Here the repaired Gaussian estimate
applies at every idele representing `τ (u, h)` because its norm is
`exp u.toAdd` for every norm-one class `h`. Borel measurability and the
unit norm of the unbarred character give an integrable slice at every
`u.toAdd ≥ 0`, including zero. Integration bounds the norm of the
pairing by the same unaveraged majorant `A * exp (-N * u.toAdd)` times
`(η₁ ν v r).real Set.univ`, not by a probability mass. The proof uses
no new argument for the compact representative cover or rapid decay.

The strengthened `exists_discriminantNormalizedIdeleHeckeGaussian_radialMellin`
instantiates the result on the *same* `T`, Borel periodization, and
counting-normalized quotient Haar as the radial formula for `Re s > 1`.
Its adjacent exact mass equality (A.3.2.1), pp. 559–560, gives the real
mass in the bound by applying `ENNReal.toReal`. The single-place section
(A.2.2.10), p. 547, the upstairs measure, the unrestricted a.e. slice
statement, and the Mellin formula (3.2.2.5), pp. 125, 127, are unchanged.

Independent Yah statement review: Session
`01a203dd-16b9-7deb-9524-c06e0a30dbeb`, child `review-large-slice`
(`gRGHhfq`, read-only output `ac3e56b6368c94fbc0dfed705d91074aec021ef2`).
The review confirmed both endpoint statements, the finite-mass premise,
and the scope of the zero-mode issue. Both readers used pinned Markdown
and numbered PDF layout, not rendered pages; the reading is provisional.
Exact-candidate replay:

```sh
go run ./cmd/godel audit-local "$CANDIDATE" \
  Theorems.IdeleClassGaussianRadial -- \
  Masullo.ideleHeckeGaussian_radialPairing_rapidDecay \
  Masullo.exists_discriminantNormalizedIdeleHeckeGaussian_radialMellin
```

### Next: Pointwise theta inversion before small-norm averaging

**Resumption handoff:** The [one-cycle rational trace audit](trace-orbital-q.md#main-cutoff-test-no-haar-lift-of-the-literal-shell-kernel)
ended at a lift obstruction. The large-norm slices including $u=0$ landed
at `0abc265a52c1`; the local integer-ring transform below landed at
`9bfb408ef0c7`. Neither needs repeating.

**Resumption update:** The general fixed-stage Gaussian now has [pointwise
inversion](#corrected-archimedean-schwartz-factor-and-pointwise-hecke-theta-inversion)
and the resulting [pointwise small-norm estimate](#zero-mode-corrected-theta-decay-at-small-norm).
Use them for averaging rather than repeating the broader inversion obligation.

Neither the large-norm bound nor the above-one Mellin identity proves
continuation, RH, or GRH. On the provisional text reading, the use of
Theorem 2.2.3.4(3), p. 83, on pp. 126–127 requires both zero modes to
vanish. A nontrivial norm-one character cannot suppress the term
`t⁻¹ f̂(0)` in the absolute value of the *unaveraged* class integrand.
The [trivial-character Gaussian inversion](#checked-pointwise-inversion-for-the-trivial-character-gaussian)
is checked at every idele. The broader obligation is actual pointwise
inversion (2.2.3.2), p. 82, for the corrected Gaussian at arbitrary
characters with a compatible Fourier normalization, retaining
`t⁻¹ f̂(0) - f(0)`. Then integrate against the norm-one character; only
there do both terms cancel for a nontrivial restriction, as required
by (2.2.5.10), (2.2.5.12), pp. 97–98. For a trivial restriction, retain
the two terms and compute their Mellin contributions instead. Analytic
agreement must start on the common domain `Re s > 1`.

#### Checked pointwise inversion for the trivial-character Gaussian

[`ideleHeckeGaussian_one_theta_inversion`](../../Proofs/Theorems/IdeleGaussianThetaInversion.lean),
accepted at `1a1110c6f535000491247596f5e9035ec3bde670`, proves a pointwise
identity for the actual principal periodization
$P(g)=\sum_{a\in K^\times}\Phi_1(ag)$ at every idele of every number field.
Here $\Phi_1$ is the existing trivial-character Gaussian. With $\delta$
the idele with Archimedean part one and finite ideal the different,
$D=|\operatorname{disc}K|$, and $A=(1/(2\pi))^{r_2}$, the identity is

$$
P(g)=\frac{P(\delta g^{-1})+A}{\sqrt D\,|g|_K}-A.
$$

The pointwise statement uses the additive test's value at zero; the
radial variant evaluates it as $A$ and uses the counting-periodization
contract to substitute the class function. Euclidean Poisson on the
scaled ideal gives the trace dual at $\delta g^{-1}$. The factor
$2^{-r_2}$ in the Gaussian transform cancels the same factor in the
ordinary Euclidean covolume. Masullo's Theorem 2.2.3.2, (2.2.3.2), PDF
p. 82, invokes Tate's adelic Riemann–Roch and uses quotient mass one
(Remark 2.2.3.3). The Lean argument derives this specialized identity
without assuming or identifying the full adelic Fourier transform.
The page reading is provisional (Markdown and numbered layout, not
rendered).

**Next on the trivial isotype:** Let $\eta_1$ be the fixed finite
norm-one Haar measure of mass $M$, and let $R(t)$ be
`ideleClassRadialPairing` for the trivial weight at log radius $\log t$.
Prove that every slice is integrable and that

$$
R(t)=\frac{R(|\delta|_K/t)+MA}{\sqrt D\,t}-MA
\qquad(t>0).
$$

In `ideleClassLogSplit`, reflection has log coordinate
$\log|\delta|_K-u$ and norm-one action $h\mapsto h_\delta h^{-1}$, where
$h_\delta$ is the norm-one component of $[\delta]$. This action preserves
$\eta_1$. Start with the existing integrability bound at nonnegative log
radius to derive the reflected tail for $0<t\le |\delta|_K$; do not use
that bound unmodified across the intermediate strip. In
`ideleHeckeGaussian_periodization_rapidDecay` the radius sign is used
in `hρ` to compare the two exponential rates. For the missing slice
integrability, extract the same lattice majorant without the rate
comparison: Choose one fixed power $p$ exceeding the lattice rank and
keep the exact factor $\exp(-p u/[K:\mathbb Q])$ in the majorant. This is
bounded on any compact log interval. Then the slice integrability
argument in `ideleHeckeGaussian_radialPairing_rapidDecay` applies with
that majorant.
For the trivial weight both zero terms survive with the actual quotient
mass and must be integrated separately on $0<t<1$; compare (2.2.5.10),
PDF p. 97. This is not the ramified Gaussian or full adelic inversion.

Check the two input modules on the pin with:

```sh
lake --wfail build +Theorems.IdeleGaussianThetaInversion \
  +Theorems.IdeleClassGaussianRadial
```

Their pointwise identity and large-norm slice bound are separate inputs;
neither proves the averaged identity by itself.

#### Local Fourier input
[`finiteCompletionIntegers_fourier`](../../Proofs/Theorems/FiniteCompletionIntegersFourier.lean)
computes the actual local trace-character integral on the integer ring:
Its negative-sign Fourier transform is the indicator of the inverse local
different multiplied by $\mu(\mathcal O_v)$ for the given additive Haar
$\mu$. The local annihilator and character orthogonality are supplied;
there is no self-dual normalization assumption. This is the local input for
Example A.3.1.10, (A.3.1.8), p. 558, not full adelic inversion. Use it to
match the finite factors and Haar constants with the global Gaussian
and the compatible Archimedean Fourier normalization in (2.2.3.2), p. 82.
The subsequent [normalized test inversion](../../Proofs/Theorems/FiniteCompletionFourierSquare.lean)
constructs Haar with integer-ring mass $(N v)^{-d_v/2}$, where $d_v$ is the
local different exponent. Its negative-sign finite transform is defined
with the conjugated *positive* local character. For the corrected global
sign, use that transform at the negated argument (equivalently remove the
conjugation in its kernel); the integer-ring indicator alone does not
detect this change. Do not remove either zero mode before nontrivial
character averaging.

#### Finite additive Gaussian and its two local zero modes

[The finite additive Gaussian](../../Proofs/Theorems/FiniteAdditiveHeckeGaussian.lean)
realizes (3.4.3.7)–(8), Definition 3.4.3.2, PDF p. 152, on all of
`v.adicCompletion K`, not just on its group of units. Its restriction is
exactly the existing `finiteHeckeGaussian`, so no factor in the idele
periodization is changed. The additive test is continuous with compact
support. Its value at the origin is `1` at an unramified place and `0` at
a ramified place. Its integral for any additive Borel Haar is the actual
Haar mass of the integer ring at an unramified place, and `0` at a
ramified place. In particular, the latter is a Fourier value at zero,
not a multiplicative zeta factor.

The manuscript specifies the tests, not this computation for arbitrary
additive Haar. The ramified calculation uses an integral unit on which
the local character is nontrivial. Multiplication by that unit preserves
the closed integer ball, so uniqueness of additive Haar with that ball's
mass gives `finiteCompletion_measurePreserving_mul_unit`. The substitution
multiplies the integral by the inverse character value; cancellation gives
zero. This uses no local mass-one or self-duality assumption.

Independent Yah statement review: Session
`01a20427-e819-7e2a-8e0b-1805c56c7463`, child `DPzChUH` (communicated
its conclusions before timeout). The source reading is provisional:
Pinned Markdown and numbered PDF layout, without rendered-page inspection.
Exact-candidate replay on this proof revision:

```sh
go run ./cmd/godel audit-local "$CANDIDATE" \
  Lemmas.FiniteCompletionAddHaar Theorems.FiniteAdditiveHeckeGaussian -- \
  Masullo.finiteCompletionIntegers_eq_closedBall \
  Masullo.finiteCompletion_measurePreserving_mul_unit \
  Masullo.finiteAdditiveHeckeGaussian \
  Masullo.finiteAdditiveHeckeGaussian_coe_unit \
  Masullo.continuous_hasCompactSupport_finiteAdditiveHeckeGaussian \
  Masullo.finiteAdditiveHeckeGaussian_zero \
  Masullo.integral_finiteAdditiveHeckeGaussian
```

Next use the local tests in the global additive tensor (3.4.3.9). This
requires the Archimedean additive extension, additive measure product and
normalization, and Fourier transforms away from zero (including the ramified
tests). For a proof via finite-coset reduction, also establish local
constancy of the ramified tests with an open additive subgroup of
periods. Do not infer a global Fourier formula from the checked local
integral. Keep both terms of (2.2.3.2), p. 82, until the norm-one
averaging is justified.

#### Archimedean fractional-ideal dual and covolume

[The trace pairing](../../Proofs/Lemmas/ArchimedeanTracePairing.lean) and
[its lattice identification](../../Proofs/Theorems/ArchimedeanIdealDual.lean)
provide the Archimedean inputs for a lattice proof of (2.2.3.2), PDF p. 82.
Theorem 2.2.3.2 cites adelic Riemann–Roch; Remark 2.2.3.3 fixes mass one
on the **additive adelic quotient** with counting measure on the diagonal.
This is not a Euclidean lattice volume calculation. Definition A.3.1.2,
PDF p. 556, and Example A.3.1.5, p. 557, supply $dx$, $2\,dx\,dy$, and the
positive trace character, whose conjugate is in the Fourier integral.
Lemma A.3.1.3, p. 556, uses the Archimedean volume of the integer-ring
lattice. Example A.3.1.11, pp. 558–559, describes an $S$-adelic annihilator,
not the full Euclidean dual of an arbitrary fractional-ideal lattice.
These readings use pinned Markdown and numbered PDF layout, not verified
rendered pages, and are provisional.

For $E=\mathbf R^{r_1}\times\mathbf C^{r_2}$ with its ordinary real
Euclidean metric, write $e:K\to E$ for the mixed embedding and $T$ for the
frequency map, identity in real coordinates and $z\mapsto 2\bar z$ in
complex coordinates. `inner_archimedeanTraceFrequency` proves that
$\langle x,T(y)\rangle$ is the sum of the real products and $2\Re(x_v y_v)$
at the complex places. On field elements this is
$\operatorname{Tr}_{K/\mathbf Q}(xy)$, by regrouping conjugate embeddings.
For a nonzero fractional ideal $I$, `mem_archimedeanIdealLattice` identifies
its lattice $L_I$ with $e(I)$. The new substantive step
`mem_archimedeanIdealLattice_euclideanDual` shows that an **arbitrary**
$v\in E$ has integral inner product against every $u\in L_I$ if and only
if $v=T(e(y))$ for some $y\in I^\vee$. The reverse construction from a
frequency uses its integer values on the embedded integral basis as
coefficients in the rational trace-dual basis. The original embedded
basis is a full **real** basis of $E$, so equality of its inner products
recovers the ambient frequency itself. Algebraically
$I^\vee=\mathfrak d_K^{-1}I^{-1}$ (`fractionalIdeal_traceDual_eq`).

Volume preservation of the change to Euclidean coordinates gives
$\operatorname{covol}_{dx}(L_I)=N(I)2^{-r_2}\sqrt{|D_K|}$ from Mathlib's mixed
embedding formula. With `archimedeanTraceMeasure`, the scalar
$2^{r_2}$ times the same Euclidean volume, the covolume is
$N(I)\sqrt{|D_K|}$. This is an Archimedean computation, not a global
adelic quotient mass or an invocation of self-duality. For Mathlib's
negative-phase volume Fourier transform $\mathcal F_E$, the compatible
trace-normalized integral has the expression
$\widehat\phi_{\mathrm{tr}}(y)=2^{r_2}\mathcal F_E\phi(T(y))$; one must use
it with the **scaled** covolume or use $\mathcal F_E$ with the **unscaled**
covolume, not mix the two.

Independent Yah statement review: Session
`01a20427-e819-7e2a-8e0b-1805c56c7463`, child `arch-dual-review` (`PgIjkqP`,
read-only output `47651bd8a11a02cc1eaf96cd19e1eb53fcb59c03`). The review
confirmed the coordinate conventions, both directions of the unrestricted
ambient dual statement, the inverse different, and both covolumes. Writer
base `61da655e889bc45bab4a530dd7f8d6e19b65f09b`; Mathlib
`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. The writer's
`lake --wfail build +Theorems.ArchimedeanIdealDual` and separate imported
signature and axiom checks succeeded. The first checked signatures match
the reviewed statements with $L_I=e(I)$ via the membership lemma; all
seven theorem endpoints below reported only `propext`, `Classical.choice`,
and `Quot.sound`. Exact integrated candidate audit (separate from writer
elaboration):

```sh
go run ./cmd/godel audit-local "$CANDIDATE" \
  Lemmas.ArchimedeanTracePairing Theorems.ArchimedeanIdealDual -- \
  Masullo.inner_archimedeanTraceFrequency \
  Masullo.inner_archimedeanEuclideanEmbedding_traceFrequency \
  Masullo.mem_archimedeanIdealLattice Masullo.fractionalIdeal_traceDual_eq \
  Masullo.mem_archimedeanIdealLattice_euclideanDual \
  Masullo.covolume_archimedeanIdealLattice \
  Masullo.covolume_archimedeanIdealLattice_traceMeasure
```

#### Checked shifted fractional-ideal Poisson summation

[`Masullo.archimedeanIdeal_poisson`](../../Proofs/Theorems/ArchimedeanIdealPoisson.lean)
proves, for every number field, nonzero fractional ideal $I$, complex
Schwartz function $\phi$ on $E$, and shift $a\in E$, that both series
below are absolutely summable and

$$
\sum_{u\in L_I}\phi(a+u)=\frac{1}{\operatorname{covol}_{dx}(L_I)}
\sum_{y\in I^\vee} e^{2\pi i\langle a,T(e(y))\rangle}\,
  \mathcal F_E\phi(T(e(y))).
$$

The sums include zero on both sides. This is a project proof of the
Archimedean input to a lattice proof of (2.2.3.2), PDF p. 82, not a
formula separately stated by Masullo. Theorem 2.2.3.2 there invokes
adelic Riemann–Roch, and Remark 2.2.3.3 fixes mass one of the *additive
adelic quotient*, not of an ordinary Euclidean lattice cell. The source
correspondence is a provisional reading of the pinned Markdown and
numbered PDF layout, without rendered-page inspection in this review.

The proof periodizes in real basis coordinates. The Schwartz majorant
on bounded sets of shifts makes the periodization continuous on the
coordinate torus. Its Haar probability coefficient at an integer tuple
$n$ is the negative-phase Euclidean Fourier transform at the unique
$v$ with $\langle b_i,v\rangle=n_i$, divided by the ordinary covolume.
`mFourierCoeff_latticePeriodization` supplies the missing calculation:
The basis coordinate map takes ambient volume to a multiple of coordinate
volume, calibrated on the unit cube; the two half-open cube conventions
agree off a null boundary. Unfolding uses global Schwartz integrability
to justify the sum-integral exchange. Schwartz decay on the Euclidean
dual gives summable coefficients, hence pointwise torus reconstruction
at the shift with the **positive** character. The ambient dual bridge
and injectivity of $T\circ e$ identify that full dual exactly with
$I^\vee$. The theorem uses unscaled volume in both the covolume and the
Fourier transform; both quantities would acquire the same factor
$2^{r_2}$ under trace-normalized volume.

Independent Yah statement review: Session
`01a2043a-58d6-7878-bb85-cb20d5ba2214`, child `statement` (`tfduHve`,
read-only output `4ab81a97db878e156fa18004865f18a3cbb3a916`). The review
checked the exact endpoint, continuous periodization and coefficient
formula, both signs, normalizations, and complete indexing. The built
signature has the reviewed quantifiers and conclusion, with local
notation for the Euclidean space and the fractional-ideal type. The
writer base is `e46ddc2d60607575a47f38b7e9bd1fe340192a2e`; Mathlib is
`fc4f59e577feb1a4956671bc04ac18aaaf8cd842` (Lean `v4.36.0`). The writer's
`lake --wfail build +Theorems.ArchimedeanIdealPoisson` passed, as did an
imported proof of the former target proposition by direct assignment of
the new theorem. Each of the four new modules passed local `leanchecker`
replay, and each endpoint below reported only `propext`, `Classical.choice`,
and `Quot.sound`.

Replay in the exact integration candidate:

```sh
go run ./cmd/godel audit-local "$CANDIDATE" \
  Lemmas.LatticeFrequency Lemmas.LatticeSchwartzPeriodization \
  Lemmas.LatticePeriodizationCoefficient Theorems.ArchimedeanIdealPoisson -- \
  Masullo.latticeSchwartzPeriodization_apply \
  Masullo.mFourierCoeff_latticePeriodization Masullo.mFourier_eq_exp_inner \
  Masullo.mem_latticeEuclideanDual Masullo.inner_latticeEuclideanDualIndex \
  Masullo.schwartz_lattice_poisson Masullo.archimedeanIdeal_poisson
```

**Next finite-to-global obligation:** The
[diagonal coset](#checked-diagonal-pullback-of-a-finite-box) and
[Fourier support and positive phase](#checked-finite-box-fourier-support-and-phase)
are checked. The centered Haar masses still need to multiply to the
reciprocal of the trace-normalized Archimedean covolume. Then combine
these inputs in the Fourier formula and extend by finite linearity to
the ramified tests, after proving their finite-coset decomposition.
Retain both zero modes in the passage to the nonzero-orbit sums, before
norm-one averaging.

#### Checked diagonal pullback of a finite box

[`Masullo.exists_finiteBox_diagonalCoset`](../../Proofs/Theorems/FiniteBoxDiagonalCoset.lean)
proves for every number field $K$, every finite adele $a$, and every
unit $g$ of the finite adele ring, that there is $x_0\in K$ such that
for every $x\in K$,

$$
   \big(\forall v<\infty,\; |x-a_v|_v\le |g_v|_v\big)
   \quad\Longleftrightarrow\quad x-x_0\in I(g).
$$

Here $I(g)$ is the existing fractional ideal of the finite idele, and
$x$ and $x_0$ use the actual completion maps. Taking $x=x_0$ proves
nonemptiness. No principality, integrality of $a$ or $g$, or restriction
on the degree, ramification, or class group of $K$ is required.

Masullo's Lemma 2.2.2.1(3), (2.2.2.3), PDF pp. 78–80, uses a finite
support bound, not an exact description of a translated box.
The finite projection of the additive covering (A.2.1.3), Lemma
A.2.1.2(1), PDF p. 545, gives existence at unit radius, while Theorem
2.2.3.2, PDF p. 82, invokes adelic Riemann–Roch. This project proof
supplies the exact diagonal index set needed by the shifted lattice
argument. These source correspondences are provisional
Markdown/layout readings, without rendered-page inspection.

The proof clears both the center and radius by one nonzero global
integer. The valuation bounds of the scaled radius are the local
extensions of a nonzero integral ideal. The canonical integral CRT
provides an integer representative of the scaled center modulo these
extensions at **all** finite places; dividing by the denominator gives
$x_0$. Ultrametricity reduces the translated inequalities to the
homogeneous ones, and `mem_finiteIdeleIdeal_iff` identifies those with
membership in $I(g)$ by fractional-ideal counts. In particular, the
zero difference is included.

Independent Yah statement review: Session
`01a20447-557d-705c-895c-7a7e44094b93`, `full-box-review` (`IvDojse`,
read-only output `a15d3cbfb4e30bc317f4fb9d8d4301397122252d`) reviewed
the all-place endpoints, scaling and signs. The integral CRT statements
were separately reviewed by `box-review` (`AETvkdM`, read-only output
`b29df76cbc0edf37095dfdff51ba01b86e61a6fd`). The joint exact integration
candidate `1ec528e0b9f4fb96d51efb7860b5488171aab606` was adopted after
`audit-local` passed on these seven modules together with the three
[diagonal-phase modules](finite-diagonal-phase.md#local-checks-and-integration-replay).
The six built signatures match the review, and each uses only
`propext`, `Classical.choice`, and `Quot.sound`. To replay just this part
of the audit from the exact integration workspace:

```sh
go run ./cmd/godel audit-local "$CANDIDATE" \
  Lemmas.FiniteCompletionPrimePow Lemmas.FiniteIdeleIdealCoordinates \
  Lemmas.IdeleCompactDenominators Lemmas.FiniteBoxCongruences \
  Lemmas.FiniteAdeleDenominators Lemmas.FiniteIdeleIdealMembership \
  Theorems.FiniteBoxDiagonalCoset -- \
  Masullo.exists_ringOfIntegers_sub_mem_finiteCompletionIdeal \
  Masullo.sub_mem_finiteCompletionIdeal_iff \
  Masullo.exists_finiteAdele_clearDenominator Masullo.mem_finiteIdeleIdeal_iff \
  Masullo.exists_ideal_finiteIdeleIdeal_of_integral Masullo.exists_finiteBox_diagonalCoset
```

#### Checked finite-box Fourier support and phase

Let $g\in\mathbf A_{K,f}^{\times}$, $B_g=\prod_v g_v\mathcal O_v$, and
$I=I(g)$ be the fractional ideal of $g$. In
[`Theorems.FiniteBoxTraceDual`](../../Proofs/Theorems/FiniteBoxTraceDual.lean),
`mem_traceDual_finiteIdeleIdeal_iff` proves for every $y\in K$ that

$$
y\in I^\vee\quad\Longleftrightarrow\quad
\forall v<\infty\;\forall t\in\mathcal O_v,\quad \chi_v(y_vg_vt)=1,
$$

where $\chi_v$ is the positive canonical local trace character. This is
about the diagonal pullback, not classification of arbitrary adelic
frequencies. For a finite adele $a$ and any $x_0\in K$ with
$x_{0,v}-a_v\in g_v\mathcal O_v$ at every finite place,
`finiteBox_tracePhase_eq_diagonal` proves for each $y\in I^\vee$ that
all but finitely many $\chi_v(y_va_v)$ equal one, and

$$
\prod_{v<\infty}\chi_v(y_va_v)
  = e^{2\pi i\operatorname{Tr}_{K/\mathbf Q}(x_0 y)}.
$$

Masullo gives the centered local support in Example A.3.1.10,
(A.3.1.8), PDF p. 558. The $S$-integer lattice orthogonal in Example
A.3.1.11, PDF pp. 558–559, is not this finite-box diagonal pullback.
Theorem 2.2.3.2, p. 82, instead invokes adelic Riemann–Roch. Lean fills
the lattice-reduction step as follows: Represent the global different
by a finite idele $h$. The placewise extension theorem and the integral
ideal membership criterion show that $h_v$ generates the local different.
Local annihilation is then the integrality condition $y_v h_v g_v\in
\mathcal O_v$. Pulling back the homogeneous box for $(hg)^{-1}$ gives
$\mathfrak d_K^{-1} I^{-1}=I^\vee$. The argument includes $y=0$ and
makes no principality assumption on either global ideal.

The conjugated Fourier kernel in (2.2.4.32), p. 92, gives the **positive**
finite factors after the [pairing sign repair](finite-diagonal-phase.md).
The difference of the two centers belongs to $B_g$, so it contributes
one at each place on the dual support. The resulting diagonal factors
have finite support and their product is the positive shift phase in
`archimedeanIdeal_poisson`. These source readings are provisional:
Pinned Markdown and numbered PDF layout, not rendered-page inspection.

Independent Yah statement review record: Session
`01a2045d-a01b-7729-b120-5b495e87d33d`, child `box-dual-review`
(`VbyJETV`). Checked against Lean `v4.36.0` and Mathlib
`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`.
To replay the declaration scope and axioms, build
`lake build --wfail +Theorems.FiniteBoxTraceDual`, then use `lake env lean`
on a fresh file importing `Theorems.FiniteBoxTraceDual` and checking
`@Masullo.mem_traceDual_finiteIdeleIdeal_iff` and
`@Masullo.finiteBox_tracePhase_eq_diagonal` with `#check` and `#print axioms`.

#### Centered finite-box mass and trace covolume

For any number field $K$ and any finite idele $g$, set $I=I(g)$ and let
$m_v(g)=\nu_v(g_v\mathcal O_v)$ be the real mass for the actual local
normalized **additive** Haar measure. In
[`Theorems.FiniteBoxCenteredMass`](../../Proofs/Theorems/FiniteBoxCenteredMass.lean),
`finiteBox_centeredMass_finprod` proves that all but finitely many $m_v(g)$
equal one, and identifies their product with the reciprocal of the
associated ideal lattice covolume in `archimedeanTraceMeasure K`.
`finiteBox_centeredMass_finprod_eq_absNorm` gives the arithmetic form:

$$
\prod_{v<\infty}m_v(g)
= \frac{1}{\operatorname{covol}_{\nu_\infty}(L_I)}
= \frac{1}{N(I)\sqrt{|D_K|}}.
$$

The endpoints use canonical Borel measures, with no auxiliary
measurable-space, principality, integrality, or unramified hypotheses.

Definition A.3.1.2(1)–(3), (A.3.1.2), PDF p. 556, stipulates trace
measure at infinity and the inverse square root of the local different
norm at each finite place. The proof of Lemma A.3.1.3 on that page
multiplies the calibrated masses at the **unit** box. Lemma A.3.1.4,
(A.3.1.4), cites the dilation formula for **global** Haar and Borel
sets. It does not give the local additive box computation used here.
To replace this appeal for the lattice proof of Theorem 2.2.3.2 and
Remark 2.2.3.3 (p. 82), Lean proves the needed local equality directly:
`finiteCompletionNormalizedHaar_real_smul_integers` gives
$\nu_v(b\mathcal O_v)=|b|_v\nu_v(\mathcal O_v)$ for every $b\ne 0$.
For integral $b$ the box is a maximal-ideal power. The prime-power
quotient equivalence gives index $q_v^{\operatorname{ord}_v(b)}$, and
additive cosets give the mass ratio. For nonintegral $b$ apply that case
to $b^{-1}$ and the Haar pushforward by multiplication by $b^{-1}$.

The product calculation compares the **scalars** at the unit box with
`prod_finiteCompletionMultiplicativeHaar_unitMass`; no identification
of the measures is made. The exceptional set includes the support of
the different as well as the places where $|g_v|_v\ne 1$. The product
of the dilation factors is $N(I^{-1})$, by `absNorm_inv_finiteIdeleIdeal`;
`covolume_archimedeanIdealLattice_traceMeasure` supplies the trace
covolume. These source readings are provisional (pinned Markdown and
numbered PDF layout, without rendered-page inspection).

Writer check in Yah session `01a20466-63f1-711c-8351-a29ff9765c84`,
assigned base `a7b18ef844a89902e35499a5e8350b10f4943fd6`, Lean `v4.36.0`,
Mathlib `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`: the following actual
build passed (8391 jobs):

```sh
lake build --wfail +Lemmas.AddSubgroupHaarIndex \
  +Lemmas.FiniteCompletionNormalizedHaar +Lemmas.FiniteCompletionCodifferentMass \
  +Lemmas.FiniteIdeleIdealNorm +Theorems.FiniteBoxCenteredMass \
  +Theorems.FiniteCompletionFourierSquare +Theorems.FiniteCompletionFourierMellin \
  +Theorems.IdeleGaussianThetaInversion
```

A fresh `lake env lean` file importing the selected modules together
checked `@` signatures and printed axioms for both box endpoints, the
local dilation theorem, `absNorm_inv_finiteIdeleIdeal`, the extracted
`measure_eq_relIndex_mul`, and the existing `finiteCompletion_codifferent_measure`.
Each depended exactly on `propext`, `Classical.choice`, and `Quot.sound`.

Exact landing: `140e39ba827eecb7f9e9b7026255fd2779974a8e` on
`9f10e8ef6104bf715c07054bf7e3c4567f15f687` reproduces the checked writer
patch from `c764da87ad1dcd29c09ab2c5f85aa1305eec2d7a` byte for byte.
In Yah session `01a20466-63f1-711c-8351-a29ff9765c84`, the owner verified
candidate sources and pins, then ran the build above with the additional
targets `+Theorems.FiniteBoxTraceDual +Theorems.ArchimedeanIdealPoisson`
(8433 jobs). A fresh joint import checked the same six signatures and
axiom reports on that candidate. Independent Yah reviewer `gJTKkEO`
checked the endpoints and promoted helpers, including the arbitrary
finite-idele quantifier, canonical Borel convention, finite support,
inverse-ideal sign, and cancellation of the complex-place factors.
The candidate was adopted without a restack (`stale: false`).

The [translated-box Fourier product](#checked-finite-fourier-product-of-a-translated-box)
now uses this mass normalization.

#### Checked finite Fourier product of a translated box

For any number field $K$, center $a\in\mathbf A_{K,f}$, radius
$g\in\mathbf A_{K,f}^{\times}$, and diagonal frequency $y\in K$, put
$I=I(g)$ and let $x_0\in K$ lie in the box. Define the actual local integral
$J_v(y)=\int_{a_v+g_v\mathcal O_v}\chi_v(y_vt)\,d\nu_v(t)$, using the
positive finite kernel and the canonical Borel additive Haar measure.
[`finiteBox_fourier_finprod`](../../Proofs/Theorems/FiniteBoxFourier.lean)
proves that $J_v(y)=1$ away from finitely many places for **every** $y$, and

$$
\prod_{v<\infty}J_v(y)=
\begin{cases}
e^{2\pi i\operatorname{Tr}_{K/\mathbf Q}(x_0y)}
/\operatorname{covol}_{\nu_\infty}(L_I), & y\in I^\vee,\\
0, & y\notin I^\vee.
\end{cases}
$$

`exists_finiteBox_diagonalCoset` supplies a center representative satisfying
this hypothesis. There is no restriction to principal ideals, unramified
places, or integral radii. In particular the theorem includes the zero mode.

Masullo gives the centered local transform in Example A.3.1.10, (A.3.1.8),
PDF p. 558, and the translated rational prime-power example in A.3.1.6,
PDF p. 557. The product of local integrals appears in (2.2.4.32), p. 92;
Theorem 2.2.3.2, p. 82, instead invokes adelic Riemann–Roch. The
[corrected pairing](finite-diagonal-phase.md) uses the positive finite
factors in the Fourier kernel. The arbitrary local box calculation
needed here is `finiteCompletion_box_fourier`: Translate the set integral
by Haar invariance, factor off the positive phase at the center, and apply
character orthogonality on the measurable subgroup $g_v\mathcal O_v$.
This gives phase times centered real Haar mass if the character is trivial
on that subgroup, and zero otherwise. These readings are provisional:
Pinned Markdown and numbered PDF layout, not rendered-page inspection.

For finite multiplicative support, the proof uses cofinite integrality of
$y_v$, $a_v$, and $g_v$ and cofinite unit mass. The local trace character
of any completion integer is one by `finiteCompletion_traceChar_eq_one_of_integral`
(trace commutes with localization). Thus one can use an actual zero factor
to evaluate the product off $I^\vee$, rather than invoking `finprod`'s
infinite-support default. On $I^\vee$, the checked trace-dual support, phase
product, and centered-mass product give the formula.

Landing: `88a3e65a3e75b353e855329a127d87d094f1eb20` on base
`b8cabd6eb671c4db055ea68ff68acfed4fe16d1b`. Yah session
`01a20473-41ea-784a-b041-316d86880af7`, sequence 128 (command) and 136
(result), records `lake build --wfail` for the changed modules and
`Lemmas.FiniteCompletionDiagonalTrace`, `Theorems.NumberFieldDiagonalPhase`,
and `Theorems.FiniteBoxTraceDual`. The fresh joint import of the three
changed modules checked the binders and axioms of all three declarations
above and `finiteCompletionDiagonalPhase_hasFiniteMulSupport`. All four
use only `propext`, `Classical.choice`, and `Quot.sound`. The owner matched
these types to the independent mathematical review (`QMraDyh`, sequence
150); the reviewer did not attest a build or reread of the integrated
candidate. Adoption is at sequence 152.

#### Shifted Poisson in Archimedean trace measure

[`ArchimedeanTracePoisson.lean`](../../Proofs/Theorems/ArchimedeanTracePoisson.lean)
uses the same Euclidean mixed space $E$, trace frequency map $T_K$, and
ideal lattice $L_I$ as `archimedeanIdeal_poisson`. Masullo gives the real
and complex local measures and characters (Definition A.3.1.2(1)–(2),
PDF p. 556; Example A.3.1.5, p. 557) and uses the conjugated kernel in
(2.2.4.32), p. 92. These readings are provisional (pinned Markdown and
numbered PDF layout). The shifted mixed-space normalization needed for
the lattice proof of Theorem 2.2.3.2, p. 82, is supplied by Lean:

- `archimedeanTraceFourier_eq` matches the integral with kernel
  $e^{-2\pi i\langle x,T_K y\rangle}$ against `archimedeanTraceMeasure K`
  at any $y\in E$ to $2^{r_2}\mathcal F_{\mathrm{vol}}\phi(T_K y)$.
  This equality uses Mathlib's totalized integral for arbitrary $\phi$;
  the Poisson theorem uses a Schwartz input.
- `covolume_archimedeanIdealLattice_traceMeasure_eq_smul` multiplies
  the ordinary covolume by the same $2^{r_2}$.
- `archimedeanIdeal_tracePoisson` cancels the scalars. For any nonzero
  fractional ideal, any Euclidean shift $b$, and any complex Schwartz
  $\phi$, both full series are absolutely summable. Their identity uses
  the trace-measure Fourier integral, the positive phase
  $e^{2\pi i\langle b,T_K\iota(y)\rangle}$ for $y\in I^\vee$, and the
  reciprocal trace covolume. Both zero indices are retained.

Review and exact-candidate replay: Yah improvement session
`01a2047b-f88e-7f1f-bbe0-8db92c92fc62`, independent draft statement review
`XgQoRQE`. Build `lake build --wfail +Theorems.ArchimedeanTracePoisson`.
In a fresh file, import `Theorems.ArchimedeanTracePoisson`,
`Theorems.FiniteBoxFourier`, and `Theorems.FiniteBoxDiagonalCoset`
together; `#check @` and `#print axioms` the new definition and the
three listed theorems. This checks the local normalization, not a
product-measure identification of `archimedeanTraceMeasure`.

#### Full diagonal Poisson sums for one translated finite box

[`finiteBox_diagonal_poisson`](../../Proofs/Theorems/FiniteBoxPoisson.lean)
is unconditional for any number field $K$, any finite adele center $a$,
any finite idele radius $g$, and any complex Schwartz function $\phi$
on the Euclidean mixed space. Let $S$ denote the diagonal pullback of
$a+g\prod_{v<\infty}\mathcal O_v$ and $\iota$ the Euclidean mixed embedding.
The theorem proves absolute summability of both series and

$$
\sum_{x\in K} 1_S(x)\phi(\iota x)
=\sum_{y\in K}\widehat\phi_{\mathrm{tr}}(\iota y)
  \prod_{v<\infty} J_v(y).
$$

The newly named `finiteBoxLocalFourier` is the same Borel Haar integral
$J_v$ previously written out in `finiteBox_fourier_finprod`; the latter
still proves finite multiplicative support at every $y$ and the product
formula. The Poisson proof chooses $x_0$ in the box by the checked coset
lemma and reindexes $S$ by $x\mapsto\iota(x-x_0)$. On the frequency side
it extends the trace-dual series by zero, using the evaluated finite
product and `inner_archimedeanEuclideanEmbedding_traceFrequency` to match
the positive phase and reciprocal trace covolume in shifted Poisson.
The sums range over all of $K$. At $y=0$ the product supplies the reciprocal
trace covolume, with phase one. At $x=0$ the summand is $\phi(0)$ if zero
is in the box and zero otherwise. The zero lattice index instead represents
$x_0$, which need not be zero.

Masullo's Theorem 2.2.3.2 (PDF p. 82) invokes adelic Riemann–Roch and
states the punctured theta identity on idele classes, with the two
zero-mode corrections. Remark 2.2.3.3 specifies quotient mass one.
Here the shifted ideal-lattice calculation replaces that invocation
for the full diagonal sums of a single box, before identifying the
global Fourier integral or applying idelic dilation. The product in
(2.2.4.32), p. 92, concerns a differentiated tensor with compactly
supported infinite factor. The local integrals here integrate the box
in the integration variable and use the [corrected pairing](finite-diagonal-phase.md),
not a literal reading of the finite factor in that display. The centered
transform in Example A.3.1.10, (A.3.1.8), p. 558, does not calculate the
translated phase. These readings are provisional: Pinned Markdown and
numbered PDF layout, without rendered-page inspection.

Replay: Build `lake build --wfail +Theorems.FiniteBoxPoisson
+Theorems.FiniteBoxFourier` and import both modules together. Check `@` types
and axioms for `finiteBoxLocalFourier`, `finiteBox_fourier_finprod`, and
`finiteBox_diagonal_poisson`. See the exact-candidate landing and independent
mathematical statement review in Yah session `01a20482-db51-7fa6-bd56-fdff5ef6ac22`
(reviewer `chDkZnH`).

#### Additive Haar on the actual finite stages

[`adeleFiniteStageHaar`](../../Proofs/Theorems/AdeleFiniteStageHaar.lean)
is the Borel product on `AdeleFiniteStage K S` for any number field $K$ and
finite set $S$ of finite places. Its Archimedean factor is
`archimedeanTraceMeasure K` carried to the infinite adele ring by
`archimedeanEuclideanToAdele K`. The two finite-place factors are the
finite product of `finiteCompletionNormalizedHaar` on the full fields in
$S$ and the infinite probability product of the **actual comaps** of those
measures along $\mathcal O_v\hookrightarrow K_v$ off $S$.
`adeleFiniteStageHaar_isAddHaarMeasure` proves this is additive Haar under
exactly the omitted mass condition $\nu_v(\mathcal O_v)=1$ for $v\notin S$;
this includes $S=\varnothing$ if all the masses are one. No topological
or measurable structure on $K$ is an extra hypothesis. The support
module proves that each such comap is probability, then that the tail
product is translation invariant and Haar on the compact product.

The restricted-product prescription before Definition A.3.1.2, PDF p. 556,
supplies the stage shape, and that definition supplies $dx$, $2\,dx\,dy$,
and the inverse square-root different norm at the finite places. This
is the stage input to Lemma A.3.1.3, (A.3.1.3), and not yet the equality of
the product with the global quotient-normalized measure. The stage here
has integral tail coordinates; it is not the finite Cartesian product
$\mathbf A_{F,S}$ in the separate $S$-local claim. Reading provisional:
Pinned Markdown and numbered PDF layout, without rendered-page inspection.

Replay: `lake build --wfail +Lemmas.AdeleFiniteStageMeasure
+Theorems.AdeleFiniteStageHaar +Theorems.FiniteBoxPoisson`. Import the three
modules together, `#check @` and `#print axioms` on the stage definition and
Haar theorem, and `#print Masullo.adeleFiniteStageHaar` for the factors.
The owning Yah ran these checks on adopted candidate
`5ebb1863c3039c8c8d54c428f6624b4bae43a788`, based on
`0342564585491fbce6725c6e1f7b65f07d239f42` (session
`01a2048a-b0d1-738f-834c-e3fa0194075b`; independent reviewer `KDWPsmK`).
The built statement has exactly the omitted mass premise above. The
joint import also checked by `rfl` that both groups of local factors use
the explicit canonical Borel Haar of `finiteBoxLocalFourier`, and that
the omitted factors are comaps. All eight inspected declarations used
only `propext`, `Classical.choice`, and `Quot.sound`.

#### Restricted-product additive Haar on the actual adeles

[`Theorems.AdeleRestrictedProductHaar`](../../Proofs/Theorems/AdeleRestrictedProductHaar.lean)
works over every number field $K$, with the Borel structure of the actual
adele topology. Put $m_v=\nu_v(\mathcal O_v)$ for the previously checked
local additive Haar $\nu_v$. `exists_finiteCompletionIntegerMass_exceptions`
proves that $\{v:m_v\ne1\}$ is finite: Use the finite-support half of
`finiteBox_centeredMass_finprod` at unit radius, and finiteness of the
mass of the compact integer ring to pass from real to extended masses.

For any finite set $E$ containing those exceptions,
`exists_adeleRestrictedProductHaar` constructs regular additive Haar $\mu$
and characterizes it among **all Borel measures** $\lambda$ by
$$
\lambda=\mu\quad\Longleftrightarrow\quad
\forall S\supseteq E,\quad j_S^*\lambda=\mu_S.
$$
Here $j_S$ is the actual open stage embedding, and $\mu_S$ is the stage
Haar above. The theorem also gives, for every Borel $B$ in the infinite
adeles,
$$
\mu(B\times\textstyle\prod_{v<\infty}\mathcal O_v)
  =\nu_\infty(B)\prod_{v\in E}m_v,
$$
where $\nu_\infty$ is the transported `archimedeanTraceMeasure K`. The
proof scales upstairs Haar on the common compact positive integral-finite
box. On every cofinal stage the box has the same mass, since newly
included places have $m_v=1$. Haar uniqueness identifies the stage
comaps. Countable cover by Borel stage images gives the stated uniqueness,
without Haar, regularity, or σ-finiteness assumptions on $\lambda$.

Masullo's restricted-product prescription before Definition A.3.1.2,
PDF p. 556, supplies the stage shape and invokes existence and uniqueness.
Definition A.3.1.2 supplies the local scales. To use a probability product
of actual integer-ring restrictions, Lean takes only the cofinal stages
containing the exceptions; a non-unit local mass cannot be discarded in
an omitted factor. This constructs the product $\nu'$ in the proof of
Lemma A.3.1.3, (A.3.1.3), p. 556, **not** the equality $\nu'=\nu$.
Definition A.3.1.1, p. 555, requires mass one for the counting-induced
quotient. The remaining bridge is a Borel fundamental domain for diagonal
$K$, with the counting quotient identity and mass one. Use a full
$[K:\mathbb Q]$-dimensional integral-basis Archimedean parallelotope: The
extracted (A.2.1.1), p. 545, sums only to $r_1+r_2$. The separate $S$-local
claim concerns a finite product **without** the integral tail. For
$K=\mathbb Q(i)$ and $S=S_\infty$, the trace-product covolume of
$\mathbb Z[i]$ is $2$ (the unit square has measure $2\,dx\,dy$), so that
product is not counting-quotient-normalized. These readings are
provisional: Pinned Markdown and numbered PDF layout; no rendered-page
visual verification.

Check record: Lean candidate `c363549d11af7aa056a75a8ab0b71160a60bdf49`
on `92f3aa50fba0f19a23ca95ab16ff69e0c94cbca6`, owning Yah session
`01a20499-69f0-72e1-8653-addac09cd2dc`. Independent mathematical statement
review `lOZnIHc` checked the two endpoint signatures, including the
canonical Borel setting, the exceptional-set premise, and the universal
measure quantifier. It did not attest the build. The owning integration
workspace passed `lake build --wfail` on 67 changed, affected, and
support targets. A fresh joint import checked the built binders and
normalizations, and all 20 axiom reports listed only `propext`,
`Classical.choice`, and `Quot.sound`.
Replay with at least:

```sh
lake build --wfail +Lemmas.AdeleFiniteStage +Lemmas.AdeleFiniteStageMeasure \
  +Lemmas.AdeleRestrictedProductMeasure +Theorems.AdeleFiniteStageHaar \
  +Theorems.AdeleRestrictedProductHaar +Theorems.FiniteBoxCenteredMass
```

Import these modules together in a fresh file. For both public endpoints,
run `#check @Masullo.<name>` and `#print axioms Masullo.<name>`; print
`finiteCompletionIntegerMass`, `adeleFiniteStageHaar`, and
`adeleFiniteStageOutsideFactor` to recover the local normalization and
verify that the tail uses the actual comaps. The proof candidate uses
Lean `v4.36.0` and Mathlib `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`.

### Continuous finite-adele trace character

On the actual finite adeles of any number field, the
[`FiniteAdeleTraceCharacter`](../../Proofs/Theorems/FiniteAdeleTraceCharacter.lean)
module constructs `numberFieldFiniteAdeleAddChar`. Masullo gives the
positive local trace characters in Example A.3.1.10, PDF p. 558, and a
global trace pullback in Example A.3.1.9, (A.3.1.7), on the same page.
The [diagonal phase repair](finite-diagonal-phase.md) shows why the
finite factors need conjugating while retaining the positive
Archimedean phase. Diagonal compatibility alone did not construct
an additive character or give continuity off the diagonal. Lean uses
local triviality on the integer ring (not an exact conductor claim),
finite multiplicative support, and restriction to stages to prove a
continuous unit-modulus character. Its conjugate has the positive
local phases of `finiteBoxLocalFourier`; its value at a diagonal
$x$ cancels the positive Archimedean phase of $\mathrm{Tr}_{K/\mathbb Q}(x)$.
The source reading remains provisional (pinned Markdown and numbered
PDF layout). See the [exact-candidate check and independent review](finite-adele-trace-character-check.md).

### Global trace character and the Archimedean Fourier factor

[`numberFieldAdeleAddChar`](../../Proofs/Theorems/AdeleTraceCharacter.lean)
combines the positive phase on the actual infinite completions with the
conjugated product on the actual finite adeles. It is a continuous
additive character of modulus one, trivial on the whole diagonal $K$.
Masullo's Example A.3.1.5 (PDF p. 557) specifies the positive real
and complex trace phases, and Example A.3.1.9, (A.3.1.7), p. 558,
specifies the trace pullback. The finite sign repair enters explicitly
in the product defining the character, using the already checked
finite character. On the Archimedean side,
[`archimedeanAdeleTrace_mul`](../../Proofs/Lemmas/ArchimedeanAdeleTrace.lean)
identifies the phase of the product with the trace pairing in continuous
mixed coordinates, including twice the real part at complex places.
Its diagonal specialization uses the rational field trace. These source
readings are provisional, based on the pinned Markdown and numbered
PDF layout.

`integrable_archimedeanAdeleFourierIntegrand` and
`archimedeanAdeleFourierIntegrand_integral` prove that at every diagonal
frequency the actual infinite-adele integral converges absolutely and
agrees with `archimedeanTraceFourier`. They transport the trace measure
through the same equivalence used in `adeleFiniteStageHaar`. The
Archimedean Schwartz factor need not have compact support. The measure
and the negative Fourier phase, rather than just the absolute value of
the phase, are both matched. This is the Archimedean factor of the
product, not an identification of the actual global integral.

Replay: `lake build --wfail +Theorems.AdeleTraceCharacter
+Theorems.AdeleRestrictedProductHaar`. Jointly import these modules and
`Theorems.FiniteBoxFourier`, and check the built signatures and axioms of
`numberFieldAdeleAddChar`, its continuity, norm, and diagonal identities,
and the Archimedean endpoints above. Exact-candidate checks and statement
review are in Yah session `01a204c2-4f2b-73b9-ad63-5fdca6cd4879`.

### Global Fourier integral for a translated finite box

[`adeleBox_fourier_integral`](../../Proofs/Theorems/AdeleBoxFourier.lean)
works over every number field $K$, on the actual adeles. Let $a$ be a
finite adele, $g$ a finite idele, $\phi$ a complex Schwartz factor at
infinity, and $y\in K$ any diagonal frequency, including zero. With
$F=\phi\otimes 1_{a+g\prod_v\mathcal O_v}$ and $\psi$ the checked global
character, the theorem proves integrability and
$$
\int_{\mathbf A_K}F(z)\,\overline{\psi(zy)}\,d\mu(z)
  = \widehat\phi_{\rm tr}(\iota y)
    \prod_{v<\infty}\operatorname{finiteBoxLocalFourier}(a,g,y,v)
$$
for every Borel measure $\mu$ with the prescribed stage comaps on a
cofinal set of stages. `exists_adeleBox_fourier_integral` obtains one
regular additive Haar measure with those comaps that works simultaneously
for all $a$, $g$, $\phi$, and $y$.

Masullo's (2.2.4.32), PDF p. 92, supplies the conjugated Fourier kernel
and tensor shape for compact-open local tests and a compactly supported
Archimedean factor. The printed local indicator uses the frequency;
`adeleBoxTensor` evaluates it at the integration variable. The Lean result
is for translated finite boxes, not arbitrary compact-open test families.
It proves the integral split without compact support at infinity by
transporting Schwartz integrability. The restricted-product prescription
before Definition A.3.1.2, p. 556, provides the stage shape and local
scales. The proof uses the cofinal stages containing the mass exceptions,
with the signs from `AdeleTraceCharacter`. The comparison with (2.2.4.32)
is provisional (pinned Markdown and numbered PDF layout).

Choose $S$ containing the mass exceptions and all nonintegral coordinates
of $a$, $g$, $g^{-1}$, and the diagonal $y$. The full integrand vanishes
outside the stage image. Transfer its integral using the comap, split the
conjugated kernel, and apply Fubini. `finiteAdeleBox_stage_fourier` proves
that the omitted boxes are integer rings, the phases are trivial there,
and the omitted mass is one. This identifies the existing right-hand
summand of `finiteBox_diagonal_poisson` as an actual Fourier integral,
without adding a convergence hypothesis or dropping the zero mode.

Replay: `lake build --wfail +Lemmas.FiniteBoxStageFourier
+Theorems.AdeleBoxFourier +Theorems.FiniteBoxPoisson`. Jointly import
these modules and `Theorems.AdeleTraceCharacter`; check the binders and
axioms of `adeleBoxTensor`, `adeleBoxFourierIntegrand`,
`finiteAdeleBox_stage_fourier`, and the two global endpoints above.

Exact-candidate check: `654e487c78d896e52647ed0c1375a9520efdc7ad` on
`b98c4c5a0b089d40082ae3f0c762827e8cb30038`, adopted after the local
`lake build --wfail` and fresh joint import of these modules plus
`Theorems.AdeleRestrictedProductHaar`. The built statements had the
actual adele and finite-stage domains, the canonical cofinal comaps,
and unrestricted diagonal $y\in K$. All thirteen axiom reports,
including `finiteBox_diagonal_poisson`, listed only
`propext`, `Classical.choice`, and `Quot.sound`. Independent reader
`KdHDnvk` confirmed the intended statements and exact scope, including
why the product is genuinely finite and why no quotient normalization
follows. The check transcript and review are in Yah session
`01a204cc-1b12-7aec-9ee7-3bcbcd0c5b7f`. Lean `v4.36.0`, Mathlib
`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`.

**Earlier target (completed in the section below): Identify this product
Haar with the counting-quotient normalization.** Use the same $\mu$ and diagonal $K\subset\mathbf A_K$.
Construct a Borel fundamental domain $D=P\times\prod_v\mathcal O_v$.
Masullo gives the product form in (A.2.1.2), PDF p. 545, but (A.2.1.1)
indexes the half-open cube by infinite places. In a field with complex
places this is fewer than the number of integral basis vectors. Use
real coordinates $[0,1)^{[K:\mathbb Q]}$ in a full integral basis
instead (provisional reading, Markdown and numbered layout).
`ZSpan.fundamentalDomain_measurableSet` and
`ZSpan.exist_unique_vadd_mem_fundamentalDomain` give the relevant
Archimedean interfaces. Use `exists_finiteBox_diagonalCoset` at unit
scale to make the finite part integral and identify the residual
translations by $\mathcal O_K$, then reduce by that lattice at infinity.
Prove `IsAddFundamentalDomain` for the diagonal subgroup acting on the
actual adeles. Compute $\mu(D)=1$ using the rectangle identity in
`exists_adeleRestrictedProductHaar` and
`finiteBox_centeredMass_finprod` at $g=1$: The latter already gives the
reciprocal trace covolume for the real-valued finite mass product. It
remains to identify the unit ideal lattice, and transfer the finite
product to `ℝ≥0∞` without losing positivity or finiteness. For the
counting-quotient integration identity, use the restriction-pushforward
and periodization construction in `RationalAdeleFundamentalDomain` and
`FundamentalDomainQuotientMeasure` as the model. This is the missing
bridge from the local scales, Definition A.3.1.2 and Lemma A.3.1.3,
PDF p. 556, to Definition A.3.1.1, PDF p. 555, not an $S$-local
normalization assertion. Inversion for the ramified Gaussian and GRH
remain separate open obligations.

### Global counting-quotient normalization for the box Fourier measure

This checks the global bridge from Definition A.3.1.2 and Lemma A.3.1.3,
PDF p. 556, to the counting normalization in Definition A.3.1.1, p. 555.
It uses the actual additive adeles and their actual diagonal quotient,
for every number field. It is not the $S$-local equality of A.3.1.3.
Source readings are provisional: They use the pinned Markdown and numbered
PDF layout (PDF SHA-256 `e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5`),
not independent rendered-page inspection.

- **Geometry and repair.** Definition A.2.1.1 and Lemma A.2.1.2(1),
  p. 545, supply the product form (A.2.1.2) and the intended translate
  cover (A.2.1.3). The absolute values in (A.2.1.1) do not give unique
  reduction in signed real coordinates; the printed $r_1+r_2$ index
  is also too short for coordinates in an integral basis when $r_2>0$.
  Use the full signed real half-open cube $[0,1)^{[K:\mathbb Q]}$ in the
  real extension of the integral basis, consistent with the argument
  in Lemma A.2.4.2(2), p. 554. At a finite adele, the unit-box diagonal
  coset specifies all reductions modulo $\mathcal O_K$. At infinity
  the basis cell then gives a unique reduction by $\mathcal O_K$.
  `adeleIntegralCell` is the image in the actual adele ring of this cell
  times the integral finite box. `measurableSet_adeleIntegralCell` uses
  the open stage embedding; `existsUnique_sub_mem_adeleIntegralCell`
  proves $\forall a\;\exists!t\in K,\ a-t\in D$. This yields
  `adeleIntegralCell_isAddFundamentalDomain` for any upstairs measure.
- **Mass, without rescaling.** In `adeleIntegralCell_mass_one`, assume
  exactly the cofinal comap interface of `adeleBox_fourier_integral`:
  for some finite $E$, the comap of $\mu$ on each stage $S\supseteq E$
  is `adeleFiniteStageHaar K S`. Enlarge $S$ to include the finite
  integer-mass exceptions. Transfer the rectangle through the actual
  stage embedding, then multiply the Archimedean trace covolume of the
  unit ideal lattice (`archimedeanIntegralCell_traceMass`) by its
  reciprocal (`finiteIntegerBox_stageMass`). This is Masullo's
  cancellation in Lemma A.3.1.3, p. 556, applied to the corrected cell.
- **Counting Weil formula.** Theorems C.4.4.3, equation (C.4.4.5),
  p. 718, and D.1.2.1, p. 747, use integration along the fibers.
  `adeleIntegralClassMeasure K μ` is $(\mu|_D)$ pushed forward along
  $\pi\colon\mathbf A_K\to\mathbf A_K/K$. Translates of the interior
  give open injective charts for Borel descent. The diagonal is discrete
  and closed; the closed coordinate box and finite integral box have
  compact quotient image and meet every class. For Haar $\mu$ with the
  same stage comaps, `adeleIntegralClassMeasure_haar_probability` proves
  that the pushforward is additive Haar of mass one. For any additive
  Haar $\mu$, `adeleIntegralClassMeasure_lintegral_counting` gives the
  nonnegative Borel Weil formula, and
  `adeleIntegralClassMeasure_integral_counting` the Borel complex
  $L^1$ formula. Both give a Borel class function, agreeing at every
  lift $a$ with the (totalized) sum $\sum_{t\in K}f(t+a)$, and its integral
  equals the upstairs integral. The complex result proves absolute
  summability for **every** lift of almost every class, not everywhere.
  The index equivalence `adelePrincipalIndex` introduces no multiplicity.
  No scale, relative Haar, or quotient is changed on the way from the
  box Fourier theorem to this probability measure.

Writer check at base `af2e69d9f26188e34fe1b98c901a5c76533edb46`, Yah session
`01a204d4-bcfe-762c-89dc-4e1088d83973`: `lake build --wfail` on
`Lemmas.ArchimedeanAdeleTrace`, `Lemmas.AdeleIntegralCell`,
`Theorems.AdeleFundamentalDomain`, `Lemmas.AdeleIntegralCellMass`,
`Theorems.AdeleIntegralCellMass`, `Lemmas.FundamentalDomainQuotientMeasure`,
`Lemmas.AdeleIntegralQuotient`, `Theorems.AdeleIntegralClassMeasure`,
`Theorems.AdeleBoxFourier`, `Theorems.FiniteBoxPoisson`, and
`Theorems.IdeleClassWeil` (use `+` for each Lake target). Fresh joint
import of the class measure, cell mass helper, box Fourier, finite box
Poisson, idele Weil, and trace character modules checked the binders
and axioms of 35 declarations, including the named endpoints above.
Only `propext`, `Classical.choice`, and `Quot.sound` were reported.
Writer checks are not exact-candidate adoption evidence.

**Exact landing evidence.** Candidate
`3b8584b048a2c6a5fa82a87612add28a89e02e02`, base
`0a7f05464e5b82cc4061852dfb039f430bfe1627`, was checked and adopted in
owning Yah session `01a204d4-bcfe-762c-89dc-4e1088d83973`. The independent
review (`UPaVyiI`, responses at child events 60, 79, and 93) covered the
geometry, mass, and counting-Weil statements and verified the final
reviewed Lean sources on first candidate `40087805f5850109404cc4e7f5449b634b469934`.
That candidate went stale. The replacement had identical Lean and pinned
build inputs. Owner events 180–194 record the source comparison, fresh
`lake build --wfail`, joint import with 35 signatures and axiom reports
(byte-identical to the owner's first check), and successful adoption.
The first check's reports and their validation are at events 167 and 169.
All reported axioms were allowed. These are scoped checks, not a project
or GRH audit.

### Additive idelic change of variables for the box Fourier measure

Lemma A.3.1.4, equation (A.3.1.4), PDF p. 556, states the image law
for arbitrary additive Haar and gives an external reference for its proof.
The Lean proof in `Theorems.AdeleAdditiveDilation` computes the ratio on
a positive compact box and uses Haar uniqueness. Source reading:
Provisional, from the pinned Markdown and numbered PDF layout.

- `archimedeanAdeleTraceMeasure_image_mul` computes the real determinant
  of multiplication in mixed coordinates, with one norm factor at a real
  place and two at a complex place. The transported trace measure is the
  same one used in stage Haar and box Fourier.
- `adeleCalibrationBox_image_idele_stage` uses local integer-ball dilation
  at the retained places and bijectivity by integral units on the compact
  tail. The chosen stage retains the finite integer-mass exceptions and
  the nonintegral coordinates of both the idele and its inverse, so the
  omitted norm factors are all one. The same comap computes both masses.
- `comap_adeleAddHaar_dilate` transports the ratio from one normalized
  restricted-product Haar to any additive Haar by uniqueness.
  `adeleAddHaar_image_idele_mul` is the image formula (even for non-Borel
  sets). `map_adeleAddHaar_dilate` uses the inverse idele to give
  the pushforward factor $|h|_K^{-1}$. In particular, it applies to the
  very measure used for box Fourier and counting quotient Weil, with
  no further change of normalization.

Exact-candidate source, joint build, signatures, axiom reports, independent
review, and adoption evidence: Owning Yah session
`01a204ec-e522-72e2-899d-3d969158c45b`. The Archimedean writer check was at
`5228df142b4bbe08f4b398e0a79abd519623e4db`, and the stage writer check at
`2986113c78beb01bce757df1e0513cb24856ebe0`. Those writer checks are not
exact-candidate adoption evidence.

### Pointwise inversion on the number-field box span

[The pointwise theorem](../../Proofs/Theorems/AdeleBoxThetaInversion.lean),
`adeleBoxSpan_theta_inversion`, proves the following for every number field
$K$, every $f$ in the complex span of `adeleBoxTensor`, and every actual
idele $h$. Let $\mu$ be additive Haar with the cofinal
`adeleFiniteStageHaar` comaps and put
$\widehat f(z)=\int_{\mathbf A_K}f(w)\overline{\psi(wz)}\,d\mu(w)$,
where $\psi$ is `numberFieldAdeleAddChar`. Both $t\mapsto f(th)$ and
$t\mapsto\widehat f(th^{-1})$ are absolutely summable over **all** of $K$,
and
\[
\sum_{t\in K^\times} f(th)
=|h|_K^{-1}\sum_{t\in K^\times}\widehat f(th^{-1})
 +|h|_K^{-1}\widehat f(0)-f(0).
\]

- **Manuscript input and scope.** Theorem 2.2.3.2, (2.2.3.2)–(3),
  PDF p. 82, invokes external adelic Riemann–Roch and uses Lemma 2.2.2.1
  for convergence; Remark 2.2.3.3 uses the counting quotient of volume
  one. `adeleIntegralClassMeasure_haar_probability` separately establishes
  that normalization for the same stage comaps. It is not another premise
  of the box theorem. We replace the invocation of Riemann–Roch at this
  point by the proofs below, only for the **pointwise box span**, not as a
  theorem of continuous functions on idele classes or for the full
  Schwartz–Bruhat space. The independent Yah reader `theta-review`
  (`GxoPgJb`, output `72ce426136af54d1cb954d6bce2b8119274ca638` in owning
  session `01a20503-084a-723f-a5ef-b59603c0635d`) verified the rendered
  p. 82 displays: (2.2.3.3) is already written on the nonzero index and
  rearranges to (2.2.3.2), with inverse norm, inverse idele, and both
  zero terms. The left-hand $f$ in $\Psi_F(g,0)$ is implicit in context.
  Other source readings here are provisional (pinned Markdown and
  numbered PDF layout).
- **Kernel and identity idele.** Equation (2.2.4.32), PDF p. 92, supplies
  the conjugated kernel of the integral; the finite indicator must act
  on the integration variable. Examples A.3.1.5–10, pp. 557–558, describe
  the local phases, product, and trace pullback. The positive finite
  standard phases in the printed product need conjugation to cancel the
  positive infinite phase on the diagonal; see the separately
  [rendered rational check](theta-inversion-q.md#rendered-sign-check-a-translated-box-breaks-the-printed-theta-identity).
  `adeleBoxSpan_diagonal_poisson` uses `finiteBox_diagonal_poisson`
  (the shifted ideal lattice and its trace dual) and
  `adeleBox_fourier_integral` (the actual integral at each diagonal
  frequency, including zero) on a generator. The span argument carries
  integrability of the kernel and absolute summability of both series
  through addition and scalar multiplication.
- **General idele.** `adeleBoxTensor_dilate` composes the Schwartz factor
  with the actual forward Archimedean dilation and multiplies **both** the
  center and scale of the finite box by the inverse finite unit. Thus
  `adeleBoxSpan_dilate` preserves the span under $w\mapsto f(hw)$.
  Masullo's image law (A.3.1.4), p. 556, gives the direct volume factor;
  `map_adeleAddHaar_dilate` gives the inverse pushforward factor on the
  same Haar. `adeleFourier_dilate` uses that factor and the inverse
  frequency $h^{-1}z$ in the conjugated pairing. Applying the identity
  result to the pullback gives both absolute full sums at $h$ and
  $h^{-1}$. The proof removes zero from each summable series and reindexes
  the nonzero terms by actual $K^\times$; neither zero term is presumed
  to vanish.

Writer base `f44dfe887421a288b8b624fed59f335d9310aa93`; the Haar dilation
prerequisite landed at `9012d9ed33a1c6be2c2a3f4793dd044f61b7d289`.
The combined writer build passed with these targets:

```sh
lake build --wfail +Lemmas.AdeleBoxDilation +Lemmas.AdeleBoxPoisson \
  +Theorems.AdeleBoxPoisson +Theorems.AdeleBoxThetaInversion \
  +Theorems.AdeleBoxFourier +Theorems.FiniteBoxPoisson \
  +Theorems.AdeleAdditiveDilation +Theorems.AdeleIntegralClassMeasure
```

A fresh joint import checked 17 signatures and axiom lists, including
all 11 new public declarations and the six direct normalization,
character, Fourier, and lattice Poisson interfaces. Each used only
`propext`, `Classical.choice`, and `Quot.sound`. This is writer evidence;
exact-candidate integration, checks and adoption belong to the owning
Yah session named above.

#### Finite local Gaussian as a principal-ball sum

[`finiteAdditiveHeckeGaussian_eq_sum_principalBalls`](../../Proofs/Theorems/FiniteAdditiveHeckeGaussian.lean)
proves, for every number field $K$, Mathlib Hecke character $\chi$, and finite
place $v$, the following equality at **all** $x\in K_v$:
\[
\Phi_{\chi,v}(x)=\sum_{i\in s}\Phi_{\chi,v}(a_i)\,1_{a_i+r\mathcal O_v}(x).
\]
Here $r\in K_v^\times$ is a single completion unit (nonzero in the field),
$s$ is a finite index set of balls, and every $a_i$ lies in $\mathcal O_v$.
In Lean the ball test is $r^{-1}(x-a_i)\in\mathcal O_v$. Neither unitarity
nor ramification is required, and both sides are zero off $\mathcal O_v$.

- **Manuscript input.** Definition 3.4.3.2(3), PDF p. 152, gives the
  integer-ring indicator (3.4.3.7), the inverse character times the
  integer-unit indicator at ramified places (3.4.3.8), and their use in
  the Schwartz–Bruhat tensor (3.4.3.9). A local integral unit has norm-one
  image under single-place idelic insertion, so the finite factor agrees
  with using the character on the norm-one classes. The description and
  the finite ramification recalled in §B.6.1.2, p. 636, do not give the
  common-scale expansion consumed by the box span.
- **Local constancy repair.**
  [`finiteHeckeRestriction_eq_one_near_one`](../../Proofs/Lemmas/FiniteHeckePrincipalUnits.lean)
  pulls a complex neighborhood of $1$ back by the continuous local
  units-valued restriction. The radius is capped at $1$, so the resulting
  ultrametric ball about $1$ in the field is a subgroup of the units.
  Its image is trivial by `complex_eq_one_of_norm_pow_sub_one_lt`:
  all powers of each element of that image lie within $1/2$ of $1$.
  `isLocallyConstant_finiteAdditiveHeckeGaussian` uses this at a
  norm-one center $x$ by applying the kernel result to $y/x$, and
  uses the clopen complement of the unit sphere for the ramified zero
  region. The unramified factor is constant on each side of the clopen
  integer ring, irrespective of the character value on uniformizers.
- **One radius and finitely many terms.**
  [`finiteCompletionTest_eq_sum_principalBalls`](../../Proofs/Lemmas/FiniteCompletionTestDecomposition.lean)
  takes a Lebesgue number of the open fibers on the compact integer
  ring. A nonzero uniformizer power has norm below both that bound and
  $1$ and gives the required scale. The closed balls of that radius are
  open, lie inside the ring for integral centers, and are the translates
  defined by the inverse-scale test. A finite subcover deduplicated by
  ball equality gives pairwise disjoint balls. At each integral point
  exactly one term contributes, and outside the ring none contributes.
  The Gaussian specialization supplies the vanishing premise directly
  from the indicators in both branches, not by assuming a value at zero.

**Evidence.** The writer base is `9f7d1847c8d41cf46f2a09283f6a947611dab03d`.
Owning check session `01a2050d-6f88-7afe-bc8b-1581241c134e` contains
writer `PbpHUJi` and independent reviewer `TNqqgXh`. The reviewer checked
both the exact local expansion and the principal-unit kernel claim, using
pinned Markdown, numbered PDF layout and raster-to-Braille glyph checks
of the p. 152 displays; this is not direct full-page visual verification.
The writer ran

```sh
lake build --wfail +Lemmas.FiniteCompletionTestDecomposition \
  +Lemmas.FiniteHeckePrincipalUnits +Theorems.FiniteAdditiveHeckeGaussian
```

and a fresh joint import with `#check @...` and `#print axioms` on all
four new declarations. Each uses only `propext`, `Classical.choice`,
and `Quot.sound`. See the owning session for the separate integrated
candidate checks and adoption decision.

The local expansion is used in the [finite-stage tensor proof](#checked-finite-stage-hecke-tensor-in-the-box-span).

#### Checked finite-stage Hecke tensor in the box span

[`adeleHeckeTest`](../../Proofs/Theorems/AdeleHeckeTest.lean) evaluates
Masullo's finite factors with any complex Archimedean Schwartz map
$\phi$ in the Euclidean mixed coordinates. For a finite set $S$ of
finite places, it is the following function on the actual adele ring:
\[
 z\longmapsto \phi(e_\infty^{-1}(z_\infty))
 \left(\prod_{v\in S}\Phi_{\chi,v}(z_v)\right)
 1_{\{w\in\mathbf A_{K,f}:\,\forall v\notin S,\ w_v\in\mathcal O_v\}}(z_f),
\]
where $e_\infty$ is `archimedeanEuclideanToAdele K`. The omitted-place
condition is part of the function, including off the stage.

- **Manuscript input.** Definition 3.4.3.2(3), (3.4.3.7)–(9), PDF
  p. 152, supplies $1_{\mathcal O_v}$ off the finite ramification set,
  the inverse-character unit test there, and the restricted tensor.
  It does not express that tensor as a finite sum of the specific
  global boxes used by the pointwise repair of (2.2.3.2), p. 82.
  The p. 152 reading is provisional (pinned Markdown and numbered PDF
  layout). See the box-span handoff above for the independent rendered
  verification of the p. 82 identity with its two zero corrections.
- **Assembly repair.** `adeleHeckeTest_mem_adeleBoxSpan` uses the
  finite local principal-ball expansion at each $v\in S$. By
  `Fintype.prod_sum`, a summand selects one center per active place and
  has scalar equal to the product of the values at those centers.
  [`exists_adeleBoxTensor_eq_stageBalls`](../../Proofs/Lemmas/AdeleStageBalls.lean)
  puts the chosen coordinates in an actual center and an actual unit
  of the finite adeles: Off $S$ the center is zero and the scale and
  its inverse are one. The resulting box indicator checks both the
  selected balls on $S$ and integrality everywhere else. Thus the
  membership is pointwise at every adele for any $S$, without
  unitarity or a Haar hypothesis.
- **Stage and idelic compatibility.** For $S\subseteq T$,
  `adeleHeckeTest_eq_of_subset` gives equality if all newly included
  places are unramified, even if a newly included coordinate is
  nonintegral: The local factor then forces the same zero as the old
  stage guard. Taking a common union gives independence of the stage
  containing all ramification, such a stage being supplied by
  `exists_finset_isUnramifiedAt`. `adeleHeckeTest_coe_idele` matches
  `ideleZetaTest K S arch (finiteHeckeGaussian χ)` on every idele,
  conditional only on equality of the two Archimedean evaluations.
  The local restriction `finiteAdditiveHeckeGaussian_coe_unit` and the
  integer-ring closed unit ball identify the finite product and guard.

**Evidence.** Writer base `024282224262c66e8aeb20a18ade8bebc664ae50`.
Owning check session `01a2051b-4cd7-7e71-b5a0-ab4e42a64c13` records
independent Yah review `tensor-review`, the exact-candidate diff and
build of `Lemmas.AdeleStageBalls`, `Theorems.AdeleHeckeTest`, and
`Theorems.AdeleBoxThetaInversion`, the joint-import signatures and
axiom check, and the adoption decision.

#### Corrected Archimedean Schwartz factor and pointwise Hecke theta inversion

[`AdeleHeckeGaussianTheta`](../../Proofs/Theorems/AdeleHeckeGaussianTheta.lean)
constructs `archimedeanHeckeSchwartz χ hχ` in
$\mathcal S(E_\infty,\mathbb C)$ for any number field and unitary Hecke
character, with the existing completion-unit measurable/Borel
instances. `archimedeanHeckeSchwartz_idele` evaluates it at
$e_\infty^{-1}((a:\mathbf A_K)_\infty)$ for **every actual idele** $a$:
It is the product of the existing `archimedeanHeckeGaussian` factors
using `ideleInfiniteCoordinates`. The construction uses the same
`.choose` terms in `realCompletionGaussianPair` and
`complexCompletionGaussianPair`, not a new pair with the same Mellin
value. `archimedeanEuclideanToAdele_symm_mixed` and the completion
extension embeddings give the coordinate equality.

- **Manuscript input and repair.** Definition 3.4.3.2(1)–(3),
  (3.4.3.3)–(9), PDF p. 152, gives the parity, Gaussian widths and
  complex prefactor, and the restricted tensor. The printed complex
  branches are $z^m$ for $m\ge0$ and $\bar z^{-m}$ otherwise. The
  [opposite-weight repair](complex-gaussian-angular.md) for the
  bilinear pairing (3.3.1.7), p. 130, conjugates those monomials and
  leaves their degrees and widths unchanged. To use the checked
  box-span Poisson argument we need a Schwartz map realizing exactly
  these repaired factors on the chosen Euclidean mixed space.
  `mixedSchwartzGaussian` composes an isotropic Schwartz Gaussian with
  the invertible block scaling $(\sqrt\pi,\sqrt{2\pi})$ and multiplies
  it by the temperate monomial product in the *unscaled* coordinates.
  Its formula holds at zero coordinates as well. The supporting
  `schwartzGaussian` factors each iterated derivative as the Gaussian
  times a temperate multilinear coefficient and requires neither
  finite dimension nor completeness of its real inner product space.
- **Pointwise specialization.** `adeleHeckeTest_archimedeanHeckeSchwartz_coe_idele`
  discharges the previous Archimedean equality premise in
  `adeleHeckeTest_coe_idele`. For its additive test $f$,
  `adeleHeckeGaussian_theta_inversion` substitutes the actual idelic
  Gaussian in the $K^\times$ sum of Theorem 2.2.3.2, (2.2.3.2), PDF
  p. 82. Unlike Masullo's appeal to Tate's formula, this specialization
  uses the proved membership of $f$ in `adeleBoxSpan K` and the checked
  inversion there. It assumes the same additive Haar $\mu$ and
  cofinal stage comaps, keeps absolute summability of **both full**
  diagonal series over $K$, and retains $|a|_K^{-1}\widehat f(0)-f(0)$.
  The finite stage $S$ is arbitrary; it need not contain the Haar
  exceptional set or the character's ramification set for this
  fixed-stage identity. To compare different stages, use the earlier
  stage-independence theorem with its unramifiedness premise.

**Writer evidence.** Base `7f60e40bea1cec5e1210f71b004b763d68d34126`;
Yah `01a20522-cddb-7b0c-a62a-3ee14581e0f1`, writer `eJBiCkP`,
`check-arch-schwartz-final`. The writer read pinned Markdown and
numbered PDF layout, not rendered pages. Independent Yah reviewer
`GjxnVNh` inspected rendered pixel crops of pp. 152 and 82, and
then verified the three exact Lean files, including the existing
choices, both zero terms and the full diagonal domains (read-only
output `7b2f1edfb28dc0b2c4a122c8ac9a6ddf07ecd8c9`). For the separate
rendered pp. 130 and 153 angular audit see the linked angular handoff.
The review and build are tied to these source hashes:

| Lean target | SHA-256 of source |
| --- | --- |
| `Lemmas.SchwartzGaussian` | `2d6f0bdb73a476af4900b4a02c00f1a17037175f039cab992934b0d38d222a97` |
| `Lemmas.MixedSchwartzGaussian` | `d577cc70dfa022c76f2a6d563e52bd76a5d01964332c2d6405396156638acf61` |
| `Theorems.AdeleHeckeGaussianTheta` | `50aa8cbd0870cf42cb64aead37b957f13e9821e6da18f60fa9c6db3d023eac10` |

The writer ran `lake build --wfail` on these three targets and
`+Theorems.AdeleHeckeTest +Theorems.AdeleBoxThetaInversion` with Lean
4.36.0 and Mathlib `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`.
A fresh joint import checked all eight new public declarations with
`#check @...` and `#print axioms`; each uses exactly `propext`,
`Classical.choice`, and `Quot.sound`. See the writer session for
complete built signatures.

**Integrated check.** Owning Yah session
`01a20522-cddb-7b0c-a62a-3ee14581e0f1` checked candidate
`1ee2d1cfbaec17c4b427f5acc549860c2c80fdee` against base
`0ec16aa411ec0b6bda96791e666ded761640c801`; adoption was stale.
The restack `91a1e59ccd12a3b51dbc5e16f8366d31ca552b0d` on
`70508bbf859d439bbed02af4b888d7fc76813ad5` had the same exact patch
and reviewed hashes. The owner reran the five-target `lake build
--wfail` and the fresh joint import in the restacked workspace
(`check-hecke-91a1e59`). All eight built signatures matched the
prior candidate and the independent review; every axiom report
listed only the three allowed axioms. The restack was adopted.

### Large-norm decay for the additive Fourier integral

Theorem 2.2.3.4(2), (2.2.3.7), PDF p. 83, needs the large-norm
bound for the **same** additive Fourier integral used in theta inversion.
The existing spatial Gaussian estimate does not establish this premise.
The following replacement obtains the estimate for each fixed member of
`adeleBoxSpan K`, which includes the repaired fixed-stage Hecke test.

1. **Actual Fourier integral.** `adeleBox_fourier_at` uses the same
   cofinal finite-stage comaps as pointwise inversion. For any actual
   additive adele frequency, it proves integrability and multiplies the
   trace-normalized Archimedean transform by the finite local integrals.
   Masullo's displayed product (2.2.4.32), p. 92, concerns a directional
   derivative under a compact-support assumption at infinity and prints
   the finite test at the frequency. The replacement uses the integration
   variable, a Schwartz factor at infinity, and the corrected conjugated
   finite factors in the global character (so the local Fourier integrals
   have positive phase). The stage contains all exceptions for the
   center, radius, frequency, and Haar normalization (Definition A.3.1.2,
   p. 556). Outside it the box is integral, the phase is one on that box,
   and the integral is one. The global integral is the old `adeleFourier`
   definition, moved unchanged to a module upstream of diagonal Poisson.
2. **Bounds on the factors.** Example A.3.1.10, (A.3.1.8), p. 558,
   gives the inverse-different support for the local *integer-ring*
   transform. `finiteBoxLocalFourierAt_eq` extends the local formula to
   scaled, translated boxes, and `finiteBox_annihilates_iff` identifies
   the support condition at an arbitrary local frequency. If $h_v$
   represents the different and $g_v$ is the box scale, then a nonzero
   Fourier value forces $h_vg_vy_v$ integral. The translation only
   contributes a phase. Since the factors are one cofinitely, one bad
   factor makes the global product zero; otherwise its modulus is
   bounded by the fixed product of centered box masses. The bound
   `exists_archimedeanTraceFourier_norm_mul_pow_le` uses the Euclidean
   Schwartz Fourier transform at trace frequency $(y_v)$ at real places
   and $(2\overline{y_v})$ at complex places. These bounds are on the
   computed integral itself, not on a substitute dual Gaussian.
3. **Fixed lattice and exponent.** Lemma 2.2.2.1(3), (2.2.2.3),
   pp. 77–78, uses finite support, and the proof (2.2.2.8)–(11),
   pp. 79–80, requires the finite coordinates of the full representative.
   With unrestricted finite coordinates even the unramified rational
   Gaussian gives arbitrarily many samples at a fixed real coordinate
   (use $g_p=p^k$ and lattice $p^{-k}\mathbb Z$). For the inference
   (2.2.3.8)–(13), pp. 83–84, `idele_periodization_rapidDecay_of_support`
   instead absorbs a fixed finite dilation into the compact norm-one
   cover used to clear denominators. The positive lower bound for the
   Archimedean unit coordinates is on the *original* cover. We use the
   scalar section of Lemma A.2.2.4, p. 547, not the section (A.2.2.11)
   chosen in the printed proof. At norm $t$ its ordinary coordinate
   dilation is $t^{1/[K:\mathbb Q]}$, not $t$ as asserted for the
   sup-norm in (2.2.3.10). An exponent larger than the lattice rank and
   at least $N[K:\mathbb Q]$ suffices. The theorem also recovers the
   previous spatial Gaussian estimate without changing its statement.
4. **Fixed box span.** `adeleBoxSpan_fourier_rapidDecay` combines these
   pointwise bounds for one box and then extends by ordinary integral
   linearity and the triangle inequality. For each $N\in\mathbb N$ it
   gives $C_N>0$ such that for all actual ideles $b$ of norm at least one,
   the series of absolute values converges and
   $\sum_{t\in K^\times}|\widehat f(bt)|\le C_N|b|_K^{-N}$.
   No uniformity on bounded families or identification with the full
   Schwartz–Bruhat space is asserted.

**Review and checking.** Owning Yah session
`01a20531-7ed6-7167-ac6c-839c1b0c8889` records the exact assembled
candidate and base, warning-failing build, fresh joint signatures and
axiom reports, and adoption result. Writer `KxuYcPr` built the six-file
arbitrary-frequency output `9984aa7ae41d568db92324ea3dd094ff2f438ed3`.
Independent Yah reviewer `mVmfYPn` audited the general support and
lattice lemma, the arbitrary-frequency fixed statements, the local
annihilator and coordinate bounds, and the exact box-span endpoint
(review outputs `fb1996783c4c6abd021397c673d56a6560bc2566` and
`40be5edb7f9b1df54ab8c19032b389bd4dfffbf3` in the owning session).
Readings are provisional from pinned Markdown and numbered PDF layout,
except for the reviewer's targeted rendering of (2.2.3.10).

The next inference is now the [zero-mode-corrected small-norm estimate
and its averaging successor](#zero-mode-corrected-theta-decay-at-small-norm).

### Zero-mode-corrected theta decay at small norm

[`adeleBoxSpan_theta_smallNorm_decay`](../../Proofs/Theorems/AdeleBoxThetaDecay.lean)
proves the fixed-test part of (2.2.3.5), PDF p. 83, on the actual
number-field ideles. Let $\Theta_f(h)$ be the $K^\times$ sum, and let
$t=|h|_K$. For every fixed $f\in\texttt{adeleBoxSpan}$ and every
$N\in\mathbb N$, it gives $C>0$ such that
$$
|\Theta_f(h)-t^{-1}\widehat f(0)+f(0)|\le C t^N\qquad(0<t\le 1).
$$
The additive Haar is the same in both inputs and has the prescribed
cofinal stage comaps. No zero-mode vanishing is assumed.

The proof on p. 83 supplies the reflection (2.2.3.7) from (2.2.3.2),
p. 82, and reduces the small-norm estimate to large-norm decay for the
Fourier sum. The checked pointwise identity `adeleBoxSpan_theta_inversion`
implements that first step. Instead of using full Schwartz–Bruhat
Fourier stability or a large-norm estimate for a substitute function,
`adeleBoxSpan_fourier_rapidDecay` directly controls the absolute mass
of the nonzero samples of this very integral. Apply it at $h^{-1}$
with exponent $N+1$ to pay for the prefactor $t^{-1}$. The bound does
not assert continuity, a result on bounded families, or full
Schwartz–Bruhat inversion.

**Evidence:** Owning Yah session `01a2053f-0c78-78bd-b245-d71dc7783365`
records independent fixed-statement review `small-norm-review`, the
exact candidate and base, build, fresh joint import and axiom reports,
and adoption decision. Source reading is provisional from pinned
Markdown and numbered PDF layout unless a rendered check is identified
in the review.

The next inference is the [counting-normalized Gaussian
average](#weighted-gaussian-decay-at-small-norm), not a generic box-span
measurability theorem.

### Weighted Gaussian decay at small norm

[`ideleHeckeGaussian_radialPairing_smallNorm_decay`](../../Proofs/Theorems/IdeleClassGaussianSmallNorm.lean)
implements the fixed-stage Gaussian case of (2.2.5.10), PDF pp. 97–98,
on the radial section, for all $t=e^u$ with $u\le 0$. Use the same
stage, measurable principal periodization $F$, and counting-normalized
norm-one Haar $m$ from
`exists_discriminantNormalizedIdeleHeckeGaussian_radialMellin`.
It supplies $m$ but not the **additive** Fourier measure: Its idele Haar
is multiplicative. Obtain the independent additive cofinal-stage Haar
from `exists_finiteCompletionIntegerMass_exceptions` and
`exists_adeleRestrictedProductHaar`, taking the comap condition from
that theorem with $\nu=\mu$. Neither Haar construction constrains the
Gaussian's choice of stage beyond the existing hypotheses. Write $P(u)$
for the norm-one pairing with the **unbarred**
restriction $\omega$ of $\chi$, and set $z_u=t^{-1}\widehat f(0)-f(0)$
for this Gaussian's additive realization $f$. Lean proves slice
integrability at **every** $u\le 0$ and, for each $N\in\mathbb N$,
$$
|P(u)-z_u\,m(C_K^1)\,\delta_\omega|
\le B_N e^{Nu}\,m(C_K^1),\qquad B_N>0.
$$

- Definition 2.2.5.1, (2.2.5.2), p. 95, gives the weighted average,
  with counting Haar specified there and in (2.2.5.7), p. 96. The
  log splitting in `ideleClassRadialPairing` implements the product of
  the section point with a norm-one class. The same product is used
  in the radial Mellin pairing (3.2.2.5), p. 125, and in the change of
  variables on p. 97 proving Lemma 2.2.5.2(1). The prose on p. 96
  interpreting $hg$ in (2.2.5.2) instead says to translate by $h^{-1}$.
  Read literally, that convention switches $\omega$ to $\omega^{-1}$
  by Haar invariance under inversion and leaves $\delta_\omega$ and the
  bound unchanged. Lean uses ordinary multiplication and the weight
  in the unfolded zeta integral; no quotient probability rescaling or
  conjugate character is used.
- The proof of Theorem 2.2.5.4(2), p. 98, uses finite Haar to preserve
  the bound (2.2.3.5), p. 83. For this inference Lean uses the existing
  Borel $F$ and checks the bound at every representative of each slice.
  `adeleHeckeTest_mem_adeleBoxSpan` and
  `adeleHeckeTest_archimedeanHeckeSchwartz_coe_idele` match the corrected
  Gaussian with `adeleBoxSpan_theta_smallNorm_decay` for the same
  additive Fourier integral. This uses the convention repair of
  `AdeleBoxThetaInversion`: The conjugated global trace kernel with
  corrected finite signs, not the literal positive finite phases of
  Examples A.3.1.5–9, pp. 557–558. No continuity assumption on $F$ or
  general Schwartz–Bruhat measurability result is needed.
- The printed estimate includes $\delta_\omega$; the proof here
  computes it explicitly. Integrate $(F-z_u)\omega$ using the pointwise
  bound and $|\omega|=1$. Left translation by $k$ multiplies the
  character integral by $\omega(k)$; it must vanish when some
  $\omega(k)\ne 1$. Otherwise the character is identically one and the
  integral is $m(C_K^1)$. The error bound has no triviality indicator.
  This is a result on radial slices, not continuity, all-class
  estimates, or bounds on families of tests.

**Evidence:** Owning Yah session `01a20546-ebfe-7af6-b8e4-93c438e74314`,
independent fixed-statement/source review `gaussian-small-norm-review`
(`VDZDFkA`). It confirms the signs, the restriction criterion, the
finite Haar scaling, and the radial scope, with the separate additive
measure and translation convention noted above.
See this session for the exact candidate and base, warning-failing
build, fresh joint signatures and axiom reports, and adoption. Source
reading is provisional from pinned Markdown and numbered PDF layout
unless a rendered check is identified in the review.

The next inference is the [entire corrected Gaussian radial Mellin
transform](#entire-corrected-gaussian-radial-mellin-transform).

### Entire corrected Gaussian radial Mellin transform

[`ideleHeckeGaussian_correctedRadialMellin_entire`](../../Proofs/Theorems/IdeleClassGaussianCorrectedMellin.lean)
uses the **same** $T,F,m=\overline\mu_1$ and idelic Gaussian as the two
weighted bounds above. Its additive test is precisely
`adeleHeckeTest χ T (archimedeanHeckeSchwartz χ hχ)`, with Fourier integral
`adeleFourier μ` for the separate additive Haar $\mu$ specified by its
cofinal-stage comaps. With $x=\log t$, write $P(x)$ for the norm-one
pairing on the section $\tau(e^x)$ and $b=m(C_K^1)\delta_{\chi|C_K^1}$.
`ideleClassCorrectedLogProfile` is
$$
p(x)=\chi(\tau(e^x))\left[P(x)-\mathbf 1_{x<0}
                (e^{-x}\widehat f(0)-f(0))b\right].
$$
Lean proves every weighted norm-one slice is integrable, $p$ is Borel,
and for every $s\in\mathbb C$ both $p(x)e^{sx}$ and $xp(x)e^{sx}$ are
absolutely integrable in $dx$. The transform is entire, with complex
first derivative the integral of the second integrand.

- The norm-one pairing (2.2.5.2), p. 95, and the radial decomposition
  (3.2.2.4)–(5), p. 125, place $\omega$ on the norm-one factor and
  $\chi(\tau(t))t^s$ outside it. Use ordinary multiplication as in the
  quotient computation on p. 97. In `ideleClassCorrectedLogProfile`,
  `Multiplicative.ofAdd x` tags $x$ itself, not $e^x$; the norm of its
  section point is $e^x$. The subtracted expression is applied to
  the pairing first; the phase has norm one but is not discarded.
- Theorem 2.2.5.4(2), (2.2.5.9)–(10), pp. 97–98, supplies the two
  weighted bounds used here. The checked fixed-Gaussian versions are
  `ideleHeckeGaussian_radialPairing_rapidDecay` on $x\ge 0$, including
  zero where there is no correction, and
  `ideleHeckeGaussian_radialPairing_smallNorm_decay` on $x<0$, using
  $e^{-x}=(e^x)^{-1}$ and the actual finite mass in the *subtracted*
  modes. The earlier correction of the finite Fourier signs is inherited;
  this step adds no Fourier inversion hypothesis. In particular, no
  conditions $f(0)=0$ or $\widehat f(0)=0$ are assumed.
- The proof of Theorem 3.2.2.1 uses the exponential estimate and
  $dt/t$ in (3.2.2.7)–(10), pp. 126–127. Its unaveraged absolute values
  cannot exploit cancellation of a nontrivial norm-one character. Use
  the modulus **after** pairing, with the correction for the trivial
  restriction even when its zero values do not vanish. The Borel
  product integrand gives a Borel slice integral by
  `StronglyMeasurable.integral_prod_right'`, using finite Haar on the
  compact norm-one group. The profile can jump at the cut. The two-tail
  helper chooses $N\ge |\Re s|+3$ and bounds $|p(x)e^{sx}|$ by
  $C_s e^{-3|x|}$. In $|w-s|<1$ changing the parameter costs at most
  $e^{|x|}$, and inserting the log moment costs at most another
  $e^{|x|}$. The measurable variant of `hasDerivAt_logMellin_of_decay`
  uses the resulting integrable majorants for Bochner parametric
  differentiation (the old continuous-profile interface is unchanged).
- `exists_discriminantNormalizedIdeleHeckeGaussian_correctedRadialMellin`
  chooses $T,F$ and the specified $m$ directly from the checked
  `exists_discriminantNormalizedIdeleHeckeGaussian_radialMellin`, not
  from a second periodization. The separate $\mu$ is obtained using
  `exists_finiteCompletionIntegerMass_exceptions` and
  `exists_adeleRestrictedProductHaar`. The **uncorrected** above-one
  integral is restated in real log coordinates by
  `map_toAdd_logVolume` (no scale factor). It equals
  $|\mathrm{disc}(K)|^{-1/2}$ times `completedHeckeEulerProduct` for
  the same Gaussian, by the existing above-one evaluation of
  (3.2.2.5), (3.2.2.11), pp. 125, 127. This is not equality of the
  corrected integral with that Euler product. The existential exports
  differentiability, not absolute convergence as a separate conjunct:
  install its `μ.IsAddHaarMeasure` as a local instance and apply the
  first endpoint with the **same** $T,\mu,E,\nu,v,r,F$ and the exported
  cofinal comaps, quotient Haar, measurability and periodization. The
  existential retains the quotient Haar and its mass, not the auxiliary
  multiplicative Haar on ideles and its splitting witnesses; those are
  in the earlier above-one theorem.

**Evidence.** Independent source and fixed-statement review: Yah session
`01a20550-d5a6-78a3-9def-ba66465b8227`, agent `WigsKzk`, report
`ac8bf85ae11152a49d5613e0f920ab0930c8eb98`, on frozen signatures SHA256
`eedd2aae55c97d102533594ce7c8c2d2651bf4dace3111b3e9b538954d494af3`.
The review confirms the ordinary-product pairing, measure and indicator,
phase, correct use of the two bounds, and coordinate transport; its
noted measurability and differentiation implementation obligations are
filled by the built `hpair` and `hasDerivAt_logMellin_of_measurable_decay`.
The review is independent of the build; both source readings are
provisional Markdown/layout readings (not visual inspection).
Writer `YjLYOPn` built all three changed Lean modules, both fixed Gaussian
tail modules, and the five direct importers of `LogMellinDerivative` with
`lake build --wfail`, then jointly imported and checked the six changed
or new declarations with complete `#print axioms` reports (only
`propext`, `Classical.choice`, `Quot.sound`). The owning integration
checks and full candidate identity are recorded by agent `main` in the
same session; writer verification alone is not an adoption check.

**Owning check.** Accepted candidate
`733c290eb19976bcb4dc15f00835ef3872bb0fc3`, on
`c6ba655a2bd4172c960654957aa0f0f4a2f8ad26`, passed `lake build --wfail`
(8613 jobs) in `integration-lVtdOuA`. The exact patch was unchanged
from both checked stale candidates. The fresh joint report for the six
reviewed declarations has SHA256
`ecf353f8e2749bbca3c76bc4de85030ca8d89bedfbac3838704c9221e8414f3c`
and contains only the allowed axioms. See `owner-entire-final-restack`
in the owning session.

### Meromorphic continuation of the fixed-Gaussian Euler product

[`exists_completedHeckeEulerProduct_gaussianContinuation`](../../Proofs/Theorems/IdeleClassGaussianContinuation.lean)
repairs the continuation in Theorem 3.2.2.1(1a),(3), PDF pp. 124–127,
for the fixed Gaussian over any number field and a unitary Hecke
character. It uses the same Gaussian, Borel periodization, separately
normalized additive Fourier Haar, and counting-normalized
multiplicative norm-one Haar as the corrected integral and Euler identity.

- Masullo supplies the twist coordinate $c=\chi|\cdot|^s$ in
  (3.1.1.1), p. 119, and the section factor $c(\tau(t))$ in
  (3.2.2.4)–(5), p. 125. Lean composes $\chi$ with the actual continuous
  log section and applies `existsUnique_unitary_oneParameterCharacter`.
  Thus $\chi(\tau(e^x))=e^{i\lambda x}$ for a real $\lambda$. Triviality
  on $C_K^1$ alone does not force $\lambda=0$.
- Equation (2.2.5.10), p. 97, gives the signs and powers of the two
  small-norm terms after pairing. For $b=m(C_K^1)\delta_{\chi|_{C_K^1}}$,
  let $a_1=\widehat f(0)b$, $a_0=f(0)b$, $z_0=-i\lambda$, and
  $z_1=1-i\lambda$. On $\Re s>1$, the corrected integrand plus the
  removed modes equals the uncorrected weighted pairing pointwise.
  `ideleHeckeGaussian_correctedRadialMellin_entire` and
  [`integral_logMellin_zeroModes`](gaussian-zero-modes.md) justify
  `integral_add`. The checked same-witness Euler identity, corresponding
  to (3.2.2.11), p. 127, then identifies
  $G(s)+a_1/(s-z_1)-a_0/(s-z_0)$ with the completed product times
  $|\mathrm{disc}(K)|^{-1/2}$, where $G$ is the entire corrected integral.
- Masullo states the zeta integral's residues in Theorem 3.2.2.1(1a),
  p. 124, invoking the general global zeta theorem on p. 126. Rather
  than assume that continuation, Lean adds the explicit rational terms
  to $G$ and multiplies **all** terms by $D=\sqrt{|\mathrm{disc}(K)|}$.
  For the resulting continuation $L$, Lean proves meromorphy everywhere,
  holomorphy off $z_0,z_1$, and entireness when the norm-one restriction
  is nontrivial. It constructs an entire $H$ agreeing with
  $(s-z_1)(s-z_0)L(s)$ off the two points, with $H(z_1)=Da_1$ and
  $H(z_0)=Da_0$. Since $z_1-z_0=1$, the residues of $L$ are $Da_1$
  at $z_1$ and $-Da_0$ at $z_0$. A zero coefficient makes the
  corresponding singularity removable; no point value at the pole is
  used for this interpretation.

**Evidence:** Owning Yah session `01a20567-4317-7598-a876-3bfb612ca5c2`
records the exact integrated candidate, warning-failing build, and
fresh joint signature and axiom check. The independent fixed-statement
and manuscript review is by agent `bSxnAsU` in the same session. Source
correspondence is provisional from pinned Markdown and numbered PDF
layout, with the already reviewed scalar signs as in the linked handoff.

**Checked strip input for §B.4.2.1 / (B.4.2.1), PDF p. 614.** Masullo
supplies the radial identity (3.2.2.4)–(5), p. 125, and the two weighted
tails (2.2.5.9)–(10), pp. 97–98. The corrected Gaussian construction
uses these after averaging and restores the removed modes for the
Euler identity. On p. 614 Masullo invokes Lang for slow growth of
$L'/L$; the strip estimate here is an input to a replacement argument,
not that cited conclusion. The bound needed on the full moving circle
is not just compact-uniform convergence of the radial integral. Lean uses the
absolute integrability from `ideleHeckeGaussian_correctedRadialMellin_entire`
for the same witnesses: the sum of the two endpoint integrand norms
majorizes the integrand on the strip, giving a uniform bound for $G$.
The polynomial formula for $H$ then gives the new conjunct, on the
**same** witness:

```lean
∀ a b : ℝ, ∃ M : ℝ, 0 ≤ M ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b →
  ‖H s‖ ≤ M * (1 + |s.im|)^2
```

No ordering hypothesis on the endpoints or exclusion of either pole is
needed; all previous hypotheses and clauses are retained. Source status
is provisional from pinned Markdown and numbered PDF layout (including
p. 614); the rendered page was not inspected.

**Acceptance evidence.** The proof landed at
`bd041db358941d519fccde5c2c734aca4dc193ba` on
`edbd681e6ecdf118e6857f053f43976451ee4328`, with Mathlib
`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. In owning Yah session
`01a2056f-8344-7f8c-ab83-1ef134597ce8`, reviewer `FgDCjGI` checked
both helper statements, the unchanged witnesses, and the exact new
same-$H$ conjunct in `a300a22099900c70f8657d8be1ed4377120d72c0`.
The replacement differs only by an unrelated manuscript note. Its
`lake build --wfail +Lemmas.LogMellinStripBounds +Theorems.IdeleClassGaussianContinuation`
and fresh joint signature, provenance, and axiom checks passed. The
full signature report matched the reviewed candidate's, and the three
endpoints use only `propext`, `Classical.choice`, and `Quot.sound`.

**Next bounded Jensen step:** Specialize to the trivial character
(identify $\lambda=0$ by uniqueness of the section phase), and prove,
for the actual same $H$, $H(c_t)\ne0$ for $c_t=2+it$ and
\[
\exists C>0\ \forall t\in\mathbb R,\qquad
\sum_{z\in\overline B(c_t,5),\ H(z)=0}\operatorname{ord}_z(H)
  \le C(1+|t|).
\]
Use the divisor on the closed inner disk to count full multiplicities,
including boundary zeros. On the radius-six sphere use $-4\le\Re s\le8$
and $|\Im s|\le |t|+6$ to obtain an envelope $M_t=C_0(1+|t|)^2$ with
$C_0\ge1$. At the center the continuation agrees with the completed
Euler product after pole clearing; use
`completedHeckeEulerProduct_one_rightLine_lower_bound` for nonvanishing
and `log_div_norm_poleCleared_completedHeckeEulerProduct_one_rightLine`
for the Jensen cost $\log(M_t/\|H(c_t)\|)$, then apply
`AnalyticOnNhd.sum_divisor_le` with radii $5$ and $6$ as in the
[rational moving-disk count](rational-explicit-formula.md#checked-multiplicity-count-in-the-moving-disk).
The checked strip estimate itself gives no zero count, slow growth of
$L'/L$, left-contour reflection, or (B.4.2.2). General reflection,
absolute convergence of the unaveraged class integral outside the
starting half-plane, and any conclusion about RH or GRH are separate.
