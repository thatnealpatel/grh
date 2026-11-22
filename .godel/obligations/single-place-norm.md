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

## Next normalization step: Split the Archimedean log measure

In the weighted log coordinates of (A.2.3.3)–(A.2.3.5), p. 548,
prove that $x\mapsto (\sum_v x_v,(x_v)_{v\ne w_0})$ sends product
Lebesgue measure to Lebesgue measure in the norm coordinate times
product Lebesgue measure on `logSpace K`. There is no scalar factor:
First split off the `w₀` coordinate via Mathlib's
`volume_preserving_piEquivPiSubtypeProd` and `volume_preserving_piUnique`.
For a fixed retained tuple the remaining change adds its sum to the
`w₀` coordinate. Use `MeasurePreserving.skew_product` with translation
invariance of real volume. This separates the norm direction without
introducing Euclidean hyperplane surface measure.

Then combine this splitting with the real and complex local coordinate
identities. The half-open lattice box must have measure
`NumberField.Units.regulator`; the angular torsion slice must still be
shown to give exactly $1/w_F$ of the angular mass, with one representative
per orbit and counting measure on the units. These steps and the global
quotient comparison remain open.
