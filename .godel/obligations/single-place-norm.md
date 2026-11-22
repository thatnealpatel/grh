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

**Next: Strictness in (A.2.3.23)–(24), p. 552.** Identify
`(ideleFiniteUnits : Set (IdeleGroup (𝓞 K) K))` with the range of
`ideleFiniteStageEmbedding K ∅`. The accepted range formula uses both an
idele and its inverse; show this is equivalent to local valuation one.
`isOpenEmbedding_ideleFiniteStageEmbedding` then gives an open subgroup
inside the kernel. Its translates make the kernel open, on ideles and on
the norm-one subgroup. Prove the surjections are continuous open maps
to the discrete ideal class group and the kernels have the closed
subgroup topology. The Archimedean and finite local compactness inputs
are in `Lemmas.IdeleFiniteStageMeasure`; distinguish them from the
compactness of norm-one *classes*.

The separate presentation (A.2.3.22), the compact finite unit block in
the class quotient, the Archimedean relatively compact fundamental
domain of Lemma A.2.3.8, pp. 550–551, and the global compact cover in
Proposition A.2.3.10 remain open here. The cover is needed for general
norm-one compactness (Theorem A.1.4.3(1), p. 542). The exact quotient Haar
volume (A.3.2.1), pp. 559–560, is a further obligation.
