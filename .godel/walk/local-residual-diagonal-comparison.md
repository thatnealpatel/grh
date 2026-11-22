# The S-local residual diagonal comparison

**Printed passage.** Masullo, *The Music of the Primes*, §1.3,
printed p. 21, preview beginning “In this section we explain the main
ingredients,” through “and factoring through GL₁(A_{F,S}).” Masullo
proposes computing the diagonal mass of the global geometric kernel
from the diagonal mass of an S-local piece. He describes “S-local” by
support on the product of the S-ideles with the outside-S local unit
product, and factorization through the S-ideles. The support display
and factorization line were spot-checked in rendered pixel crops of
the [pinned PDF](../sources/masullo/README.md), SHA-256
`e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5`.
The prose was read in the chapter Markdown and cross-checked with PDF
layout extraction and raster OCR. The next paragraph's assumptions
about the lifted kernel are outside this passage.

**Meaning of locality.** Let $U^S=\prod_{v\notin S}\mathcal O_v^\times$
and $G_S=\mathbf A_{F,S}^\times\times U^S$. For the idelic variable in
question, read the factorization on $G_S$: Restrict the residual to
$G_S$, descend by $U^S$, and extend the pullback by zero off $G_S$.
Support on $G_S$ does not imply $U^S$-invariance there. Conversely,
factorization on *all* ideles through the projection to the S-ideles
would be incompatible with nonzero S-local support. Holding the
S-coordinates fixed, each fibre contains an idele with a nonunit at a
finite place outside S, where the supported kernel must vanish. The
restricted reading agrees with the distinction between support and
invariance in Masullo's final bullet of §1.3.2, p. 27. That later reading
is provisional, from the chapter Markdown and PDF layout extraction.

**Open diagonal comparison.** For the introductory twist $1/2$, a
nondegenerate symmetric base, degree $s=0$, a fixed norm-one isotype,
and a test supported strictly above idelic norm one, identify the
actual residual of the lifted geometric kernel and prove its outside-S
unit invariance. To reduce the global diagonal mass, recover the same
averaged Haar diagonal by unfolding with the same lift and quotient
measure, justify integration of the signed shell split and its limit,
and show that the orbital masses outside the chosen S vanish. Then
identify the residual mass with the S-unit skewered diagonal integral
of the projected kernel, using compatible averaging neighborhoods and
Haar normalization. A partition of an almost-everywhere kernel does
not by itself control the diagonal obtained by averaging. Neither the
support convention nor an asymptotic for a separately constructed
local cutoff kernel supplies these identifications.

The reduction is Masullo's preview, not a proof in this paragraph.
His §12.3, p. 514, is the advertised global-to-local comparison.
Layout extraction shows a heading and an “Include section” footnote
but no derivation before §12.4; raster OCR also places the two headings
next to each other. That is a provisional reading of the later page,
not an assertion that the argument is absent elsewhere. See the
[geometric trace audit](../obligations/trace-geometric.md) for the
conditional split of an already identified integrable diagonal and
for the difference between that split and evaluating its pieces. The
restricted factorization reading and the separation of the mass
comparisons are the reviewer's. No Lean declaration is used to
establish or refute the preview.
