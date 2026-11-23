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

## The use of Connes's local calculation in §1.5.1

**Status: Open.** Printed p. 32, preview from “The calculations in
Connes’ S-local trace formula” through “and much expanded.” Masullo
says those calculations are used to compute the diagonal mass of
$k_{S,\varphi}$ and that he expands observations from Connes's paper.
This previews the evaluation of the residual itself, not merely its
separation from the global kernel. It gives no normalization, cutoff
regime, or new test hypothesis. The next sentence, on the singleton
strip, is a separate claim. The chapter Markdown and layout extraction
located the prose; raster OCR and direct inspection of rendered crops
of the digest-verified PDF checked the attribution and kernel notation.

In the proof on p. 520, Masullo invokes Theorem 12.4.1.1 for this
mass, subtracting the two polar Mellin values from the local sum, as
recorded in the [source reading](../obligations/trace-assembly.json).
The theorem on p. 514 describes a different object: A normalized
cutoff Paley–Wiener diagonal integral on $J_{F,S}$, with the term
$\varphi(1)\log(\lambda\lambda')+o(1)$ in (12.4.1.3). The
normalization, local kernel, and cutoff terms were spot-checked in
rendered crops. Even granting that local asymptotic, at the introductory
half twist, positive symmetric strip width, degree zero, and a fixed
norm-one isotype with test supported strictly above norm one, the
missing step is to compare the actual averaged residual on $C_F$
with that local cutoff limit. Show the descent of the chosen lift with
compatible diagonal averages and Haar normalizations, justify removal
of the cutoffs in this comparison, and derive the two polar Mellin
subtractions in the trivial isotype. Vanishing of $\varphi(1)$ kills
the logarithmic term, not the polar Mellin values.

The local adaptation and its application on p. 520 are Masullo's;
§12.4 attributes the underlying calculation to Connes and its reprise
to Meyer. This checks the attribution in Masullo's manuscript, not the
original papers or the validity of the operator comparison. No Lean
statement is invoked.
