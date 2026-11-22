# Support and equivariance of the finite orbital dual basis

**Printed passage.** Masullo, *The Music of the Primes*, §1.2.11,
printed p. 20, claim in the paragraph beginning “We discussed what
this means,” through the sentence about the action of the S-units.
Masullo says that the dual basis elements of the S-local p-primary
orbital quotient are supported over the union of $H_v^\times$ for
$v\in S_p$, where $x_v=0$ and every other coordinate is nonzero.
He calls the basis elements derivatives of eigendistributions and
says their support “matters” only modulo the S-units. The prose and
displays were spot-checked in rendered pixels and raster OCR of p. 20
of the [pinned PDF](../sources/masullo/README.md), SHA-256
`e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5`,
separately from the chapter Markdown and PDF layout extraction.
This passage follows the [individual loci](individual-orbital-loci.md)
and ends before “This requires real work to show.”

**Basis and equivariance.** The dual basis belongs to the strong
continuous dual, not the primal orbital quotient. Masullo's later
Theorem 7.3.1.6, pp. 344–349, uses two families: The principal-part
coefficients (7.3.1.12) and the Fourier–Mellin jets (7.3.1.13)–(7.3.1.14).
It imposes trivial S-class group and the character choices in
Situation 7.3.1.1, besides saturation. Theorem 7.2.1.4, pp. 336–337,
relates the two families by Laurent multiplication in the local
functional equation. If a holomorphic family of distributions has
weight obtained from a fixed character by twisting by a power of the
norm, the weight is constant on the S-units by the product formula.
Differentiating then preserves S-unit invariance for the families in
question, provided that the jet identification and the action
convention are justified. This does not make higher derivatives
eigenvectors for all ideles, and invariance of support alone says
nothing about which invariant locus is its support.

**Open localization.** Pull the proposed basis functionals back
along the test-space projection to the exact p-primary quotient.
For the relative support interpretation, show that every pulled-back
functional vanishes on every ambient Schwartz–Bruhat test compactly
supported in $D_{F,S}$ off the union of the $H_v^\times$ for $v\in S_p$.
A pole-order test for the principal-part route is to bound the order
at each $c$ for such tests by $m_S(c)-N_p(c)$: The coordinates in
$S_p$ stay away from zero on the compact support, so their local
Mellin factors for compact-away tensor tests are entire. One must
match the coefficient and jet families to the actual quotient, with
the finite factors at ramified places and the orders at coincident
poles accounted for. The [basis audit](local-orbital-schauder-basis.md)
records the still-open quotient comparison; a check on selected
functionals does not supply the basis assertion as printed.

Masullo's later Theorem 8.3.0.1(1), pp. 387–388, uses extra hypotheses,
including trivial S-class group and a global character unramified
outside $S$. Its replacement by an ambient test supported inside the
one-zero union does not prove the needed vanishing: That union has
empty ambient interior. A distribution's support relative to the
open set $D_{F,S}$ also need not describe its support in the entire
S-adeles, where points with several zero coordinates are omitted from
the proposed loci. For example, in the full finite quotient for
$F=\mathbf Q$, $S=\{\infty,p\}$, and the trivial isotype, the
[local comparison audit](orbital-subquotient-comparison.md) shows
that the nonzero functional given by evaluation at the origin is
invisible on restriction to $D_{F,S}$. That example is about the
whole dual, not by itself an identification of a basis element.

The assertions and the cited later proof route are Masullo's. The
conditional equivariance calculation and the distinction between
relative support, ambient support, and supported test representatives
are the reviewer's. The Chapter 7 and 8 readings use the chapter
Markdown and PDF layout extraction and are provisional pending
rendered-page inspection. No Lean declaration is used to establish
or refute this passage.
