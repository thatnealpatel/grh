# The Archimedean orbital preview and its later scope

**Printed passage.** Masullo, *The Music of the Primes*, printed p. 19,
§1.2.10, opening preview through “We fix ideas on the S-local ones for
simplicity.” The heading sentence says the Archimedean Schauder bases
will not be used but are worth mentioning in connection with Deninger’s
program. The next paragraph announces an Archimedean analogue of the
“Orbital Trace Formula from §3.2” and orbital subquotients at both the
S-local and global levels. The §3.2 citation and the local/global scope
were spot-checked in the rendered pixels of the pinned PDF, separately
from chapter Markdown, PDF text extraction, and raster OCR. Printed p. 19
is PDF page 19 of SHA-256
`e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5`.
This review ends before “These are denoted” and the local definition.
The stated non-use is the author’s signpost, not a completed audit of
later uses.

**Where to look, and what does not transfer.** The literal §3.2,
“Global Idelic Zeta Functions,” pp. 122–128, treats Hecke L-functions
and global idelic zeta integrals and does not supply the cited orbital
trace formula. The later relevant S-local construction is Notation
7.3.4.1, p. 364, (7.3.4.3): Its numerator is the image of the finite-place
principal-value product on the full S-local theta isotype, not the full
isotype used in the introduction. Its denominator is written with the
chapter’s S₀₀ test space on all the S-adeles. The global quotient in
(7.4.3.13), p. 372, instead starts with the global two-zero-moment theta
isotype. Theorem 7.4.3.2(2), pp. 372–373, gives a *matrix trace* on that
global quotient for tests on C_F supported over norms greater than one.
Its formula (7.4.3.14) subtracts a term on the trivial norm-one isotype.
These later readings are provisional, from chapter Markdown and PDF text
extraction, not rendered-page inspection.

**Disposition.** This is an overview, not a checked theorem. Masullo
makes the preview and states the later results. The source and scope
comparison is the reviewer’s. To use those later results as evidence for
the introductory S-local trace, one still needs a comparison on the
actual quotients that intertwines the test-function actions and justifies
the trace on the local basis, including the treatment of the trivial
isotype. Neither the shared notation nor the global trace statement
provides that comparison. No Lean declaration is used. The local
quotient, its claimed closed denominator, and its matrix trace will
require their own passage reviews.
