# The orbital bases and the common trace diagonal

**Printed passage.** Masullo, *The Music of the Primes*, printed p. 31,
§1.4.9, opening paragraph, from “The Orbital Bases are the crux of the
matter” through “the S-local piece of the Trace Calculation.” Masullo
previews the use of the orbital bases to connect the spectral side to
the $S$-local computation. The paragraph states no operator identity,
convergence topology, or new test or Sobolev hypotheses. This review
stops before the next paragraph, beginning “Because they enable us.”
The chapter Markdown and PDF layout extraction located the passage;
raster OCR checked the wording, and direct inspection of rendered
pixel crops checked the heading, bridge sentence, and start of the
next paragraph. The [edition](../sources/masullo/README.md) was verified
against SHA-256
`e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5`.

**Open comparison.** The bases are for auxiliary orbital subquotients,
not by themselves bases of the global spectral quotient. Even in the
introductory degree-zero case, fix twist $1/2$, a positive symmetric
half-width, and a norm-one isotype. Identify the cutoff orbital operators
on the Paley–Wiener levels with the actual signed shell cuts of the
lifted geometric kernel, in a sense that permits taking the averaged
Haar diagonals and removing the cutoffs. Then justify integrating the
shell split, discarding the orbital tail, and identifying the surviving
$S$ piece with the normalized local cutoff limit, with the two polar
Mellin subtractions in the trivial isotype. The spectral calculation
must evaluate that **same** global diagonal for the same width, Bruhat
test vanishing on $C_F^1$, and Haar normalization. Agreement of a scalar
orbital trace with a Poisson sum cannot supply either identification.

The [geometric audit](../obligations/trace-geometric.md) distinguishes
these interfaces. In particular, on the provisional extraction reading,
Theorem 11.3.2.1 (p. 495) assumes $s>1$ and support strictly above norm
one. It is not a degree-zero comparison on the two-sided test class.
The [accepted reading of pp. 519–520](../obligations/trace-assembly.json)
records the final algebra under the two evaluations of a single
integral; it does not validate either evaluation. The
[degree-zero spectral audit](degree-zero-narrow-strip-spectral-trace.md)
records the separate projection and cutoff obligation. The bridge is
Masullo’s proposed strategy; distinguishing its two identifications
and their scope is the reviewer’s audit. No Lean result is used to
establish or refute this preview.
