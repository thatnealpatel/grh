# Trace-class approximation of a truncated orbital kernel

**Printed passage.** Masullo, *The Music of the Primes*, §1.4.9,
preview beginning “Because they enable us” on printed p. 31 and
ending “trace-class limits of explicit finite rank operators)” on
p. 32. Masullo proposes splitting the global convolution kernel by
the non-Archimedean unit-versus-ball strata and using the orbital
bases to express the **truncated** pieces as these limits. The
paragraph does not specify the rank-one factors, the truncations,
or the topology of the limit beyond the phrase “trace-class
limits.” The next paragraph, “As the cutoff tends to,” begins a
separate claim about evaluating the trace. Chapter Markdown and
PDF layout extraction located the passage, raster OCR checked its
wording, and direct inspection of rendered pixel crops checked
the opening, the continuation across the page break, and the
start of the next paragraph. The [pinned edition](../sources/masullo/README.md)
was verified against SHA-256
`e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5`.

**Missing operator and estimate.** At fixed cutoffs, identify the
Haar integral action of the actual signed source cut of the chosen
lift with the operator on the claimed orbital Paley–Wiener level,
using a representative-independent comparison or explicitly
specified compatible lifts. On that same space, justify trace-norm
convergence of the actual finite-rank sums. For example, a sufficient
estimate for an absolutely summable rank-one expansion is summability
of the products of the norms of the cutoff output vectors and the
convolved coefficient functionals. A Schauder expansion alone does
not give this estimate. Neither does trace-norm convergence on an
auxiliary quotient identify its trace with the averaged Haar
diagonal of the lifted shell. The latter comparison must be made
for the same cut kernel before passing to the next paragraph's
cutoff limit. See the [signed kernel cut](primary-divisorial-kernel-cut.md)
and the [common diagonal comparison](orbital-basis-trace-bridge.md).

**Scope of the later route.** The proof of Theorem 11.3.2.1,
pp. 495–496, invokes the series (11.2.2.12), p. 491. The theorem
is half-twisted with $s>1$ and support strictly above norm one;
the cited series is for the untwisted singleton-base orbital dual
and assumes $s\ge2[F:\mathbf Q]$. These readings of the hypotheses
and series are provisional, from chapter Markdown and extraction.
One still needs the transport and the trace-norm estimate at the
actual levels, in particular for the degree-zero positive-width
use in the introduction. The separate [rendered fixed-shell audit](../obligations/trace-orbital-q.md#the-right-cutoff-erases-a-fixed-shell-in-the-literal-chain)
checks that the literal extra right mask in (11.3.2.3) annihilates
the fixed shell once its index reaches $k+1$. Thus the printed
same-chain comparison cannot justify replacing that mask by the
outside-$S'$ unit mask in (11.3.2.4). This does not rule out an
expansion of the original truncated shell by another route.

**Disposition.** The proposed construction and its later application
are Masullo's. The separation of the operator comparison, summability,
and diagonal identification is the reviewer's. The passage remains
open, with no new Lean claim or evaluation of the limiting trace.
