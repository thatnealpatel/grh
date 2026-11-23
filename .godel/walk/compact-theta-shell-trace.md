# Compact theta convergence is not a shell-trace limit

**Printed passage.** Masullo, *The Music of the Primes*, §1.5.1,
printed pp. 32–33, preview from “My method of trace calculation
instead rests” through “the topology of 𝒮_E(C_F).” Masullo says
he uses the bases to compute the orbital kernels and traces and
identifies their action by a weaker version of Meyer's Euler-product
convergence. He describes his version as convergence on relatively
compact subsets of $C_F$, coming from rapid decay of adelic
Schwartz–Bruhat tests. He says the bases compensate for using the
isotype Hardy–Sobolev spaces $W_I^{s,2}(C_F)$ rather than the finer
topology of $\mathcal S_{\mathrm E}(C_F)$. No particular degree,
operator convergence topology, or estimate is stated in this
paragraph. The next paragraph's novelty claim is separate.

Chapter Markdown and PDF layout extraction located the passage.
OCR of rendered pages checked its wording, and direct inspection
of raster crops spot-checked the opening, compact-set phrase, and
continuation after the page break. The [pinned PDF] was verified
against SHA-256
`e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5`.
The later readings of §1.8.1 and Theorem 11.1.2.1 below use chapter
Markdown and are provisional; the later right-mask reading comes
from the separate [accepted orbital audit].

**What compact convergence addresses.** The tensor in (1.8.1.1),
p. 39, replaces outside-$S$ full integer-ball factors by unit
indicators. For a fixed test $f=f_S\otimes\prod_{v\notin S}
1_{\mathcal O_v}$, the compact-set convergence suggested by the
preview can be understood directly on the theta sum. Cover a
compact set of classes by images of finitely many relatively
compact neighborhoods of idele lifts, using that the quotient map
is open. On the resulting compact set of lift representatives,
all finite components are units outside one finite set of places.
The finite support conditions confine the contributing principal
multipliers to a fixed fractional ideal. The Archimedean part of
the lifts is bounded and bounded away from the coordinate zeros,
so Schwartz decay gives a summable bound on that lattice,
independent of the finite set of added unit tests. For each fixed
principal multiplier the mask stabilizes uniformly on the chosen
lifts once the exhaustion includes its finitely many relevant
places. This gives locally uniform convergence for this **fixed
tensor** to the periodization with unit tests at every outside-$S$
place. This argument concerns a function on the ideles; the
infinite unit mask need not be a Schwartz–Bruhat factor on the
additive adeles. Projection to one compact norm-one isotype is
compatible with this compact convergence by averaging on compact
norm-one translates.

**What the trace comparison still needs.** Theorem 11.1.2.1,
pp. 480–483, concerns cutoff closures on the zero line with
$s\ge2[F:\mathbf Q]$; its proof of (3) uses weighted $L^2$ convergence
of periodizations of a fixed input above the lower norm cutoff.
Even fixed-vector norm convergence does not identify the
intersection of the closed images or give a trace limit. In
particular the orbit bases describe auxiliary orbital
subquotients. Identify the operator of the actual cut shell on
compatible representatives with the basis operator on its
Paley–Wiener level, and justify a limit that permits both taking
the trace and recovering the averaged Haar diagonal of that
same shell. The degree and half-twist actually used must be
checked, rather than transferring the zero-line estimate to
positive-width degree zero. The [accepted orbital audit] checks
that the literal second-variable mask in (11.3.2.3), p. 495,
eventually kills the fixed shell in the same chain, rather than
approaching the outside-$S'$ unit mask of (11.3.2.4), p. 496.
Rebasing on $S'$ could preserve that cut but would still need the
operator and trace comparisons. See also the [cutoff trace audit].

The method and comparison with Meyer are Masullo's. The
fixed-tensor explanation and distinction from the operator
limit are the reviewer's. The trace preview remains open; no
Lean declaration proves or refutes it here.

[pinned PDF]: ../sources/masullo/README.md
[accepted orbital audit]: ../obligations/trace-orbital-q.md#the-right-cutoff-erases-a-fixed-shell-in-the-literal-chain
[cutoff trace audit]: orbital-cutoff-trace-limit.md
