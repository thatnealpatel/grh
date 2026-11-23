# Geometric trace on arbitrarily narrow Hardy–Sobolev strips

**Status: Open.** Masullo, *The Music of the Primes*, printed p. 31,
§1.4.8, opening paragraph from “GRH is a topological phenomenon”
through “as small as we please!”. Masullo says that the geometric
side of the trace formula can be calculated intrinsically in
$W_I^{s,2}(C_F)$ for every $s\ge 0$ and every $I=[-a,a]$ with $a>0$.
The positive half-width is arbitrary; no singleton calculation or
uniform limit as $a\downarrow0$ is stated. The opening paragraph does
not specify a new test class. This review stops before “Because then,
once the geometric side is computed,” which begins the proposed
spectral inference.

Chapter Markdown and PDF layout extraction located the passage in
the [digest-verified edition](../sources/masullo/README.md). Raster OCR
checked the prose, and direct inspection of rendered pixel crops checked
the Sobolev notation and the degree condition on p. 31, the $s\ge3$
condition of Definition 10.4.3.7 on p. 473, and the “Include section”
footnote under §12.3 on p. 514. The §12.3 heading is followed by §12.4,
not by the claimed global-to-local derivation. That observation is
about this section, not absence elsewhere.

**Missing step.** Even for the introductory degree $s=0$, take the
half-norm twist, a fixed norm-one isotype, a positive-width strip,
and the Bruhat tests vanishing on $C_F^1$ used by Theorem 12.5.1.1
(pp. 519–520). Identify the global geometric operator at that degree
and width, justify the removal of the position cutoff and the
integrated Haar diagonal, then evaluate that *same* diagonal by the
signed shell split. This requires justifying integration of the split,
vanishing of the orbital tail, and identifying the averaged $S$ piece
with the normalized local Paley–Wiener cutoff limit with both polar
Mellin corrections (in the trivial norm-one isotype). The visible
§12.3 does not provide that identification. Computing the local
place distributions independently of $I$ is not a computation of
the trace of the operator on each $W_I^{s,2}(C_F)$.

The [accepted source packet](../obligations/trace-assembly.json)
checks the final comparison on p. 520, not its analytic inputs.
Definition 10.4.3.7, cited for the kernel there, assumes $s\ge3$;
its formula is not a justification of the integrated diagonal at
$s=0$. The $a=1/2$ of the later calculation is the twist, not a
restriction giving the variable strip half-width. The provisional
reading of Theorem 11.3.2.1 on p. 495 gives $s>1$ and tests supported
strictly above norm one; even its asserted local evaluation cannot
be applied as printed to the degree-zero, two-sided tests. The
[geometric audit](../obligations/trace-geometric.md) distinguishes
the local asymptotic from its use for the actual global residual.

The proposed computation is Masullo’s; the comparison of the scopes
and identification of missing steps are the reviewer’s. No new
Lean claim is made. In
[`RationalRadialStripTrace.lean`](../../Proofs/Theorems/RationalRadialStripTrace.lean),
`Masullo.riemannHypothesis_iff_rationalRadialStripTrace` characterizes
the *scalar* open-strip identity at every positive half-width for
smooth compactly supported radial tests vanishing at log-norm zero,
over $\mathbb Q$ in the trivial compact isotype. It does not evaluate
a geometric operator, supply the strip identity unconditionally, or
cover general Hecke characters and Sobolev degrees.
