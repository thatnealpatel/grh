# The finite orbital trace tail still needs the global Mellin trace

**Printed passage.** Masullo, *The Music of the Primes*, §1.2.9,
printed p. 19, claim beginning “If φ is fixed and compactly
supported over (1, +∞),” including the “In other words” restatement.
The test eventually lies in the relatively compact norm bands
$(1,q_v)$ as the residue characteristic grows. Masullo concludes
that the traces just computed vanish at all but finitely many
finite places. The scope and conclusion were spot-checked in
rendered pixels from PDF page 19; the full paragraphs were read in
the chapter Markdown and checked against PDF layout extraction
and raster OCR. The [pinned edition](../sources/masullo/README.md)
was verified against SHA-256
`e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5`.

**Finite exceptional set.** For a fixed compactly supported test
strictly above norm one, take a finite $B>1$ bounding the norms of
its support. If $p>B$, then $q_v=p^{f_v}\ge p>B$ simultaneously
for every $v\mid p$, so no norm in $q_v^{\mathbb Z}$ belongs to
$(1,B]$. The finitely many rational primes at most $B$ have only
finitely many places altogether above them. This makes the
simultaneous quantifier in the [preceding support argument](orbital-support-vanishing.md)
unambiguous: It kills the entire scalar sum indexed by $p$, not
merely one term chosen at some $v\mid p$. In the fixed-character
Mellin sum the same bound makes the whole sampled norm fibres
disjoint from the support. Ramified places have no Euler zero
lattice. One does not need the printed point-sample formula.
The norm bands are relatively compact by the compactness of $C_F^1$
and the continuous norm section: The closed band is the image
of $C_F^1\times[1,q_v]$ under multiplication using that section.
The readings of Lemma A.1.3.4(3) and Theorem A.1.4.3(1), p. 542,
are provisional from the appendix Markdown.

**Open operator step.** The finite-tail inference is Masullo's;
the simultaneous bound and its application to the character-weighted
fibre formula are the reviewer's. For the conclusion about actual
operators, the [p. 18 claim](global-orbital-mellin-trace.md) still
needs nuclearity and identification of the trace with the stated
Mellin sum on the intrinsic global two-zero-moment isotype modulo
the actual introductory principal-value range. This scalar check
does not identify a geometric kernel diagonal with that trace.
The [Lean finite-place restriction audit](../obligations/finite-place-support.md)
concerns vanishing of the entire test pullback along each omitted
single-place inclusion. It does not identify or evaluate the
operator traces on the $p$-primary quotients. No Lean declaration
resolves the printed claim.
