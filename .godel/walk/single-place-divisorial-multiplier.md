# The single-place divisorial multiplier

**Printed passage.** Masullo, *The Music of the Primes*, §1.3.2,
printed p. 25, unnumbered definition of ρ_v and its smoothness
sentence. The display tensors the all-one factors indexed by S,
the all-one factors indexed by w outside S with w ≠ v, and the
indicator of the integer-unit group at v. In the middle tensor the
subscript on the constant-one function is F_v, not F_w. The next
sentence calls this a smooth function on GL₁(A_F), citing compact
openness of the integer-unit group in F_v. This review stops before
the definition of ρ_T in (1.3.2.2).

Chapter Markdown and PDF layout extraction located the passage.
Direct inspection of rendered pixel crops of the [pinned PDF][source]
confirmed the distinct F_w and F_v subscripts; raster OCR confirmed
the smoothness prose. The PDF matched the SHA-256 in the source
record.

**Checked scope.** Take v finite and outside S, as required in the
subsequent use of ρ_v. As a literal tensor of functions on the
indexed local fields the middle factor has the wrong domain: At w
it must be the constant one on F_w, or its restriction to F_w× on
the idèles. One can instead read all those factors as scalars equal
to one. On either reading with that correction, the definition is
the coordinate multiplier ρ_v(g) = 1_{O_{F_v}×}(g_v).

The smoothness assertion is Masullo's. The reviewer checks it for
the corrected multiplier: Coordinate projection is continuous in
the restricted-product topology. The local unit group is open and,
being compact in a Hausdorff field, closed. Its inverse image and
complement are open, so ρ_v is locally constant, including in the
Archimedean directions, on which it does not depend. Its 1-locus is
clopen, and the formula makes it independent of every coordinate
other than v. This is a cylindrical multiplier upstairs, not a
Schwartz–Bruhat test on the full additive adèles. Its nonzero locus
projects onto an unrestricted Archimedean idèle factor, so the
multiplier does not even have compact idelic support. This check
does not identify any finite product or partition, establish descent
to the class group, or compute a diagonal integral.

Independent Yah reviewer CInTFEt (output
`3c8228064fe10c7022436de44ed4aa1382a9041a`) separately inspected
rendered crops of the page and checked the same subscript mismatch,
the corrected coordinate-pullback signature, and local constancy.
The pullback can also be defined inside S, but in that case the
first printed tensor block and the singleton v are no longer
disjoint. No Lean endpoint is used.

[source]: ../sources/masullo/README.md
