# Cutting the lifted kernel in the second idèle variable

**Printed passage.** Masullo, *The Music of the Primes*, §1.3.1,
printed p. 24, claim in the paragraph beginning “The advantage.”
He proposes using the restricted-product coordinates of the idèles
G = GL₁(A_F) to chop the measurable lifted geometric kernel K into
components by multiplying by indicators of domains in its second
variable y. He contrasts this with working on C_F = G/F×. The
paragraph does not yet specify the domains. This review stops before
“The formula in (1.3.1.12) teaches us.”

The [pinned PDF][source] matched SHA-256
`e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5`.
Chapter Markdown and PDF layout extraction supplied the paragraph.
Direct inspection of rendered pixel crops confirmed “restricted
product structure” and “indicator functions in the y-variable”;
raster OCR independently recovered the prose.

**What a cut gives.** For a supplied Borel domain B in G and a
measurable K, Masullo's operation is the measurable kernel
1_B(y)K(x,y) upstairs. In §1.3.2, pp. 25–26, equation (1.3.2.2)
and the displayed stratum and difference, the finite-place cuts are
provisionally read from chapter Markdown as predicates that y_v be a
unit at each place in a finite set. For that scoped reading, the
reviewer checks that each condition is clopen: The coordinate maps
are continuous, and the local unit groups are compact and open.
Finite intersections and successive differences remain clopen.

These multipliers need not descend to C_F. For a nonempty finite
set, choose a place v in it and let p be its rational residue prime.
The identity idèle passes all unit tests, while the principal idèle
p fails the test at v, but both have the same class in C_F. Thus the
indicator of that stratum cannot factor through G → C_F. This is a
check about the multiplier, not a claim that no cut can ever be
described on the quotient after orbit summation. In particular the
indicator is not of the type used in the earlier [invariant cutoff].

**Checked scope and open use.** At any fixed pair (x,y), genuine
shrinking boxes in the second variable eventually lie in a region
where a fixed clopen cut is constant. Its indicator can then be
pulled out of each sufficiently small box average exactly, wherever
the averages are defined. This reviewer calculation assumes the
shrinking property and supplies neither the limit of the uncut
average nor a uniform interchange over all cuts and skewers. The
subsequent use still needs the specified divisorial partition and
justification that its averaged pieces recombine in the orbit sum
and Haar integral of [(1.3.1.12)][mass]. The paragraph itself is a
preview of the ambient cut, not a diagonal-mass identity or a
quotient kernel decomposition. No Lean endpoint is used.

[source]: ../sources/masullo/README.md
[invariant cutoff]: post-smoothening-cutoff.md
[mass]: lifted-geometric-diagonal-mass.md
