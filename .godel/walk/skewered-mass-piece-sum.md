# Splitting the skewered diagonal mass into pieces

**Printed passage.** Masullo, *The Music of the Primes*, §1.3.1,
printed p. 24, the paragraph beginning “The formula in (1.3.1.12)
teaches us.” He proposes computing the right-hand side of (1.3.1.12)
as a sum of the same type of integral for the cut pieces of the lifted
geometric kernel, and making the pieces explicit from their action on
certain large subspaces of the global Schwartz space. He does not
specify the subspaces or a convergence argument in this paragraph.
This review ends before §1.3.2, p. 25.

The [pinned PDF][source] matched SHA-256
`e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5`.
Chapter Markdown and PDF layout extraction supplied the passage.
Direct inspection of rendered pixel crops checked the reference to
(1.3.1.12), the sum of integrals, and the last line about the Schwartz
subspaces. Raster OCR cross-checked the paragraph.

**Conditional splitting, not a trace evaluation.** Let A(x, ξ) be
the smoothened value of the actual lift at (x, ξx), for x in the
normalized domain D and ξ in F×. For a countable clopen partition
of the second idèle variable, including its residual part, genuinely
shrinking boxes give each cut the value 1_B(ξx)A(x, ξ): For any
fixed (x, ξ), each fixed cut is eventually constant on the second
box. This uses existence of the uncut limits on a single conull set
of x for all ξ. The sufficient bound for summing the masses of the
cuts is

$$\int_D\sum_{\xi\in F^\times}|A(x,\xi)|\,d\mu(x)<\infty.$$

The disjoint indicators partition this nonnegative integral, so
Tonelli bounds the sum of the absolute cut masses by the displayed
quantity. Equation (1.3.1.12) in its displayed order would only
identify the integral *after* the orbit sum. It does not by itself
supply this bound before cancellation.

For the repaired one-variable test lift, one may choose support
strictly above norm one when the quotient test has that support:
Multiply any repaired lift by a smooth norm cutoff equal to one on
the quotient test's norm support. Then its continuous convolution
term is zero on every principal skewer. If the spectral lift has the
[skewered diagonal identification][mass], the remaining value is
−w(x, ξx)d([x]), where w is the nonnegative normalized indentation
weight and d is the absolutely integrable quotient spectral diagonal.
The left side of the bound is then exactly the quotient L¹ norm of d.
The introductory spectral identification, diagonal control, and
compatibility of the boxes are still hypotheses here. For an arbitrary
lift, φ(1) = 0 only makes the orbit sum of regular terms zero; it
need not make an individual principal value of the test lift zero.

The [geometric audit] already separates the partition argument from
its evaluation. For decreasing unit loci beginning with the full
space, the disjoint shell indicators are α_k − α_{k+1}, plus the
residual indicator for idèles that are units outside S, provided the
place sets exhaust the complement of S. The residual subgroup is
clopen in the restricted product topology. The later signed pieces
α_{k+1} − α_k of (11.3.1.4), p. 494, must therefore be subtracted in
that convention rather than added. This later sign was read
provisionally from chapter Markdown. Section 12.3, p. 514, supplies
no derivation at its heading: The extraction and a raster OCR check
show the heading, footnote 1 (“Include section”), and the next heading.
This is not a claim that the comparison is absent elsewhere.

**Open identification.** The plan is Masullo's; the conditional bound
and the distinction between the two integration orders are the
reviewer's application of the accepted [cut] and [mass] analyses.
To evaluate a cut by its action on a Schwartz subspace, one still
needs to identify the actual cut kernel, or at least its averaged
skewered mass, with that of the proposed operator on the subspace.
Agreement on a named subspace alone is not kernel uniqueness. One
needs a separating family in a justified kernel space, or a direct
comparison of the masses, and convergence strong enough to pass the
trace through the finite-rank and cutoff limits. Theorem 11.3.2.1,
p. 495, provisionally read from chapter Markdown, uses degree s > 1,
Paley–Wiener levels, and a separately specified indentation. It
cannot be used directly to identify the introductory degree-zero
shells. No Lean endpoint was checked for this passage.

[source]: ../sources/masullo/README.md
[mass]: lifted-geometric-diagonal-mass.md
[cut]: second-idele-indicator-cuts.md
[geometric audit]: ../obligations/trace-geometric.md#integrating-the-stratum-split-is-not-evaluating-its-parts
