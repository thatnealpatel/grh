# Successive differences of the primary unit loci

**Printed passage.** Masullo, *The Music of the Primes*, §1.3.2,
printed p. 26, unnumbered display after “The complement to each
stratum” and the following “where Q varies” clause. The left side
is the earlier primary locus minus the next one. The right side
unites the conditions that every old coordinate is a unit and
that every coordinate in Q is in a nonzero uniformizer shell. The
prose specifies all nonempty subsets Q of the new fiber, including
the full fiber. There is no condition at new coordinates outside Q.
Coverage here stops before the paragraph introducing αₖ.

Chapter Markdown and PDF layout extraction located the passage.
The PDF digest matched the [source pin][source]. Raster OCR of the
rendered crop confirmed the prose, and inspection of the rendered
pixels checked the order of subtraction, the outer Q index, the
old-coordinate test, and the nonzero shell index at coordinates in Q.

**Checked scope.** Use the explicit coordinate loci Dₖ from the
preceding passage: An idèle belongs to Dₖ if its components at all
places in Pₖ are integer units. Put U = Pₖ₊₁ ∖ Pₖ. For each finite
place, the union of uniformizer shells with nonzero integer exponent
is the complement of the unit group in the local multiplicative
group. Thus an idèle in Dₖ fails the next cut exactly when some
coordinate in U is a nonunit. If it fails, a singleton Q consisting
of such a place witnesses membership on the printed right side.
Conversely, a witness Q is nonempty, so the idèle passes the old
cut and fails the next one. This proves Masullo's set identity for
the explicit coordinate loci, by the reviewer's direct set argument.
The finitely many new unit tests also show that the difference is
clopen. The identity holds for any nested finite sets of finite
places on the idèle group, without a choice of S. To realize it
using the indicators defined by (1.3.2.2), retain that equation's
outside-S condition.

The displayed union is not disjoint when at least two new
coordinates can fail together. A disjoint version would require
units at all sites in U ∖ Q; the printed identity does not need
that condition. For αₖ = 1_{Dₖ}, the indicator of this difference
is αₖ − αₖ₊₁, with the opposite sign for the reverse difference
of indicators.

**Not inferred.** This argument uses the explicit coordinate
loci, not the [false ambient norm-preimage identification][norm].
For instance, at the first prime in that audit's split-prime
example, the idèle is removed by the coordinate cut but is
retained by the norm cut. The display makes no claim that its
pieces descend to the idèle class group or yield an operator
trace. No Lean statement or endpoint is supplied.

[source]: ../sources/masullo/README.md
[norm]: primary-divisorial-norm-preimage.md
