# Scope of the function-field trace comparison

**Printed passage.** Masullo, *The Music of the Primes*, §1.7.1,
printed p. 34, third bullet, closing paragraph from “A similar
phenomenon is at play here” through “the subject of the next bullet
point.” The paragraph applies the preceding analogy to the paper's
own spaces: The direct positive-characteristic analogues yield at
most an analogue of the Lefschetz trace formula, which, Masullo says,
is not enough to prove the Weil bound even for curves. He contrasts
this with the number-field spaces and previews the next bullet. That
bullet is outside this passage.

**Source check.** The [pinned PDF](../sources/masullo/README.md) matched
SHA-256 `e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5`.
Chapter Markdown and PDF layout extraction located the paragraph.
Raster OCR of p. 34 checked its wording and boundary, and direct
inspection of rendered pixel crops spot-checked “anything more than”
and “insufficient to establish the Weil bound.” The readings of the
forward locators below are provisional from extraction.

**What the obstruction would have to show.** Section 14.2, printed
p. 534, identifies a shared-pole phenomenon for the untwisted curve
zeta function. A closed point of degree $d$ contributes the factor
$(1-q^{-ds})^{-1}$, which has a simple pole at each common point
$s=2\pi i n/\log q$ on the exponent plane. A finite product over $m$
closed points thus has order $m$ at such a point. This local pole count
does not prove that a correction to the *operator* must retain pole
orders growing with $m$. The open step in the paragraph beginning
“Such correction enables the deconstruction of the global geometric
kernel” is to show, for the direct analogue of the stated Sobolev
construction and its cutoff comparison, that the needed corrections
really require unbounded orders of evaluation at the same point,
that the excess orders cannot be absorbed continuously in the fixed
Sobolev space, and that the resulting infinite-order vanishing
condition forces the relevant holomorphic component of the test to
vanish. The identity theorem gives only the last implication, once
all the derivative conditions are known.

**What the alternative trace would have to show.** Section 14.2,
printed p. 535, from “An analog of the trace calculation” through “It
would recover Weil’s own Explicit Formulas only,” proposes a different,
non-normable topology. The open step there is to specify the operator
and topology, justify the limit giving the trace, and identify its
spectral side with the explicit formula without a restriction to
critical-line zeros or an input that already assumes the Weil bound.
A bare Lefschetz identity expresses point-count errors as traces of
Frobenius powers. It supplies no absolute-value bound on individual
eigenvalues by that description alone. The distinction is between
recording a spectrum and bounding it, not between having spectral
data and having none. Failure of the proposed Sobolev route would not
show that no other use of these spaces can prove the bound.

**Number-field preview.** The fourth bullet on pp. 34–35, especially the
paragraph beginning “This Theorem has nothing to do with the zeros,”
invokes prime-logarithm independence through polar multiplicity to
select regularity making the coefficient functionals continuous.
Separation of two local pole lattices is not itself that continuity
estimate or a geometric trace computation. This preview does not
certify either step.

**Disposition and provenance.** Open as printed. The methodological
comparison, shared-pole argument, and proposed replacement trace are
Masullo's. The separation of the finite pole count from a necessary
operator correction, and of a trace identity from a spectral bound,
is the reviewer's scope analysis. No matching Lean statement was
found in the inspected proof tree at
`b5269d20c97d233c924b199d6670244f012036f7`. Neither a general
impossibility theorem nor an analogous function-field trace has been
checked here.
