# The orbital support analogy with Sarnak

**Printed passage.** Masullo, *The Music of the Primes*, §1.2.11,
printed p. 21, claim in the paragraph beginning “The fact that they
serve as the ‘equivariant supports’,” through footnote 3's callout.
“They” refers to the Archimedean classifying stacks and finite-place
one-zero quotient stacks in the preceding paragraph. Masullo says
these are equivariant supports of the orbital dual basis elements,
promises a precise treatment in Chapter 8, and likens their role to
Sarnak's Theorem 2. The phrases naming the support and the theorem
number were spot-checked in rendered pixel crops of p. 21 of the
[pinned PDF](../sources/masullo/README.md), SHA-256
`e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5`.
The paragraph was also checked by raster OCR, separately from the
chapter Markdown and PDF layout extraction. Footnote 3 cites Sarnak's
*Asymptotic Behavior of Periodic Orbits of the Horocycle Flow and
Eisenstein Series*, *Comm. Pure Appl. Math.* 34 (1981), 719–739.
The paragraph ends §1.2.11, not Chapter 1.

**Open support claim.** Let $D_{F,S}$ be the open locus of S-adeles
with at most one zero coordinate. A minimal relative support claim
for either family is that one can pull the dual basis back to
Schwartz–Bruhat distributions on the S-adeles and that every such
pullback annihilates each ambient test compactly supported in
$D_{F,S}$ off the corresponding union of one-zero strata. This
requires a specified test-to-quotient map and identification of its
dual with the basis on the introductory quotient. Norm-one
equivariance makes the support invariant but does not localize it.
Relative support inclusion would not decide support at several-zero
points or show that every proposed stratum occurs in the support.

Masullo's Theorem 8.3.0.1, pp. 387–389, uses saturated S, trivial
S-class group, and a global character unramified outside S. It
uses the later subquotients (7.3.1.5) and (7.3.4.3). In particular,
the latter has a principal-value range as numerator, so the map
from all ambient tests into it needs to be specified rather than
inferred from the subquotient notation. Even with the maps in
place, equality of functional values with those on an ambient
Schwartz–Bruhat representative supported inside the indicated
union cannot prove localization of a nonzero functional. That
union lies inside a finite union of closed coordinate hyperplanes
of empty interior. A continuous ambient function supported there
is zero. This obstruction concerns the representative argument;
it does not imply that a distribution cannot be supported there.
See the [finite support audit](finite-orbital-dual-support.md),
[Archimedean quotient comparison](archimedean-orbital-quotient.md),
and [equivariance audit](norm-one-orbital-equivariance.md).

**Scope of the analogy.** Masullo's Remark 7.1.2.4, pp. 318–321,
compares horocycle measures and their Mellin asymptotics with
S-local Mellin principal-part coefficient functionals. It invokes
Sarnak's §0, Theorem 1 in that discussion, not the Theorem 2 named
on p. 21. Support of an individual closed-orbit measure is
separate from support of a Mellin residue or a limiting measure.
To make the support analogy precise, identify the exact Sarnak
functional and the sense of its support, and establish the
relative vanishing for the corresponding adelic functional.
Neither equidistribution nor the common use of Mellin transforms
supplies that vanishing. This paragraph states no adelic
equidistribution theorem.

The comparison and the later representative argument are Masullo's.
The separation of equivariance, support, and asymptotics is the
reviewer's. Chapter 7 and Chapter 8 readings here are provisional,
from chapter Markdown and PDF text extraction, not rendered-page
inspection. Sarnak's Theorem 2 was not checked against the primary
text. No Lean declaration is used to establish or refute the passage.
