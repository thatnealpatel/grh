# The individual orbital loci in the introductory diagram

**Printed passage.** Masullo, *The Music of the Primes*, §1.2.11,
printed p. 20, claim in the paragraph beginning “The Orbital
quotients,” read with the lower-right corner of the diagram. The
Archimedean quotient is “thought of as being supported over” the fat
points $BU_v$, and the $p$-primary quotient over the finite-place
stacks $[\mathbf R_{>0}/F_v^\times]$, whose coarse spaces are loops
$\mathbf R_{>0}/N(\mathfrak p_v)^{\mathbf Z}$. The prose ends with
“for each finite place $v\in S$”; the diagram groups the finite
loci by $p$ and marks the inner coproduct with a prime. The wording
and stack formulas were spot-checked in rendered pixels of PDF
p. 20, separately from the chapter Markdown, PDF layout extraction,
and raster OCR. The PDF matches the [pinned edition](../sources/masullo/README.md),
SHA-256 `e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5`.
This follows the [middle-row support preview](introductory-stack-loci.md)
and stops before the next paragraph about the dual basis.

**Geometric check.** Let $G=\prod_{w\in S}F_w^\times$ and $N$ be
its product norm. The one-zero stratum $H_v^\times$ is the
homogeneous space $G/F_v^\times$, by deleting the $v$-coordinate.
The commuting actions of $\ker N$ and $F_v^\times$ on $G$ are
principal for the respective projections to $\mathbf R_{>0}$ and
$H_v^\times$. The norm has a continuous section on an Archimedean
coordinate, and the deletion map has a section inserting one.
Taking the quotients in the other order gives
$[H_v^\times/\ker N]\simeq[\mathbf R_{>0}/F_v^\times]$, with
$F_v^\times$ acting by the local norm (inverting that action
amounts to inverting the group variable). At an Archimedean place
this action is transitive with stabilizer $U_v=\ker|\cdot|_v$, so
the stack is $BU_v$. At a finite place its inertia is
$\mathcal O_{F_v}^\times$, and the norm image is
$N(\mathfrak p_v)^{\mathbf Z}$, giving the stated coarse circle
via the logarithm. This computes the geometric loci, regardless of
whether any functional in a specified character component detects
them. Chapter 8, p. 391, explains the primed coproduct as retaining
only the places unramified for the character.

**Open localization.** The calculation does not put the named
orbital spaces or their duals on the stacks. Specify continuous
maps on the S-adelic test space to the precise finite and
Archimedean subquotients, and show that their dual pullbacks,
restricted to $D_{F,S}$, vanish on tests off the indicated strata.
For the later Archimedean quotient this also requires accounting
for its principal-value numerator. Do not infer a model of the
whole dual just from this restriction: For example, for
$F=\mathbf Q$, $S=\{\infty,p\}$, and the trivial norm-one isotype,
the [local comparison audit](orbital-subquotient-comparison.md)
shows that evaluation at the origin descends to a nonzero
functional on the full finite orbital quotient. Its ambient
pullback is supported at the origin, outside $D_{F,S}$.

Theorem 8.3.0.1, pp. 387–388, is Masullo's later support argument
under additional hypotheses, including trivial S-class group and
a global character unramified outside $S$. Its literal replacement
by an ambient Schwartz–Bruhat function supported in the one-zero
union cannot furnish this step: The union has empty interior in
the S-adeles, and a nonzero continuous function is nonzero on an
open set. A test on a stratum, a distribution supported on a
stratum, and an ambient test function supported there are different
objects. The Chapter 8 readings are provisional, from Markdown and
PDF text extraction, without rendered-page checks. The localization
preview is Masullo's; the quotient calculation and the distinction
between support notions are the reviewer's. No Lean declaration is
used to establish or refute the passage.
