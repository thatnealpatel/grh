# Norm time at the one-zero strata

**Printed passage.** Masullo, *The Music of the Primes*, §1.2.11,
printed p. 21, claim in the paragraph beginning “With respect to the
semigroup action” and ending at the second “as predicted by Deninger.”
For the semigroup $\mathbf R_{>1}$, the Archimedean stacks $BU_v$ are
said to be “points of attraction” and the finite-place stacks
$[D_{S,v}/\mathrm{GL}_1(\mathbf A_{F,S})^1]$ “periodic.” The tests and
norm action are introduced in the [preceding paragraph](norm-time-test-descent.md).
The following analogy about equivariant supports is a separate passage.
The [pinned PDF](../sources/masullo/README.md) matches SHA-256
`e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5`.
The strict inequality was checked in the rendered pixel crop of p. 21;
the prose was checked by raster OCR, separately from the chapter
Markdown and PDF layout extraction. The reprise in §8.4, p. 392,
explicitly names left translation on the coarse space and includes the
identity in the semigroup. Its prose was cross-checked by raster OCR;
its formulas were read from extraction.

**Fixed and periodic coarse orbits.** Use the subspace topology on
$D_{F,S}$ from §1.2.11, and the quotient topology on coarse orbits. Let
$G=\mathrm{GL}_1(\mathbf A_{F,S})$, $N$ its product norm, and $H=\ker N$.
The stabilizer of the point $e_v$ with all coordinates one except a
zero at $v$ is the coordinate subgroup $F_v^\times$. The coarse
one-zero stratum is therefore $N(G)/N(F_v^\times)$; see the
[individual loci](individual-orbital-loci.md). Norm time $t>0$ acts
by multiplication by $t$ on this quotient. The section of the norm
in an Archimedean $v$-coordinate acts trivially on the stratum with
that coordinate zero, so the coarse point is fixed. At a finite
place $v$, set $q_v=N(\mathfrak p_v)$. The positive log-time returns
are exactly the positive integral multiples of $\log q_v$, not just
returns deduced from preservation of the stratum. This checks
periodicity on coarse orbits (return up to isomorphism on objects),
not the action on any orbital dual.

**Fixed is not forward attracting.** The product
$x\mapsto\prod_{w\in S}|x_w|_w$ extends continuously by zero at the
one-zero strata and descends to a continuous function on the coarse
space. For an all-nonzero point of norm $r>0$, the norm along the
forward left action is $tr$, not $r/t$. Thus its orbit as
$t\to\infty$ cannot tend to any one-zero stratum, even in a
non-Hausdorff coarse space. Every neighborhood of $[e_v]$ meets the
all-nonzero stratum. For Archimedean $v$, this is witnessed by the
section in the $v$-coordinate, with local absolute value tending to
zero. It also exhibits convergence in *reverse* norm time: For any
all-nonzero $x$, multiplying its $v$-coordinate by that section at
$t\downarrow 0$ tends to the point with the same other coordinates
and zero at $v$, which represents $[e_v]$. This is not convergence
along $t\to\infty$ in the printed semigroup. Restricting the support
of a test changes neither the point action nor this limit. The other
one-zero strata are separately closed and invariant in the coarse
space, so they do not supply a forward basin either.

**Disposition.** The paragraph is open at its printed scope. An
ordinary forward-attraction interpretation conflicts with the
left action in the manuscript's topology. To justify a different
interpretation, specify an inverse-time convention or another
precise notion of attraction, show that it is the one used in the
comparison, and identify the particular Deninger prediction and
match its actions, fixed points, and periods. Reversing the action
would be a change, not a proof as printed. Deninger's source was not
checked here. The preview and its reprise are Masullo's. The
period and direction calculations are the reviewer's. Masullo's
Propositions 8.2.0.4(1), 8.2.0.5, and 8.2.0.6(1), pp. 386–387,
address the finite-place norm slice, Archimedean transitivity, and
closure of the norm section, respectively. Those readings are
provisional from chapter Markdown, not rendered-page checks; the
closure result does not give a forward-time limit. No Lean
declaration is used.
