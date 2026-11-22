# The S-local remnant of the lifted geometric kernel

**Printed passage.** Masullo, *The Music of the Primes*, §1.3.2,
printed p. 27, final bullet on the S-local remnant, beginning “As
$k\to+\infty$.” The bullet says a remnant $k_{S,\varphi}$ of the
lifted geometric kernel is supported on
$(\mathrm{GL}_1(\mathbf A_{F,S})\times U^S)\times
\mathrm{GL}_1(\mathbf A_F)$, with $U^S=\prod_{v\notin S}\mathcal
O_v^\times$. It asserts $U^S$-invariance in the same variable:
Masullo calls it the first variable and explicitly says this is $y$,
listed second. He proposes evaluating the remnant's diagonal mass
by an analog of (1.3.1.12) and a Connes-style local trace calculation.
The section on the Shell structure starts a separate passage.
Chapter Markdown and layout extraction located the bullet. Raster
OCR checked the prose, including the variable convention and the
reference, and direct inspection of the rendered support display
checked the order and grouping of its factors in the [pinned PDF],
SHA-256 `e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5`.

**What the indicators give.** Use the explicit coordinate-unit
predicates of p. 26, not the ambient idèlic norm preimage. Let $G_S$
be the subgroup of idèles that are units outside $S$. If the blocks
exhaust the finite places **outside** $S$, as the disjointness in
(1.3.2.2), p. 25, suggests, the decreasing unit masks $\alpha_k$
converge pointwise to $1_{G_S}$. With $\alpha_0=1$, adding the first
$k$ signed cuts $(\alpha_{j+1}-\alpha_j)K$ to the lift $K$ leaves
$\alpha_k K$. The coordinate-mask limit is thus $1_{G_S}(y)K(x,y)$.
The literal first-$k$ rational primes wording on p. 26 does not
exclude primes with places in $S$. If all primes are tested, the
intersection instead requires units at **all** finite places. It is
still contained in $G_S$, but does not exhaust the intended residual
locus when $S$ includes finite places. See the [p. 26 audit] for the
difference between the two notions of unit predicate.

**What the indicators do not give.** The mask is itself invariant
under $U^S$, but on $G_S$ the invariance of the masked kernel is
exactly that of $K$ in $y$. For the lift from p. 24 this requires
control of the actual lifted test and spectral indentation weight,
not just invariance of the quotient test or simultaneous principal
invariance of the lift. Even for an invariant quotient spectral
kernel, its indentation factor must be controlled. The required
step is to prove the invariance for the chosen lift, or identify an
invariant replacement and show that it preserves the same
regularized diagonal mass. Only then is the masked variable's
restriction to $G_S$ a pullback from the $S$-idèles, extended by zero
outside $G_S$. Any descent in the other variable also needs its
specified orbit recovery. Neither descent follows from support.

**Missing diagonal comparison.** Clopen masks commute with taking
pointwise limits of genuinely shrinking averages at the sampled
pairs, when those limits exist. Passing to the integrated sum needs
the absolute integrability of the actual skewered values or another
limit estimate, not just telescoping. With the former bound the
[conditional split] gives absolute summation after averaging, with
the sign dictated by the cuts. It still does not show that the
omitted orbital masses vanish or that the remnant's skewered Haar
integral equals the integral for a local operator. For the
introductory half twist, positive-width symmetric base, degree
$s=0$, and fixed norm-one isotype with test supported strictly above
norm one, compare the same averaged remnant with the $S$-unit orbit
sum using compatible boxes and quotient measures. Then identify
its scalar mass with the cutoff limit for the local Paley–Wiener
operator, with the prescribed normalization, and account for the
two Mellin corrections in the trivial-isotype comparison. An
asymptotic for a separately constructed local operator does not
supply this bridge.

In §12.3, p. 514, layout extraction and raster OCR show a heading,
“Include section” footnote, and the next heading, not a derivation
of the comparison. This later reading is provisional and does not
rule out a derivation elsewhere. The [geometric audit] separates
Theorem 12.4.1.1's normalized local cutoff calculation from that
bridge. The [trace assembly reading] confirms that p. 520 invokes
the local theorem for the remnant mass, taking that mass to be the
local side less the two Mellin values. That reading checks what is
invoked, not the invocation's validity.

The strategy and locality claim are Masullo's. The mask limit and
separation of the invariance and diagonal obligations are the
reviewer's, using the existing conditional split. This is an open
finding. No Lean endpoint identifies or refutes the remnant as
printed.

[pinned PDF]: ../sources/masullo/README.md
[p. 26 audit]: primary-divisorial-norm-preimage.md
[conditional split]: skewered-mass-piece-sum.md
[geometric audit]: ../obligations/trace-geometric.md
[trace assembly reading]: ../obligations/trace-assembly.json
