# Adelic double cosets and the bundle-stack analogy

**Printed passage.** Masullo, *The Music of the Primes*, §1.7.1,
printed p. 34, third bullet from “I would like to offer an analogy”
through “Geometric Asymptotics by Guillemin and Sternberg [GS].” For
$F=k(X)$ and $G$ connected reductive over the finite field $k$, (1.7.1.2)
displays $G(F)\backslash G(\mathbf A_F)/K$. Masullo also displays
$\mathrm{Bun}_G(k)\simeq G(F)\backslash G(\mathbf A_F)/K$ without
specifying $K$ there or saying whether the left side denotes isomorphism
classes. He motivates using stack geometry by citing Laurent Lafforgue's
use of shtuka cohomology and Weil II, and contrasts this with the smooth
function spaces supplied by the Archimedean factors in the number-field
case. This finding stops before “A similar phenomenon is at play here,”
which makes a separate claim about the manuscript's own function spaces.

**Source check.** The [pinned PDF](../sources/masullo/README.md) matched
SHA-256 `e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5`.
Chapter Markdown and PDF layout extraction located the passage. Raster
OCR checked the text, and direct inspection of rendered pixel crops
checked both displays, the absence of a level specification in the
displays, and the boundary before the next paragraph.

**Scope of the identification.** The usual unlevelled interpretation
uses $K=\prod_v G(\mathcal O_v)$ for the constant group scheme on $X$.
The gluing description starts by choosing a trivialization over $F$ and
integral trivializations over the completed local rings $\mathcal O_v$;
changing the choices yields the left rational and right integral
actions. To use this description as an identification of all bundle
classes, one needs the trivializations for the stated $G$ and the
corresponding gluing result. In particular, coverage of all classes
requires generic triviality, not just the construction starting with a
generically trivial bundle. Changing the level need not give the same
bundle moduli problem. The double-coset set records orbits, not
stabilizers: For $G=\mathrm{GL}_n$, $n\ge 2$, the trivial bundle has
nontrivial automorphisms even though its class is one element of the
set. A groupoid interpretation needs the action groupoid or equivalent
automorphism data, and the stack over varying bases is further data. The
set-level display is not itself a construction of that geometry.

**Disposition and provenance.** The analogy and appeal to Lafforgue are
Masullo's. The level, trivialization, and groupoid distinctions above
are the reviewer's scope analysis, not a checked bundle correspondence.
Likewise, the usual smooth test spaces use a specified level and
smoothness on the real or complex group factors; their existence does
not show that no additional structure is needed for all number-field
problems. The examples motivate the contrast without proving a
necessity or sufficiency theorem. No matching Lean statement was found
in the accepted tree at `65c47377eac2080b1310073604660fd6d3f64ae1`.
The printed identification remains open as stated here; no external
historical or mathematical theorem is certified by this review.
