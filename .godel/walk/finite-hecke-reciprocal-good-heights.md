# Selected horizontal heights for the finite Hecke reciprocal

**Status: Open at the formal scope.** In Masullo, *The Music of the
Primes*, §1.4.7, printed p. 31, the second bullet after “other
properties of $L_f(s,\chi)$ are also used” announces ordinates
$T_k$ going to both ends of the imaginary axis, with a nonzero
reciprocal $1/L_f(s,\chi)$ on $\Im s=T_k$ and polynomial growth
in $|T_k|$. Masullo attributes the method to analogues of
Titchmarsh's zeta arguments. The bullet does not specify abscissa
endpoints; the preceding use concerns boxes of fixed horizontal
width. The next bullet, about the vertical line $\Re s=1$, is a
separate input.

Chapter and appendix Markdown and numbered PDF layout extraction
located the statements in the [digest-verified edition](../sources/masullo/README.md).
Raster OCR checked the prose on pp. 31, 641, and 643. Inspection of
rendered crops checked the two-sided ordinate notation and finite
reciprocal on p. 31, the bound in (B.6.1.35) on p. 641, and the
segment in (B.6.1.45) on p. 643. The details of the intermediate
logarithmic-derivative estimates on p. 642 were read by extraction
and are provisional.

## Printed conclusion and needed estimate

Theorem B.6.1.7, pp. 641–643, (B.6.1.35), asserts for fixed
$F,\chi,S$ and every sufficiently large $H$ a single $T\in(H,H+1)$
with a polynomial lower bound for the omitted product
$D=L_{\Sigma_F-S}(\chi,\cdot)$ on $[-1,2]+iT$. Corollary B.6.1.8,
p. 643, (B.6.1.45) at $m=0$, gives a sequence at both ends of the
strip. The negative-height step passes to $\bar\chi$. Take $S$
to be the Archimedean places, optionally with the
character-ramified finite places whose local Euler factors are
$1$, to get $D=L_f$. At sufficiently large absolute heights the
possible shifted Dedekind pole does not occur. The conclusion
needed for the preview is one common $T$ per horizontal edge,
with $0<|D(\sigma+iT)|<\infty$ and
$|D(\sigma+iT)^{-1}|\le C|T|^A$ uniformly on the segment, not a
separate choice of $T$ for each $\sigma$. A segment bound is not
a bound on an unbounded horizontal line, on either vertical edge,
or for a contour limit. The appendix citation supplies a stated
segment result, not the unrestricted literal reading of p. 31.

## What still needs checking

Masullo's Titchmarsh route estimates the logarithmic derivative
on moving disks, then reduces the lower bound to a sum of logarithms
of distances to nearby zeros (B.6.1.39)–(B.6.1.44). The general
formal endpoint still needs this analysis for the continuation
of the actual Euler product: In particular, a polynomial upper
bound on the wider disks free of poles at large heights, a
positive right-hand anchor from absolute convergence, and a
selection estimate controlling the *total* logarithmic loss
from nearby zeros counted with multiplicity. The
[previous strip-growth audit](finite-hecke-polynomial-strip-growth.md)
identifies the scope mismatch in the upper-growth citation in
(B.6.1.37)–(B.6.1.38). A narrower convexity estimate does not
supply that disk bound. Just separating a chosen height from each
zero ordinate by a constant times $1/\log H$ can cost
$O(\log H\log\log H)$ for $O(\log H)$ zeros. To get a polynomial
reciprocal bound by this route, the total cost must be $O(\log H)$.
Averaging the positive logarithmic losses over a unit interval
is one way to meet that requirement. This is the reviewer's
scope and proof-interface comparison, not a check of all the
appendix's analytic inputs or its derivative claims.

The accepted Lean declaration
`Masullo.analytic_good_heights_of_circle_growth` in
`Proofs/Theorems/IdealClassGoodHeights.lean` uses a different disk
factorization and logarithmic averaging argument. It assumes an
entire function, a uniform positive anchor on $\Re s=2$, and
polynomial growth on moving radius-six circles, and produces a
good positive height in each specified unit interval on the
segment with abscissas $[-1/2,2]$. It does not instantiate these
hypotheses for the general finite Hecke function, handle its
possible pole, or give the full appendix interval. The same file's
`Masullo.qSqrtNegFiveDirichletProduct_good_heights` discharges
the hypotheses for the explicit product $L(\cdot,\chi_{-4})
L(\cdot,\chi_5)$. The [quadratic class denominator audit](../obligations/isotypic-good-heights-q-sqrt-minus-five.md)
explains the special argument, conjugation, and the separate
identification with the Euler product on $\Re s>1$. This is a
specialization proved by the project, not verification of
Masullo's general proof. The
[forward scalar division audit](../obligations/isotypic-forward-division-q-sqrt-minus-five.md)
separately explains why the horizontal estimate alone does not
supply the vertical-line inputs of the cited residue theorem.
No new Lean result or contour conclusion is claimed here.
