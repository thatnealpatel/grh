# Positive-degree spectral contributions at the strip edges

**Status: Open.** Masullo, *The Music of the Primes*, printed p. 31,
§1.4.8, claim in the single sentence beginning “For Sobolev degree
$s>0$” and ending “a function of the Sobolev degree $s$.” Masullo says
that the spectral side at positive degree receives contributions from
zeros on the edge lines $\{\sigma=-a,a\}$, with multiplicity capped as a
function of $s$. These are edges in the shifted variable $z=\rho-1/2$
inherited from the preceding paragraph. The sentence neither gives a
formula for the cap nor says how low degrees or equality are handled.
It does not assert existence of zeros on any particular edge. The
[degree-zero passage](degree-zero-narrow-strip-spectral-trace.md) and
the following paragraph on continuity are separate reviews.

Chapter Markdown and layout extraction located the sentence, raster
OCR checked the prose, and direct pixel inspection of crops from the
[digest-verified PDF](../sources/masullo/README.md) checked the printed
$s>0$ and the edge-line display. Rendered crops also checked the
bracketed cap on pp. 446 and 454, $s>1$ on p. 453, and the interior
restriction on p. 519. The cutoff proof comparison below is based on
extraction.

## The candidate cap needs a strict endpoint check

Masullo's Theorem 10.2.2.1, p. 446, (10.2.2.4–6), lists jets of orders
$0\le m<N_{I,s}$, with edge cap $N_{I,s}=\min(N(\rho),
\lfloor (s-1)/2+1\rfloor)$. Theorem 10.3.2.1, pp. 453–454,
(10.3.2.3–5), uses the same count in the quotient trace, but assumes
$s>1$. Its floor convention is stated below (10.3.2.4).

In the positive weighted log model, on the matching end of the log
line the squared divided kernel for an order-$m$ edge jet has density
$|x|^{2m}(1+x^2)^{-s/2}$. Its integrability needs $2m+1<s$, not
$2m+1\le s$. In particular even point evaluation is excluded for
$0<s\le1$. At equality the printed rule admits an inadmissible last
jet if the zero's order is high enough. The compatible *model count*
is the number of integers $0\le m<N(\rho)$ with $2m+1<s$, namely
$\min(N(\rho),\lceil (s-1)/2\rceil)$ for $s\ge0$. This is an
admissible jet count, not a proved trace multiplicity.

The project theorem `Masullo.boundaryLogJet_exists_smooth_extension_iff`
in [BoundaryLogJet.lean](../../Proofs/Props/BoundaryLogJet.lean) takes
real $s\ge0$, $m\in\mathbb N$, and $|\Re z|=\alpha$. It characterizes
existence of a complex continuous linear functional on $L^2(dx)$
agreeing with the log-Mellin jet on weighted smooth compact profiles.
It does not identify the actual idelic theta quotient, prove jet
totality there, or compute a trace. The accepted
[rational membership audit](../obligations/boundary-vector-membership-q.md)
exhibits the printed equality error at $s=1$ in the actual reciprocal
norm over $\mathbb Q$ with trivial compact character, by choosing a
twist that places a known zeta zero on an edge. That witness is outside
the $s>1$ trace theorem and does not exhibit an edge zero for the
positive-width strip centered at the twist $1/2$ in §1.4.8. It is not a
refutation of this introductory trace claim as printed.

## What remains to obtain an edge trace

For the actual theta quotient at twist $1/2$, each positive symmetric
half-width, and a fixed norm-one isotype, show that admissible edge
jets annihilate the twisted theta closure and, with the interior jets,
separate the quotient. Then prove trace class for quotient convolution
and compute its boundary Mellin coefficients on the common trace tests.
In particular, the comparison must include widths with a boundary zero,
justify the equality case of the degree cutoff, and account for the
range $0<s\le1$ rather than cite the higher-degree theorem there.

On the extraction reading, Theorem 10.4.2.8, p. 463, (10.4.2.20),
imports (10.3.2.3) for the cutoff trace of convolution **after** the
spectral projection. Its (10.4.2.21–22) lists the jet orders using $N$
rather than the capped $N_{I,s}$, and (10.4.2.22) has a different
exponent from (10.2.2.4). A transfer must track the jet orders and
shift in the actual cutoff trace, not just the abstract quotient
trace. Theorem 12.5.1.1, p. 519, (12.5.1.3) and following text,
selects **interior** zeros only. It does not provide a positive-degree
edge term or justify discarding one in the cutoff comparison at a
width with a boundary zero.

The proposed basis and trace argument are Masullo's. The strict jet
criterion and the scope comparisons are project checks. The project
[strip trace](../obligations/trace-spectral-strip-q.md) and
[theta closure](../obligations/trace-theta-density-q.md) repairs use
$\mathbb Q$, the trivial compact isotype, positive even degrees, and
a full-measure set of widths excluding all boundary zeros. Those
repairs do not resolve the edge contribution claim.
