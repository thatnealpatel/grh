# The degree-one Hardy–Sobolev completion need not have continuous edges

**Printed passage.** Masullo, *The Music of the Primes*, p. 36,
§1.7.2, third bullet, from “I feel I need to repeat this” through
“topologies to which I am alluding.” Masullo says that for $a>0$ and
$b\ge0$ the Mellin transform turns these completions into spaces of
holomorphic functions on $|\Re z|<a$, with continuity and
differentiability at the edges up to order $|b-1|/2$. He also says that
the spaces were chosen to contain the bare minimum for the geometric
trace, especially certain continuous functionals of the stated form
on closed subspaces derived from locally convex Schauder bases, and that
the zeros do not select the topology. This note stops before “The
entire paper itself.” Chapter Markdown and PDF layout extraction
located the paragraph in the [digest-verified edition][edition]. OCR
of the p. 36 raster checked the prose; direct pixel crops checked the
parameter relations, the edge-regularity wording and cutoff, and the
paragraph boundaries.

**Which completion.** The [preceding display review][display] checks
that (1.7.2.2) is not a norm as printed. Its square gives a weighted
$L^1$ topology, not the weighted $L^2$ topology: A unit-$L^2$ radial
bump shrinking in the log coordinate at a fixed point has weighted
$L^1$ norm tending to zero. The squared-modulus $L^2$ topology is the
intended Hardy–Sobolev topology in the rendered (1.8.2.2), p. 44, and
(9.2.2.34), Lemma 9.2.2.10(2), p. 417. The edge obstruction below is
for that squared-modulus norm, not for the metric obtained from the
literal display. On the literal weighted $L^1$ model the exponential
weight already dominates every Mellin moment on $|\Re z|\le a$.

**Failure of even order zero.** Write $x=\log|g|_F$. The proper
surjective log module pushes Haar forward to $c\,dx$, $0<c<\infty$:
Properness gives local finiteness, a lift of each translation in
$\mathbb R$ shows invariance, and the preimage of a nonempty open
set is nonempty and open, hence of positive Haar measure.
Smooth compact log profiles pull back to all-weight radial
Schwartz–Bruhat tests and lie in the trivial norm-one isotype. Fix
$a>0$ and $b=1$, and take a smooth nonnegative profile $h$ supported in
$x>2$ with tail

$$
h(x)=\frac{e^{-ax}}{x\log x}\qquad(x\ge3).
$$

Its squared weighted integrand is comparable on the tail to
$1/(x(\log x)^2)$, so smooth compact cutoffs converge in the weighted
norm and define an element of the completion. For $|\Re z|<a$ the
Mellin transform of this element is $c\int h(x)e^{zx}\,dx$:
Cauchy–Schwarz gives local bounds for the evaluation and all
moments by the available exponential margin, so this is the
holomorphic limit of the cutoff transforms. But as real
$\sigma\uparrow a$, monotone convergence gives divergence to
$+\infty$ because the tilted tail at $a$ is $1/(x\log x)$. This
rules out even a continuous extension of the function to the right
edge. It uses no zero of a Hecke $L$-function.

**Comparison evidence.** The [boundary-evaluation audit][evaluation]
separately exhibits unbounded evaluation at degree one on smooth
compact log tests in the squared-modulus norm (and in a permitted
interior-line topology for Corollary 9.2.2.5(2), p. 414). For an
integer jet order $m\ge0$, the ambient symmetric weighted log model
has the strict threshold $2m+1<b$ for bounded boundary evaluation:
At the matching tail the squared reciprocal-weight kernel behaves
like $x^{2m-b}$. In the exact accepted Lean source,
`Masullo.boundaryLogJet_exists_smooth_extension_iff` in
[`Props.BoundaryLogJet`][lean] assumes $s\ge0$ and $|\Re z|=\alpha$.
It characterizes continuous complex-linear extension to
$L^2(dx)$ agreeing with the bilinear moment on smooth compact
profiles represented by the weight root times the profile. It does
not assert the full idelic transform, existence of pointwise traces
on general completions, or anything on a theta quotient. The p. 36
claim is Masullo's; the completion counterexample and norm
distinction are the reviewer's. The strict ambient threshold is
comparison evidence from the existing checked log model, not a new
Lean result. Independent Yah reviewer `p36-edge-reader` checked the
Haar pushforward, compact-test obstruction, divergent finite-norm
tail, and Lean source signature at accepted revision
`697feb624394c2fc95bc6162d040e06d20dd83ab` (review output
`b87708264c43378fc8d274b21acf6d3a3c05dc40`). The Lean file is
unchanged at the landing base. The review did not run a new build.

**Remaining scope.** Interior holomorphy is not refuted, and the
example does not refute an a.e. or $L^2$ edge trace. Nor does it settle
use of the completion in the geometric trace. For that use, identify
the actual orbital coefficient functionals on the completed
subquotients, show that their prescribed pairings are bounded and
vanish on the subspaces by which one quotients, and justify their use
in the cutoff diagonal and its limit. Ambient Mellin estimates do
not supply these comparisons. The [geometric-first audit][geometric]
and [coefficient audit][coefficients] separate them. No comparison
class or order on all candidate topologies is stated that would turn
“bare minimum” into a minimality theorem.

[edition]: ../sources/masullo/README.md
[display]: first-hardy-sobolev-display.md
[evaluation]: ../obligations/boundary-point-evaluation.md
[lean]: ../../Proofs/Props/BoundaryLogJet.lean
[geometric]: geometric-first-preview.md
[coefficients]: polar-coefficient-continuity.md
