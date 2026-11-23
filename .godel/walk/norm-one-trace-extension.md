# Extending the trace formula across the norm-one fibre

**Status: Open.** Masullo, *The Music of the Primes*, printed p. 30,
§1.4.6, paragraph beginning “Indeed, the trace formula can only be
proved” and ending “by a continuity argument.” He says the calculation
starts with Bruhat tests on $C_F$ supported at norms in
$[1+\varepsilon,+\infty)$ for arbitrary fixed $\varepsilon>0$. It then
extends to support in $(0,1-\varepsilon]$ for arbitrary fixed
$0<\varepsilon<1$, and finally to all tests with $\varphi(C_F^1)=0$.
The paragraph gives neither the transport to the lower side nor the
topology for the last step. Coverage stops before “The condition
$\varphi(C_F^1)=0$ cannot be removed before GRH is proved.”

Chapter Markdown and PDF layout extraction located the passage in the
[digest-verified edition](../sources/masullo/README.md). Raster OCR
checked the prose; direct inspection of rendered raster crops checked
the two intervals, the inequality for the lower-side width, the
vanishing condition, and the words “continuity argument.”

**Starting comparison and reflection.** In the context of §1.4, the
needed comparison is at twist $1/2$, Sobolev degree zero, and positive
symmetric strip half-width, with the same Haar normalization, both
polar Mellin terms, and the same centered strip zero sum throughout.
The [later trace comparison](../obligations/trace-assembly.json),
Theorem 12.5.1.1, pp. 519–520, asserts the full vanishing-class
identity. Its algebra does not prove the two evaluations it equates.
The orbital input invoked there, Theorem 11.3.2.1, p. 495, has
above-one support and degree $s>1$ in the chapter Markdown and PDF
extraction (provisional source reading). Even for the upper side,
a calculation at that degree does not supply the introductory
comparison. For the lower side, proving the same comparison directly
would suffice. To use inversion instead, one needs compatible
transformation laws on both sides, including the local measures and
cutoff normalizations and the reflected Mellin indices and zero
multiplicities in the dual isotype. Inverting the support of a test
alone does not give those laws.

**The last continuity step.** Even if the comparison holds on both
separated sides, splitting tests proves it only for support disjoint
from the norm-one fibre. As in the [geometric audit](../obligations/trace-geometric.md#extending-across-the-norm-one-fibre),
write $x=\log|g|_F$. First normal-derivative evaluation at the identity
is continuous on the Bruhat test space and vanishes on every test
supported off the fibre. A radial test $x\eta(x)$, with $\eta$ a compact
smooth bump equal to one near zero, vanishes on the fibre but has that
derivative equal to one. Thus ordinary Bruhat-test continuity does
not extend the equality to the printed class: A difference of
functionals could be supported on the fibre and detect that derivative.
The missing step is a common limiting comparison, for instance
control of **both** scalar sides as cutoffs excluding a shrinking
neighborhood of the fibre are removed from each vanishing test, or a
proof that any residual supported on the fibre depends only on the
test's restriction to it. The failure of Bruhat-test density does not
refute the trace formula or exclude convergence of the two scalar
values.

The extension is Masullo’s assertion; the separation of the steps
and the density obstruction are project audit reasoning. No Lean
result is added. The accepted `Masullo.rationalIdeleRadial_explicit_formula`
([audit](../obligations/rational-explicit-formula.md#checked-rational-radial-idelic-explicit-formula))
uses compact smooth radial log tests over $\mathbb Q$ with trivial
compact isotype, a normalized scalar local pairing, and the full
nontrivial zeta zero sum. It is not a comparison of Masullo’s geometric
diagonal with a variable-width strip trace and does not justify this
extension.
