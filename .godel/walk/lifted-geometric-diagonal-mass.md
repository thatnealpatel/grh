# The lifted geometric diagonal mass

**Printed passage.** Masullo, *The Music of the Primes*, §1.3.1,
printed p. 24, second bullet beginning “We compute its diagonal
mass,” equation (1.3.1.12) and the sentence about choices. Put
G = GL₁(A_F), H = F×, and π: G → C_F. Masullo invokes simultaneous
H-invariance of the two-idèle geometric lift K to infer that the
formulas referenced as (12.2.2.4) apply. He equates the integral of
the smoothened quotient diagonal with the integral over D of the
sum of the ambient smoothening at (x, ξx), ξ ∈ H. The two
smoothenings use a chosen D′-sequence and its quotient image.
He asserts independence from that choice, the lifted test φ̃,
and the indentation u₀.

The [pinned PDF][source] matched SHA-256
`e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5`.
Chapter Markdown and layout extraction supplied the passage.
Direct inspection of rendered pixel crops confirmed the reference
(12.2.2.4), the ambient smoothening and second-coordinate skewer
in (1.3.1.12), and the choice-independence wording. Raster OCR
cross-checked the prose. This note stops before the following
paragraph beginning “The advantage.”

**Missing identification on the skewers.** Even after the
[one-variable test repair][lift], K is a convolution lift minus
an indentation lift, not in general the diagonal indentation
lift of the geometric difference. Simultaneous invariance and
unaveraged orbit recovery do not justify unfolding the averaged
values. Proposition 12.2.2.2(2), p. 508, equations
(12.2.2.4)–(12.2.2.7), unfolds the lift of an *already*
smoothened quotient kernel with an absolutely integrable
diagonal, not the smoothening of an arbitrary invariant lift.
The value identity in part (4), (12.2.2.9), p. 509, is only
product-Haar almost everywhere; the skewers are product-Haar
null. These later locators were read provisionally from chapter
Markdown. For the actual spectral term, one needs convergence
of the ambient averages to the indented quotient diagonal
value for every ξ on a single Haar-conull subset of D.

**Conditional check of the displayed order.** Let S denote the
same Haar-relative spectral kernel that is subtracted on the
quotient, let d(q) be its smoothened quotient diagonal, and let
w = u₀^Δ be the continuous normalized indentation weight.
Supply a normalized measurable fundamental domain and actual
shrinking, quotient-compatible boxes. A sufficient extra input
is d ∈ L¹(C_F) and bounded normalized averages of |S| at (q,q)
for Haar-almost every q where d is defined. The [skewer estimate]
then gives ambient limits w(x, ξx)d(π(x)) for the spectral
lift: The error is bounded by the oscillation of w in the
translated product box times the corresponding normalized
absolute quotient average. Countability of H permits a common
conull set. The orbit sum of the nonnegative coefficients
w(x, ξx) is one.

The continuous regular term has ambient limit φ̃(ξ⁻¹) there.
Its orbit sum is finite and equals φ(1), so the sum of the
smoothened values is φ(1) − d(π(x)), the quotient smoothened
geometric diagonal. In the introductory support range strictly
above norm one, φ(1) = 0, and the normalized section identity
now gives (1.3.1.12) in the displayed order. This calculation
uses local integrability, not the earlier disputed uncut
product L² assertion. It is the reviewer's conditional
calculation, using Masullo's weight and unfolding setup.

**Limits of choice independence.** For those fixed compatible
boxes, this calculation gives the same integrated orbit sum
for all repaired test lifts and continuous indentations to
which it applies. Independence across box choices additionally
needs a common quotient diagonal mass. The [spectral audit]
proves a conditional common trace value and absolute-average
bound for an identified trace-class operator with genuine D′
boxes; it does not identify the introductory s = 0 spectral
term in the correct operator order and Haar convention. Its
angular check also rules out assuming the literal standard
boxes shrink for all F, not the equation for Masullo's kernel.

If one also wants absolute integration in both orders, the
regular terms must be controlled before cancellation. A lift
supported above norm one vanishes at every ξ⁻¹ and suffices
under the spectral hypotheses above. An unrestricted repaired
lift need not vanish there: Adding the difference of a compact
smooth bump near 1 and its translate by a nonidentity element
of H preserves periodization but can produce nonzero values
on H. A nonzero constant φ̃(ξ⁻¹) is not integrable on D of
infinite Haar mass; an L¹ spectral summand cannot make that
individual geometric summand integrable. This distinguishes
the summed integrand in (1.3.1.12) from an absolute Fubini
statement for arbitrary lifts.

**Formal scope: Open.** The required skewered comparison,
quotient diagonal control, and box independence for the actual
spectral term remain unverified. No Lean result is used.

[source]: ../sources/masullo/README.md
[lift]: two-idele-geometric-lift.md
[skewer estimate]: skewered-smoothening-use.md
[spectral audit]: ../obligations/trace-spectral.md#from-the-weighted-kernel-to-the-haar-diagonal
