# Integrability of the uncut geometric kernel

**Printed passage.** Masullo, *The Music of the Primes*, §1.3.1,
printed p. 24, claim in the paragraph beginning “We are now back to
the situation of interest.” For a fixed character χ and smooth
compactly supported φ, Masullo defines the uncut kernel
`k_geom(x,y) = φ(xy⁻¹) − k_spec(x,y)`. He asserts measurability,
square-integrability on the product for ν ⊗ ν∨, and existence and
Haar integrability of its smoothened diagonal. He attributes these
properties to the spectral kernel's construction as a limit of
smooth finite-rank kernels. No cutoff or vanishing condition on φ
is repeated in this paragraph. The ensuing lift preview is a
separate passage.

The [pinned PDF][source] matched SHA-256
`e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5`.
Chapter Markdown and layout extraction supplied the passage. Direct
inspection of rendered pixel crops confirmed the subtraction, the
words “square-integrable,” the Haar-integrability wording, and the
reciprocal weight in (1.8.3.5) on p. 47. Rendered-page OCR
cross-checks the prose and places the claims before the lift preview.
On pp. 47–48, item (5) claims weighted L² for the *spectral* term,
and item (6) calls the geometric operator “neither trace class,
nor Hilbert-Schmidt.” The latter wording was checked by extraction
and rendered-page OCR, not direct inspection of that phrase.

**Product norm obstruction.** With μ̄ the Haar measure on C_F, set
ν = wμ̄ and ν∨ = w⁻¹μ̄. Write t = log |y|_F and u = log |z|_F,
where z = xy⁻¹. The change of variables x = zy replaces the
square norm of φ(xy⁻¹) by the μ̄-integral of |φ(z)|² times the
inner integral of w(zy)/w(y) over y. For each fixed z, (1.8.3.5)
gives w(zy)/w(y) tending to exp(2|a|u) > 0 as t tends to +∞:
The polynomial weight ratio tends to 1. Each norm tail has infinite
Haar measure, since it contains infinitely many disjoint translates
of a relatively compact open set with log norms in a bounded
interval. By continuity, a nonzero φ is nonzero on a positive-Haar
set of z. Tonelli therefore gives an infinite square norm for the
regular term. This check does not require φ to meet the norm-one
fibre. If the spectral term is in this same weighted L², as p. 47
claims, the uncut difference cannot also be there. Local L², or L²
after a bounded compactly supported first-variable cutoff, would
follow from spectral L², but neither is the statement on p. 24.

**Separate diagonal obligation.** For genuinely shrinking product
boxes the regular term averages tend to φ(1) at each (x,x) by
continuity. If the spectral diagonal exists almost everywhere and
is Haar-L¹, then the geometric diagonal is Haar-L¹ only when
φ(1) = 0: C_F has infinite Haar mass. The earlier support
restriction strictly above norm one implies that vanishing, but
does not fix the product norm. A missing step for the diagonal is
to identify the very spectral term subtracted on p. 24 as the Haar
kernel of a trace-class operator on the stated weighted isotype,
with the correct operator order, and show that the chosen boxes
for this use satisfy the needed differentiation hypotheses. A
finite-rank limit with no convergence norm or bound does not do so,
and product-Haar almost-everywhere recovery does not give values
on the product-null diagonal.

The [spectral audit][spectral] separates the operator-order and
weight-convention gaps in the provisional Chapter 10 reading from
its own conditional diagonal argument. The latter uses a
trace-class operator and genuine shrinking boxes with an L²
maximal bound, estimates the absolute rank-one tails, and converts
the weighted kernel to the Haar kernel. The singleton-strip
application in Theorem 12.1.1.3, pp. 502–503, is not the printed
general claim. The norm calculation and the separation of the
regular and spectral diagonal terms above are the reviewer's,
not Masullo's finite-rank argument. No Lean endpoint was checked.

[source]: ../sources/masullo/README.md
[spectral]: ../obligations/trace-spectral.md#from-the-weighted-kernel-to-the-haar-diagonal
