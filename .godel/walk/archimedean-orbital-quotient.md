# The introductory S-local Archimedean orbital quotient

**Printed passage.** Masullo, *The Music of the Primes*, p. 19,
§1.2.10, from “These are denoted” through the complex flatness
parenthesis. The numerator of the quotient is the norm-one character
isotype of the **full** S-local S-unit theta space. The denominator is
printed as the S-unit theta space on $\mathcal S_\infty$, without an
isotype on that term, and is called closed. The displayed test space
uses tests flat at each real or complex coordinate zero, tensored
with **unrestricted** $\mathcal S(F_v)$ at each finite place in $S$.
Flatness in the complex coordinate includes all holomorphic and
antiholomorphic derivative orders. The notation, denominator,
“closed subspace,” finite tensor factors, and complex derivative
symbols were spot-checked in rendered pixel crops, separately from
chapter Markdown, PDF text extraction, and raster OCR. Printed p. 19
is PDF page 19 of SHA-256
`e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5`.
The next sentence asserting a closed convolution submodule is not
part of this passage.

**Interpretation and missing step.** Write $H$ for the full test-space
theta isotype and $q_\omega$ for theta followed by projection to it.
The denominator for a quotient of $H$ needs to be interpreted as
$q_\omega(\mathcal S_\infty)$, not as the unprojected theta space written
in the display. Closedness of the flat test subspace before taking
theta does not imply closedness of its image in the intrinsic theta
quotient topology. One needs to show that
$\mathcal S_\infty+\ker(q_\omega)$ is closed in the full test space,
or identify the projected image as a closed subspace of $H$ directly.

**Scope of the later construction.** Notation 7.3.4.1, p. 364,
(7.3.4.3), uses $PH$ as numerator, where $P$ is the finite-place
principal-value product, and $D=q_\omega(\mathcal S_{00})$ as
denominator. The later $\mathcal S_{00}$ on all the S-adeles uses
$\mathcal S(F_v^\times)$, extended by zero, at each finite place
(Definition 5.3.4.1, p. 259, (5.3.4.1)). Theorem 7.3.4.1(1),(3),
pp. 364–365, states closedness of $D$ in $PH$ using the pole
filtration. It does not directly give closedness for the introductory
denominator. To use that route, one needs
$q_\omega(\mathcal S_\infty)=P^{-1}(D)$ in $H$. A sufficient check is
that the later finite-place product on tests carries the introductory
flat space onto the later all-place polar-free space and that the
commuting descended operator is injective on $H$. Lemma 5.3.1.5,
p. 242, states local injectivity for that operator. With the preimage
identity, continuity into $PH$ with its subspace topology suffices;
closedness of $PH$ in $H$ is not needed for that inference.

**Disposition.** The quotient notation and later statements are
Masullo's. The projection interpretation, distinction between test
and quotient closedness, and conditional comparison are the
reviewer's. The Chapter 5 and Chapter 7 readings are provisional,
from chapter Markdown and PDF text extraction, not rendered-page
inspection. The closed-denominator premise remains open here. No
Lean declaration is used, and neither a basis nor a trace is checked
in this passage.
