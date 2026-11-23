# Idelic quasi-character planes and annuli

**Printed passage.** Masullo, *The Music of the Primes*, §1.7.1,
printed p. 33, first bullet, opening paragraph from “They make all the
function spaces involved far more interesting” through “annuli of finite
area.” “They” refers to Archimedean places. The mathematical claim is
that the global idelic quasi-character components are simply connected
for number fields, in contrast to the finite-area annuli obtained as
vertical strips for global function fields. The paragraph beginning
“By far the most important difference” is a separate claim about theta
periodization and is not reviewed here.

The [pinned PDF](../sources/masullo/README.md) matches the recorded
SHA-256. The chapter Markdown and PDF layout extraction located the
passage, raster OCR checked the paragraph, and direct inspection of
rendered pixel crops spot-checked the number-field and annulus wording.
The forward locator, §3.1.1, printed p. 119, restriction map and
connected components (3.1.1.1), was cross-checked by raster OCR; its
formulas below are a provisional reading from Markdown and PDF text
extraction, not visually checked formulas.

**Norm-coordinate comparison.** Write $C_F^1$ for the kernel of the
idele class norm. Given its compactness, restriction of quasi-characters
lands in its discrete unitary dual. Two characters in a nonempty fibre
differ by a character of the norm image. With a continuous homomorphic
section of the norm, compact-open restriction to the section and
pullback by the norm are inverse homeomorphisms on this difference
family. Multiplication by a fixed quasi-character then gives the same
model for the entire fibre. If the norm-image character space is
connected, discreteness of the target makes the fibre a whole connected
component, not just a connected subset.

For a number field, a positive radial section at one Archimedean place
gives log-norm image $\mathbf R$. Its continuous quasi-characters are
$t\mapsto e^{st}$ for unique $s\in\mathbf C$. For the inverse continuity
in compact-open topology, it suffices by translation to work near the
trivial character. Evaluation at $1$ recovers $\operatorname{Re}s$
from the modulus. If the unitary parts are uniformly close to $1$ on
$[0,1]$, the frequency $b=\operatorname{Im}s$ must satisfy $|b|<\pi$:
Otherwise the unitary part hits $-1$ in that interval. Evaluation at
$1$ then recovers $b$ by the principal argument near $1$. Thus the model
is a complex plane, not a cylinder obtained by evaluating at just one
norm value. Independence of logarithms of distinct primes is not used.

For a global function field, with $q$ the constant-field cardinality,
local norm values lie in $q^{\mathbf Z}$ and some are nontrivial.
Consequently the log-norm image is $\delta\mathbf Z$ for $\delta>0$.
Choose an idele class of log norm $\delta$ to split this discrete
quotient. Evaluation at $\delta$ identifies its character space with
$\mathbf C^\times$, and in the exponent coordinate it is
$\mathbf C/(2\pi i\mathbf Z/\delta)$. In these coordinates the open
strip $a<\operatorname{Re}s<b$, for finite $a<b$, maps under
$e^{\delta s}$ to the annulus $e^{\delta a}<|z|<e^{\delta b}$.
This has finite Euclidean area in the annulus coordinate and finite
flat quotient area $2\pi(b-a)/\delta$ in the exponent coordinate.
The finite-area assertion is per component and for bounded abscissa;
it is not an intrinsic area claim about the entire character space.

**Checked scope and open inputs.** This comparison is the reviewer's
informal calculation under the stated norm and compactness inputs.
Masullo states the contrast here and gives the abstract fibre picture
in §3.1.1. For a checked finding, the number-field branch still needs
the exponent chart as a homeomorphism onto the actual compact-open
component, including its transport to arbitrary components. The
function-field branch needs the compact norm-one kernel and the
compact-open component identification on the actual idele class group
with its discrete norm image. These are distinct from the elementary
annulus calculation once the component model is supplied.

At accepted revision `47eb4b607ef17236bbc0e82d00a4346d7dc3d0a8`,
`Proofs/Theorems/IdeleClassCharacterComponent.lean` gives
`Masullo.ideleClass_component_one` and
`Masullo.ideleClassNormPower_existsUnique` for actual number-field
idele classes, and `Masullo.continuous_ideleClassNormPower` proves
continuity in the forward direction. These are membership,
parametrization, and continuity statements, not the inverse continuity
or simple-connectedness statement. The declarations do not treat
global function fields. No fresh Lean statement and independent
signature audit resolve the contrast here, so the formal finding
remains open, without adverse evidence against the printed topology.
