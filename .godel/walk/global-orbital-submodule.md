# Closedness of the global finite-place orbital submodule

**Printed passage.** Masullo, *The Music of the Primes*, §1.2.9,
printed pp. 17–18, opening claim beginning “The linear subspace.”
The inclusion displayed at the bottom of p. 17 and completed by
“is a closed $\mathcal D(C_F)$-submodule” at the top of p. 18 is
$\mathrm{PV}_{S_p}H\subset H$, where
$H=\mathrm H_{0,\mathrm{cont}}(\chi|_{C_F^1},\mathcal S_0(\mathbf A_F))$
and $S_p$ is the set of finite places over the rational prime $p$.
The topology here is the intrinsic theta quotient topology, not a
Sobolev completion. The display and its continuation were checked
in rendered pixel crops, separately from the chapter Markdown,
text extraction, and OCR. The PDF ordinals match the printed pages;
SHA-256 is `e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5`.
This finding covers the opening claim, not the subsequent subquotient
identifications or the trace formula.

**What the operator argument checks.** For an idele $a$, write
$T_a f(x)=f(a^{-1}x)$. On adelic tests, $T_a$ fixes evaluation at
zero and scales the Fourier value at zero by $|a|_F$, by change of
variables. Thus $1-T_{\pi_v}$ preserves the two zero moments. These
differences commute with translation and intertwine the theta map
with the corresponding differences of translations on its image.
They also commute with the norm-one isotype projection in Masullo's
setup. Once descended continuously to $H$, the endomorphism
commutes with integrated translation, so its image
is stable under $\mathcal D(C_F)$ convolution. This is the reviewer's
operator check. It does not imply closedness of the image.

**Which operator?** The next sentence on p. 18 writes the ordinary
uniformizer difference, as confirmed by the rendered formula.
Masullo's Definition 5.3.1.2, p. 241, instead uses the difference on
the local unit-invariant part and the identity on the nontrivial
local unit isotypes. Equivalently, with $U_v$ the normalized local
unit average, this operator is $1-T_{\pi_v}U_v$. The same moment and
commutation checks apply to it. On a norm-one isotype unramified at
each $v\mid p$, the induced operators agree, since $U_v$ acts as the
identity there. The later closed-range claim for this definition
cannot simply be used for the literal difference in a ramified
isotype. The reading of the later definition uses the chapter
Markdown and raster OCR and is provisional.

**Open topological step.** Theorem 7.4.2.1(1), printed p. 367,
repeats the claim for the global principal-value operator; the
proof paragraph discusses part (2), not the closedness in (1).
Lemma 5.3.1.5, p. 242, claims a closed topological embedding for
the descended operator on the *full* global theta quotient.
Its printed argument passes from closed ranges on adelic inputs
through the theta quotient and then uses insertion from a fixed
$S$-local stage. Relative openness of the theta quotient map on
the principal-value image, and closedness of that image after
descent, do not follow from openness on the whole space. Nor does
compatibility with insertion alone put the whole global image in
one fixed stage. What is needed is a closed-range argument in the
actual global quotient. A sufficient route is to verify the
closed topological embedding of Lemma 5.3.1.5, then realize $H$
with its intrinsic topology as the closed norm-one isotype in the
joint kernel of the descended moments of Lemma 5.5.2.1 (p. 280).
The embedding would then carry this closed subspace to a closed
subspace in the full quotient, hence also in $H$. This route uses
Masullo's stated inputs and the reviewer's conditional restriction
argument, not a proof of the inputs. The reading of the two Chapter
5 arguments is from the chapter Markdown and PDF extraction and
is provisional. The matching statement in Theorem 7.4.2.1(1) was
checked in a rendered crop; the reading of its proof is from text
extraction and raster OCR. No Lean statement establishes this
closed-submodule claim at its printed scope.
