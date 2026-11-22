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
This audit covers the opening claim, the global operator definition,
and the immediately following $S$-local operator preview. It does not
cover the subquotient identifications or the trace formula.

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

**Which operator?** The next sentence, §1.2.9, printed p. 18,
beginning “Recall that,” takes $S_p$ to be the finite places of residue
characteristic $p$ and defines $\mathrm{PV}_{S_p}$ as the product of the
operators induced by the literal differences $1-T_{\pi_v}$, for a
choice of uniformizer at each $v\in S_p$. The rendered sentence and
display match the chapter Markdown and PDF text extraction. The
translation intertwining above gives descent to the theta quotient:
The kernel of the theta map is stable under $T_{\pi_v}$, and continuity
passes to the quotient by its defining topology. Since the differences
commute with each other, their product needs no ordering.

Masullo's Definition 5.3.1.2(2)–(3), p. 241, instead uses the difference
on the local unit-invariant part and the identity on nontrivial local
unit isotypes. Definition 5.3.1.4(1)–(2), pp. 241–242, tensors these
local principal-value operators to form the adelic product, not the
unconditional differences. The two cases of the local definition and
the lines specifying the tensor factors on p. 242 were checked directly
in rendered pixel crops of the same pinned PDF. With $U_v$ the normalized
local unit average, the later local operator is $1-T_{\pi_v}U_v$.
It preserves the two zero moments and commutes with translations, as
in the calculation above. On a norm-one isotype unramified at every
$v\mid p$, the two products agree because each $U_v$ acts as the
identity. At a ramified place the local factors differ on every
nonzero vector in that unit isotype: The omitted translate is nonzero
because $T_{\pi_v}$ is invertible. The unit average also makes the
later factor independent of replacing $\pi_v$ by a unit multiple,
unlike the literal factor on a nontrivial unit isotype. Thus
unramifiedness at all places over $p$ licenses the identification;
without it, the local formulas do not justify the substitution.
This is a source comparison and an elementary operator check, not a
Lean result or a determination of the range, topology, or trace of
either product.

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

## The S-local operator preview

**Printed passage.** Section 1.2.9, printed p. 18, beginning “An analog
of” and ending “In the $S$-local case we assume $S_p\subset S$,”
announces an analogue of the principal-value product on
$\mathrm H_{0,\mathrm{cont}}(\mathcal O_{F,S}^\times,\mathcal S(\mathbf A_{F,S}))$.
The display uses the full $S$-local test space, not $\mathcal S_0$ and
not a single norm-one isotype. The sentence, display, and inclusion
were checked directly in a rendered crop of the pinned PDF, separately
from the chapter Markdown, PDF text extraction, and raster OCR.

**Descent check.** At a finite stage $S$ containing the Archimedean
places and $S_p$, every uniformizer at $v\in S_p$ can be placed in the
$v$-coordinate of an $S$-idele with all other components equal to one.
Each corresponding translation is continuous on the $S$-local
Schwartz-Bruhat space. Masullo's Definition 2.3.1.1, pp. 99–100, and
Proposition 2.3.1.2(1), p. 100, supply the convergent $S$-unit sum
$\Phi_{F,S}(f)(g)=\sum_{\xi\in\mathcal O_{F,S}^\times} f(\xi g)$.
Term by term, $\Phi_{F,S}(T_a f)(g)=\Phi_{F,S}(f)(a^{-1}g)$ by
commutativity. Therefore each $T_a$ preserves its kernel, and the
product of the literal differences descends continuously by the
quotient topology of Definition 5.1.1.1(3), p. 223. It commutes with
translation and preserves norm-one isotypes. The Chapter 2 and
§5.1 citations here are provisional readings from chapter Markdown
and PDF extraction. The descent calculation is the reviewer's, using
those definitions and the stated convergence, not a proof of the
convergence result.

**Later formulation and scope.** Definition 5.3.1.4(1), pp. 241–242,
uses the unit-averaged factors $1-T_{\pi_v}U_v$ of Definition 5.3.1.2
at the selected places and identity factors elsewhere. Its following
paragraph gives the continuous endomorphism of the full $S$-local
theta quotient in (5.3.1.9) and states compatibility with norm-one
isotypes. The display and the isotype line on p. 242 were checked in
the rendered PDF, separately from the Markdown and text extraction.
The literal and averaged products agree on isotypes unramified at
every place in $S_p$, not by the inclusion $S_p\subset S$ alone. This
passage previews the construction. It states neither closed range
nor the later local-to-global isomorphism. Descent does not establish
either, and no Lean declaration is claimed for this preview.
