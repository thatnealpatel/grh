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
This finding covers the opening claim and the following global
operator definition, not the $S$-local analogue, the subquotient
identifications, or the trace formula.

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
