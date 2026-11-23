# What must vanish outside a fixed S

**Printed passage.** Masullo, *The Music of the Primes*, printed p. 32,
§1.4.10, from “The orbital bases are the principal tool” through the
parenthesis ending with $\mathrm{Pic}(\mathcal O_{F,S})=1$. Masullo
says that the bases reveal cancellation of the global kernel's
diagonal mass, leaving all of the geometric side in the $S$-local
piece. The calculation is character by character; a sufficiently
large finite $S$ is chosen for the test and character, then held
fixed. The paragraph assumes trivial $S$-ideal class group and
gives no new degree or support condition. It does not claim a common
$S$ for all tests or characters, or pointwise vanishing of the
omitted kernels. The review stops before §1.4.11. Chapter Markdown
and PDF layout extraction located the paragraph; raster OCR checked
the prose, and rendered pixel crops spot-checked “fixed” and the
class-group condition in the [digest-verified PDF].

**What the support bound gives.** In the proof on p. 520, Masullo
chooses $S$ to cover the relevant ramification and outside-unit
invariance and to have $q_v>T$ off $S$, with the test's norm support
in $(T^{-1},T)$. Saturate $S$ by residue characteristic as in §11.3:
If $p$ is omitted, every $v\mid p$ is omitted. Then the norm lattice
$q_v^{\mathbb Z}$ meets that annulus only at one. A test vanishing on
the entire norm-one fibre kills that sample too, including its
character-weighted fibre average. This support check works for one
fixed set and for a two-sided annulus. It only proves vanishing of
the *scalar samples*, not of the geometric shell integrals.

**Missing fixed-set comparison.** Even for a single norm-one
isotype, twist $1/2$, positive symmetric half-width, degree $s=0$,
and a Bruhat test supported strictly above norm one, two steps
remain. Identify the averaged Haar integral of each actual signed
shell for $p$ outside this $S$ with its orbital cutoff trace, with
justified removal of the cutoffs. Then justify integrating the
signed shell split and its limit in the same lift and quotient Haar
measure, so the surviving term is the diagonal integral of the
actual $S$-residual, not just a separately constructed local
operator. Pointwise telescoping does not justify either step. For
the two-sided test class used on pp. 519–520, the same operator
comparison is needed there as well. Theorem 11.3.2.1, p. 495, is
printed for $s>1$ and support strictly above norm one. Section 12.3,
p. 514, shows a heading and “Include section” footnote, with §12.4
following; this later observation is from layout extraction and
raster OCR, not fresh direct inspection of the rendered page.
The [accepted assembly reading] verifies that Masullo invokes the
vanishing on p. 520, not that it follows. The [geometric audit]
distinguishes an integrated split conditional on an integrable
identified diagonal from any evaluation of the pieces.

The localization is Masullo's proposal. This review applies the
geometric audit's annulus check to the fixed-set claim and separates
it from the shell trace and limit obligations. The preview remains
open. No Lean declaration is invoked for it.

[digest-verified PDF]: ../sources/masullo/README.md
[accepted assembly reading]: ../obligations/trace-assembly.json
[geometric audit]: ../obligations/trace-geometric.md
