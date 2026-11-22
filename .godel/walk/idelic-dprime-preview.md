# The idelic D′-sequence construction preview

**Printed passage.** Masullo, *The Music of the Primes*, printed p. 22,
§1.3.1, preview in the paragraph beginning “We call a sequence” and
ending “S-idelic norms).” Masullo names the Borel closed-ball analogues
D′-sequences, credits Hewitt–Ross (footnote 4, vol. II, ch. XI, §44),
and promises a direct construction for the groups of interest using
continuous sections of the idelic and S-idelic norms. This paragraph
neither states the full axioms nor proves the subsequent claim about
images of a sequence lying in a fundamental domain.

The [pinned PDF][source] was checked against SHA-256
`e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5`.
Chapter Markdown and PDF layout extraction identify the passage and
footnote. OCR of the rendered page was used to spot-check the paragraph
and the footnote locator, and the printed “II” was checked in a pixel
crop. The [angular trace audit][spectral], at revision
`a0724c05f93bbb4a1bb5883785f5bb9923202b47`, records the rendered-display
checks behind the counterexample below. The Appendix A and Chapter 12
passage locators were checked against the chapter Markdown and OCR
from rendered pages, not by reviewing the later proofs in full.

**Axioms and intended input.** Definition A.5.2.1, p. 569, requires
identity-containing nested sets of positive finite Haar measure, with
a uniform bound on μ(UₖUₖ⁻¹)/μ(Uₖ). For D′ the sets must eventually fit
inside every identity neighborhood. The definition allows Haar-measurable
sets; this preview and the recap after Definition 12.1.1.1, p. 498,
use Borel sets. That recap expressly invokes Appendix A and calls its
idelic sequences symmetric D′-sequences. For the full ideles and their
class group the intended boxes and quotient images are Lemma A.5.2.17(1),
p. 577, and Definition A.5.2.18(1)–(2), p. 578. Lemma A.5.2.15,
pp. 576–577, asserts the S-local conclusion for the boxes of (A.5.2.22)
and their images in J_{F,S}; the general S-local verification is not
part of this finding.

**Construction gap.** The angular trace audit's ordinary-mathematics
counterexample applies to the route advertised here. For F = ℚ(i),
the full inverse image in (A.5.2.19)–(20), p. 576, is the entire
Archimedean circle S¹: The logarithm just below (A.5.2.9), p. 574,
records absolute value but not phase, and for ℚ(i) the sum defining Pₖ
has no indices. On the tail k ≥ 2, the boxes of (A.5.2.23)–(24),
p. 577, therefore all contain S¹ with every finite coordinate equal
to 1, since the norm section sends 1 to 1 and every Bₖ contains 1.
That circle maps injectively to C_F: A principal idele equal to 1 at
all finite places comes from the field element 1. In both groups a
neighborhood excluding a fixed nonidentity point of the circle thus
contains none of the tail boxes. This rules out the D′ shrinking
condition for these literal boxes, not the existence of a different
D′-sequence on either group or the conditional differentiation theorem.

To use such a construction in the trace comparison, one must restrict
the norm-one boxes in the angular directions as well and verify
shrinking and uniform doubling in the groups and on the quotient
images actually used. The audit proposes replacement angular boxes;
those are not Masullo's printed boxes. The accepted Lean source of
`Masullo.ideleLogNorm_scalarSection` only identifies the log norm of
a homomorphic scalar section on full ideles in log coordinates. It
neither states the S-idelic result nor constructs a D′-sequence. No
Lean declaration for the preview's conclusion is used here.

**Independent check.** Yah dispatch `dprime-source-review` (review
session `01a204f9-3a44-7fbf-ad04-65126a72480a`, assigned revision
`a3db2556294b9bd62998eff56d16b45fd802d08e`) independently checked the
pin, the printed excerpts by layout extraction and raster OCR, and
the scope of the accepted counterexample. It confirmed failure of
shrinking for both the printed global boxes and their quotient
images, not failure of existence of alternative boxes. It reported
no Lean endpoint for that counterexample and no kernel check.

[source]: ../sources/masullo/README.md
[spectral]: ../obligations/trace-spectral.md#the-averaging-boxes-must-actually-shrink
