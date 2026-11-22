# Applying the unit cut to the common theta test factor

**Printed passage.** Masullo, *The Music of the Primes*, §1.3.2,
printed p. 25, paragraph beginning “The stratification of the global
ideles” and the next sentence through the unnumbered indicator identity.
He says the planned divisorial stratification fits the common tensor
factor outside S of the Schwartz–Bruhat representatives from (1.3.2.1).
He gives the local principle: The unit group is compact and open in the
local field, and its indicator times the integer-ring indicator is the
unit-group indicator, as an equality of local Schwartz–Bruhat functions.
This review stops before the local Mellin identity.

Chapter Markdown and PDF layout extraction supplied the text. Direct
inspection of pixel crops rendered from the [pinned PDF][source] checked
the outside-S tensor and the unnumbered indicator display. Raster OCR
also recovered the compatibility paragraph and its lead-in to the
indicator display. The PDF matched the SHA-256 in the source record.

**Checked scope.** At a finite place v, the valuation ring and its
unit group are compact open subsets of the local field. The identity
follows because the unit group is contained in the valuation ring.
Consequently, for a test already in (1.3.2.1), multiplication by a
product of local unit indicators at finitely many places outside S
replaces exactly those integral factors by unit-group indicators and
leaves the S-factor and every other factor unchanged. The product can
be taken on the additive adèles and restricted to the idèles; it is
still a Schwartz–Bruhat test on the additive adèles. This checks the
pointwise mechanism on a supplied test, not an identity on theta
images or a preservation statement for the two zero moments.

**Open use.** The mechanism is Masullo’s; the finite-coordinate
calculation above is the reviewer’s application of it. Applying it
uniformly to representatives of the printed global norm-one isotype
requires [one fixed S supplying all the representatives][fixed], not
merely an S for each individual test. Applying it to the announced
strata uses the identification of the later cuts (1.3.2.2) with the
products of the coordinate unit indicators. Neither dependency is
resolved by the indicator identity. No Lean declaration is used.

[source]: ../sources/masullo/README.md
[fixed]: fixed-stage-theta-representatives.md
