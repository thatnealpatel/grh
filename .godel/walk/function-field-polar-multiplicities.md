# Scope of the function-field polar-multiplicity warning

**Printed passage.** Masullo, *The Music of the Primes*, §1.7.1,
printed p. 35, fourth bullet, standalone sentence beginning “Theorem
1.7.1.1 has no useful analog”. This is the last sentence before §1.7.2.
It is a qualitative claim about the polar-multiplicity result, not a
statement of an impossibility theorem with a specified class of analogues.

**Source check.** The [pinned PDF](../sources/masullo/README.md) matched
SHA-256 `e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5`.
Chapter Markdown and PDF layout extraction located the sentence. Raster
OCR checked the sentence and its boundary, and direct inspection of
rendered pixel crops spot-checked “no useful analog”, “a function field”,
and “positive characteristic.” On printed p. 534, §14.2, see (14.2.0.1),
the paragraph beginning “The size”, and the sentence beginning “In short”.
Rendered crops there spot-checked “many poles in common” and “does not
hold”; the separate operator-correction paragraph below was read from
extraction only and its reading remains provisional.

**What fails.** Masullo's example on p. 534 is the untwisted zeta function
of a curve over 𝔽_q. A point of degree d has residue size q^d, so its
Euler factor is the reciprocal of `1 − q^(−ds)`. The argument needs
residue sizes that are powers of q, not merely divisible by q. Each
factor has simple poles at every `s = 2πin/log q`, for integer n, so a
finite product over m points has pole order m there. Part (1) of Theorem
1.7.1.1 with its literal distinct-residue-characteristic hypothesis is
vacuous here. Replacing it by distinct places does not preserve the
pairwise at-most-one assertion in the s-plane.

Nor is the failure of the at-most-one assertion for infinitely many
places just an artifact of the s-plane parameter. In the norm-character
coordinate `u = q^(−s)`, the factor is the reciprocal of `1 − u^d`.
Two such factors in degrees d and e share exactly the roots of unity of
order dividing `gcd(d,e)`. For the rational function field 𝔽_q(t), there
are infinitely many even-degree places: For each even degree d, the
minimal polynomial of a generator of 𝔽_(q^d) over 𝔽_q gives one. Thus both
`u = 1` and `u = −1` are poles at infinitely many places for the trivial
character. This is enough to disprove the direct at-most-one analogue
of part (3) and gives the same obstruction for the trivial, untwisted case
of part (2), independently of the transcendence input.
It does not exclude other statements that retain the degree information.

**Open use and provenance.** The shared-pole example and the proposed
trace obstruction are Masullo's; the vacuity distinction and the
rational function field calculation in u are the reviewer's scope checks.
If “useful” is meant for the direct Sobolev trace construction, §14.2,
p. 534, in the paragraph beginning “Such correction enables the
deconstruction of the global geometric kernel”, still needs to show that
the growing product pole orders survive in the actual cutoff corrections
and force unbounded Mellin jet orders at a common point, without
cancellation or a continuous correction in the fixed topology. See the
[earlier trace comparison](function-field-trace-comparison.md). Local
poles alone give neither that necessity nor an impossibility result for
all analogues. The nearby number-field normalizations cited in the
[finite local audit](finite-local-polar-multiplicities.md) concern pointwise
Euler factors, not meromorphic poles of function-field factors. No
matching Lean statement was found in the inspected accepted proof tree.
The printed warning remains open at that broader scope.
