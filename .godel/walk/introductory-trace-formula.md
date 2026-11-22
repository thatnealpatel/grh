# The opening trace formula: Strip, degree, and test class

**Status: Open.** Masullo, *The Music of the Primes*, §1.4, printed
pp. 27–28 (PDF ordinals 27–28), opening “Putting everything together”
through test assumptions (1)–(2), before §1.4.1. The [pinned
PDF](../sources/masullo/README.md) was checked by SHA-256. The chapter
Markdown and layout extraction located the passage, and raster OCR
checked the opening and test assumptions. The two strip expressions
below were spot-checked directly in rendered pixel crops. The full
formula transcription was not independently checked glyph by glyph.

## Statement as printed

For an arbitrary fixed positive half-width α, take I = [−α, α] and
s = 0. For a smooth compactly supported test φ on the idèle class
group that vanishes on the norm-one subgroup, the display equates
three normalized local integrals (real, complex, and finite) to the
two Mellin terms at norm exponents ±1/2 minus a sum with full zero
orders. The summand uses the Mellin argument cρ·|·|⁻¹ᐟ²; the text
selects zeros of L(cρ) in the interior of **σ(cρ) ∈ I**. Vanishing
on the subgroup is not support separated from it, nor a restriction
to the side |·| > 1.

**The later theorem is not the literal same statement.** The strip
display in Theorem 12.5.1.1, p. 519, reads **σ(c) ∈ 1/2 + I**.
The repeat in §1.8.4, p. 53, gives the same shift (chapter Markdown,
provisional). In §4.4.1, p. 189, σ(c) is the real norm exponent of c, not
that of c·|·|⁻¹ᐟ² (chapter Markdown, provisional). Thus the shift on
the Mellin argument on p. 28 does not by itself shift the set of
zeros being summed. The later centered strip is a plausible repair
of the introductory indexing, not evidence for the literal strip.
Here α names the width to distinguish it from the twist 1/2.

## What is needed to assemble the formula

Masullo's argument on p. 520, documented in the [accepted reading
of the final comparison](../obligations/trace-assembly.json), equates
two evaluations of the same integrated, averaged geometric diagonal.
On the geometric side it splits the diagonal, kills the orbital
tail, and identifies the S-residual with the normalized local value
minus the two Mellin terms. On the spectral side it identifies the
same diagonal with the negative strip sum. Equating the values is
algebra; the reading does not certify either evaluation.

- **Geometric input:** Justify integration of the split on the
  actual lifted and averaged kernel, not just on a partition of
  its pointwise values. At the same degree, width, and Haar
  normalization, recover the normalized local cutoff limit from
  that residual, with both Mellin subtractions, and show vanishing
  of the actual orbital tail. Local support can kill scalar
  positive and negative prime-power samples at large places and
  norm-one vanishing kills the unit samples; that calculation does
  not identify the orbital diagonal with the sample sum. The
  invoked Theorem 11.3.2.1 (p. 495) assumes s > 1 and support above
  norm one. The broader test class needs a direct comparison or a
  limit controlling both sides at the fibre. The [geometric
  audit](../obligations/trace-geometric.md) explains why density in
  the Bruhat test topology is insufficient: Tests supported away
  from the fibre have zero normal derivative there, while a test
  vanishing on the fibre need not.
- **Spectral input:** Prove (12.5.1.4) for the same Haar diagonal,
  with a valid degree-zero kernel and the claimed zero indexing.
  Definition 10.4.3.7 (p. 473) requires s ≥ 3; its kernel is what
  p. 520 invokes. Theorem 10.4.2.8 (p. 463) nominally allows s ≥ 0
  but points to (10.3.2.3)–(10.3.2.4) (p. 454), under s > 1,
  which use the centered strip, full interior orders, and capped
  orders on its boundaries, not an interior-only sum at every
  width. Excluding boundary-zero widths would remove that mismatch
  on the remaining widths, not prove the arbitrary-width claim.
  These later signature and boundary readings are provisional
  from chapter Markdown and layout extraction; see the [spectral
  audit](../obligations/trace-spectral.md).

The strip distinction and separation of the proof obligations are
reviewer checks. No Lean theorem establishes or refutes this
passage. The [rational radial scalar explicit
formula](../obligations/rational-explicit-formula.md#checked-rational-radial-idelic-explicit-formula)
is over ℚ in the trivial compact isotype with the full zero sum and
does not identify the averaged geometric diagonal. The separate
`Masullo.zetaZero_in_closedStrip_of_test_agreement` assumes equality
of full and width-supported rational zero sums on smooth compact
positive-log tests of integral zero. It proves a closed-strip
consequence under that premise, not the comparison or arbitrary
widths. See the [trace-to-zeros audit](../obligations/trace-to-zeros.md).
