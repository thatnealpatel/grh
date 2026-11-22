# The character-by-character trace formula: Local weights

**Status: Open.** Masullo, *The Music of the Primes*, §1.4.1,
“Character by character,” printed p. 28, through the sentence about
the two Mellin terms. The chapter Markdown and PDF layout extraction
located the display in the [digest-verified edition](../sources/masullo/README.md).
Raster OCR checked the surrounding prose. Direct inspection of rendered
crops checked the bar on the isotype weight, the real sign summation
and denominators in the two displays, the unbarred Archimedean factors,
the complex radial power, and the unbarred first and barred second
finite coefficients.
Other formula details below use the extraction. The reference to
assumptions “(a) and (b)” apparently means (1) and (2) immediately above.

Masullo says the [opening trace formula](introductory-trace-formula.md)
reduces to two Archimedean coordinate integrals and a signed prime-power
sum for a test of norm-one weight χ̄. Its right side retains the Mellin
pair at norm exponents ±1/2 and writes the zero integrand as
χ(g)φ(g)|g|^(ρ−1/2). The final sentence says the Mellin pair vanishes
for a noninvariant homogeneous test.

## What the character restriction gives

Let χ be unitary, and let φ(gk) = χ̄(k)φ(g) for k in the norm-one
subgroup. Then χφ is invariant under that subgroup and descends to a
radial profile f, with φ(g) = χ̄(g)f(|g|) and f(1) = 0. Translating the
Mellin integral by k makes it vanish unless the Mellin character
restricts to χ there. The surviving zero parameters have the form
χ·|·|^ρ; this gives the displayed zero integrand, with the starting
strip restriction unchanged on the surviving isotype. Each of the two pole
terms vanishes in the nontrivial compact isotype. None of these steps
changes the starting strip center or justifies its spectral sum at
Sobolev degree zero.

## What the local change of variables does not give

- **Real place:** Substituting g = tu for t > 0 and u = ±1 in the
  opening denominator |1−g| gives |1−tu|, whereas §1.4.1 prints |1−t|
  for both signs. Over ℚ take χ trivial and a nonnegative nonzero
  smooth radial profile supported in (1,2). The negative branch then
  has the same positive numerator in the two displays, but has
  denominator 1+t in the opening display and t−1 in §1.4.1. Their
  integrals differ strictly. No identity contact term or finite
  prime-power term can compensate on this support. This checks a
  discrepancy in the proposed reduction, not which side of the
  global trace comparison is valid.
- **Complex place:** For z = teⁱᶿ with t the Euclidean radius and
  normalized norm |z|ᵥ = t² (Appendix A, p. 539, extraction), the
  half-norm factor is t, not t^(1/2), and the radial profile is f(t²).
  With t the normalized norm instead, the local argument must be
  √t eⁱᶿ and the Haar coordinates must also be transformed. In both
  Archimedean terms, using the original test requires its local
  restriction, with no additional χᵥ factor. Using the radial profile
  requires χ̄ᵥ times that profile. The displayed unbarred χᵥ factors
  need a separate convention or correction, not just homogeneity.
- **Finite place:** With π a uniformizer and q = |π|ᵥ⁻¹, the shell
  factors |g|ᵥ^(1/2)/|1−g|ᵥ at norms q^m and q^(−m) are both
  q^(−m/2) for m > 0. The norm-one shell vanishes. The other shells
  give the two printed character coefficients on f(q^m) and f(q^(−m))
  **times the normalized Haar average of χ̄ᵥ on the unit group**.
  That average is one at an unramified place and zero at a ramified
  place, so summing bare uniformizer samples over all finite places
  needs a ramified zero convention or an explicit restriction. Without
  it, those samples can depend on the choice of uniformizer. This
  shell calculation is for the normalized Haar expression; the
  removal of the prime on the local integral must use the same
  normalization. The proof of Theorem B.4.4.7, p. 625, equations
  (B.4.4.20)–(B.4.4.22), is the later comparison to check for these
  tests, not evidence for the strip identity.

The reduction is Masullo's; the compact-character and coordinate checks
above are the reviewer's. The existing [rational radial scalar explicit
formula audit](../obligations/rational-explicit-formula.md#checked-rational-radial-idelic-explicit-formula)
checks `Masullo.rationalIdeleRadial_explicit_formula` for ℚ with trivial
compact isotype, a normalized real Haar comparison, and the full zero
sum. It neither checks the printed real sign summation nor supplies the
arbitrary-isotype, strip-restricted trace identity. No new Lean result
is claimed here. A valid degree-zero starting comparison for each
isotype, and local formulas under one consistent test, Haar, and
character convention, are still needed for the subsequent limiting
argument.
