# Convolution squares in the norm-one vanishing class

Masullo, *The Music of the Primes*, printed p. 35, §1.7.2, first
bullet, paragraph beginning “Weil’s Positivity Criterion uses test
functions” and ending “is identically zero.” Masullo says that a Weil
positivity test has the form $\varphi=\psi*\psi^*$, where
$\psi^*(g)=\overline{\psi(g^{-1})}$, and that the only such test
satisfying (1.7.2.1) is the zero function. Coverage stops before the
separate comparison with Deligne.

Chapter Markdown and PDF layout extraction located the paragraph in the
[digest-verified edition](../sources/masullo/README.md). Raster OCR checked
the prose and direct inspection of the rendered formula checked the
conjugation bar and the inverse in its argument. PDF text extraction
alone loses the bar.

**Checked implication.** With the class-Haar convolution convention,
\[
(\psi*\psi^*)(x)=\int_{C_F}\psi(g)\,\overline{\psi((g^{-1}x)^{-1})}\,d\mu(g),
\qquad
(\psi*\psi^*)(1)=\int_{C_F}|\psi(g)|^2\,d\mu(g).
\]
Since $1\in C_F^1$, (1.7.2.1) makes the second integral zero. The
integrand is nonnegative and integrable for a Bruhat test, and Haar
measure is positive on every nonempty open set. Thus continuity forces
$\psi=0$ pointwise, and hence $\varphi=0$ pointwise. No condition on
any other norm-one value is needed for this intersection statement.

The claim is Masullo’s; the class-Haar calculation and Lean proof are
the reviewer’s. The Lean endpoint
[`Masullo.ideleClass_convolution_star_self_eq_zero_of_one`][lean]
uses an arbitrary number field, Borel measurable structure, class Haar
measure, and a continuous compactly supported complex factor. It unfolds
the convolution and involution, and assumes only vanishing at the
identity. These weaker hypotheses cover the printed Bruhat-test
implication with no isotype or Haar normalization restriction. It does
not prove Weil’s positivity criterion, exclude all possible uses of
positivity, or establish a trace comparison or a zero-location result.

**Review and checks:** The owning Yah session
`01a2066a-7188-70de-8481-807efc041fe1` records the independent
`square-statement-review` source and fixed-statement review, exact
candidate, module build, built signature, axiom report, and adoption.

[lean]: ../../Proofs/Theorems/IdeleClassConvolutionKernel.lean
