# The boundary nonvanishing preview

**Status: Open (scope and use).** Masullo, *The Music of the Primes*,
printed p. 30, §1.4.7, opening paragraph ending “boundary of their
critical strips.” Masullo says that nonvanishing of the finite Hecke
$L$-function $L_f(s,\chi)$ on $1+i\mathbb R$ is used, and compares the
role of this input to boundary nonvanishing in Deligne's proof. This
is a preview of an input, not a proof or a use of Deligne's argument.
Coverage here stops before “For example, assume $S$.”

Chapter Markdown and PDF layout extraction located the paragraph in the
[digest-verified edition](../sources/masullo/README.md). Raster OCR
checked the prose, and direct inspection of rendered crops checked the
finite subscript, function arguments, and line $1+i\mathbb R$. The
later manuscript passages cited below were consulted in extraction,
not checked on rendered pages.

**Input and uses to check.** The boundary input is absence of zeros for
unitary Hecke characters, not that the meromorphic function is finite
at every point of the line. For a norm twist of the trivial character,
there is a shifted Dedekind zeta pole there. The reciprocal extends
with a zero at that pole; division across it and inversion of a
finite jet block at it are different operations.

- Proposition B.6.1.1, p. 636, is the manuscript's classical zero-free
  region reference. The preview needs only the boundary consequence
  for each unitary character, not the quantitative region.
- Theorem 7.1.4.3, pp. 331–332, invokes boundary nonvanishing to
  separate completed Hecke zeros from the zeros of reciprocal local
  Euler factors. Check this disjointness for the actual pole-cleared
  divisor on the trivial norm-one isotype as well.
- Theorem 7.5.0.1, p. 374, uses the input in its proof on pp. 376–378.
  The triangular comparison (7.5.0.9)–(13) reads ordinary derivatives
  of the outside-$S$ factor at reflected Euler-zero frequencies.
  If that factor has a pole there, nonvanishing does not give a finite
  invertible block. In the trivial character, an unramified local
  reciprocal factor vanishes at $s_c=0$, so the reflected point can
  be $1$. What is needed at such a frequency is the correct comparison
  after using the two vanishing moments, including the orders of the
  jets and invertibility of the resulting block. The large-height
  estimate of Theorem B.6.1.6, p. 640, does not handle this finite
  frequency. Section 7.5 itself says it is not logically necessary
  for the main trace calculation, so this use should not be promoted
  into a necessary step in that calculation.

**Provenance and checked scope.** The announced use and the later
arguments are Masullo's. The pole distinction and the need to check
exceptional jets are the reviewer's audit, not a refutation of the
comparison or of classical boundary nonvanishing. The accepted
[`Masullo.finiteHeckeCharacterEulerProduct_logDeriv`](../obligations/hecke-right-line-majorant.md#the-finite-product-of-an-actual-hecke-character)
proves differentiability, nonvanishing, and the logarithmic derivative
expansion for the Euler product of a unitary character on $\Re s>1$.
It neither gives meromorphic boundary nonvanishing nor checks the jet
comparison. No new Lean result is claimed.
