# The 1-line input and extension by zero

**Status: Open (scope of the analytic input and its use).** In *The
Music of the Primes*, printed p. 35, §1.7.2, second bullet, first
paragraph, Masullo says that properties of the Hecke $L$-function on
the 1-line, including nonvanishing, are used throughout, mostly to
pass from $S$-local theorems to global ones. The example of local
flexibility is extension of smooth compactly supported tests from
$\mathrm{GL}_1(\prod_{v\in S}F_v)$ by zero to Schwartz–Bruhat tests on
$\prod_{v\in S}F_v$, which he says fails globally. Coverage stops
before the next paragraph, beginning “This feels analogous.”

Chapter Markdown and PDF layout extraction located the passage in
the [digest-verified edition](../sources/masullo/README.md).
OCR of the rendered page checked the prose, and direct inspection
of raster crops checked “1-line” and “which fails globally.” The
later formulas cited below were located in Markdown and layout
extraction; details beyond the raster OCR checks are provisional.

## Scope of the extension example

For finite $S$, put $X_S=\prod_{v\in S} F_v$. Its unit set is open,
and a compact support in it stays compact and closed in $X_S$.
Thus zero extension is zero on a neighborhood of each boundary
point and is smooth at the Archimedean places and locally constant
in the non-Archimedean variables. The compactly supported extension
is Schwartz–Bruhat. Globally, every basic additive adele
neighborhood of an idele contains a nonidele: Set one coordinate
at a finite place outside the finitely many distinguished places
equal to zero, which still meets the integral restriction there.
Zero extension is therefore discontinuous at any idele where the
test is nonzero. This does not rule out the different operation of
tensoring an $S$-local additive test with integral-ring indicators
outside $S$; that operation makes no vanishing demand on nonideles.

## Scope of the analytic transfer

The more specific [§1.4.7 preview](boundary-nonvanishing-preview.md),
p. 30, identifies the boundary input as absence of zeros of the
meromorphic **finite** Hecke factor for unitary characters. Its
boundary assertion (as distinct from a quantitative zero-free
region) is the input needed from Proposition B.6.1.1, p. 636.
Absence of zeros does not mean finite and nonzero at a shifted
Dedekind zeta pole.

For a concrete transfer, rendered OCR on pp. 374 and 378 confirms
that §7.5 invokes boundary nonvanishing for the comparison of
orbital jet blocks and invokes Theorem B.6.1.6, p. 640, for growth
of the inverse block norms at large heights. The provisional reading
of (7.5.0.9)–(13) places the diagonal of the block at the outside-$S$
factor evaluated at the reflected Euler-zero frequency $1-s_c$.
For the trivial character $s_c=0$ can occur, while the outside-$S$
factor has a pole at $1$. The missing step is a finite, invertible
comparison on the two-zero-moment isotype at the exceptional
frequency, with the resulting jet orders justified after pole
cancellation. Large-height polynomial control of the reciprocal
of $L_f$ does not settle that block. The claim of use “throughout”
is not itself a dependency analysis of the main trace calculation:
The opening of §7.5, checked by raster OCR on p. 374, explicitly
says its results and those of the next subsection are not logically
necessary for that calculation.

The proposed uses are Masullo's; the compact-support and neighborhood
arguments, and the distinction between absence of zeros and ordinary
jet invertibility at a pole, are the reviewer's checks. The accepted
Lean declaration `Masullo.finiteHeckeCharacterEulerProduct_logDeriv`
in `Proofs/Theorems/FiniteHeckeCharacterEulerProduct.lean` gives
nonvanishing, differentiability, and the logarithmic derivative
expansion of the unitary-character Euler product for $\Re s>1$.
It supplies neither a boundary input nor a topological transfer of
orbital bases. No new Lean result is claimed.
