# Polynomial growth of the finite Hecke reciprocal on the 1-line

**Status: Open at the formal scope.** Masullo, *The Music of the
Primes*, printed p. 31, §1.4.7, third bullet after “other properties
of $L_f(s,\chi)$ are also used,” announces that $1/L_f(s,\chi)$
grows at most polynomially over $1+i\mathbb R$. This is a separate
input from the [previous bullet](finite-hecke-reciprocal-good-heights.md)
about selected horizontal heights. Coverage stops before §1.4.8.

Chapter and appendix Markdown and numbered PDF layout extraction
located the passages in the [digest-verified edition](../sources/masullo/README.md).
Raster OCR checked the prose on pp. 31, 640, and 378. Inspection of
rendered crops checked the reciprocal and the line on p. 31, the
reciprocal in (B.6.1.22), the notation in (B.6.1.23), and the two
abscissa ranges on p. 640. The balancing calculation on p. 641 and
the surrounding jet formulas in §7.5 were read from extraction;
those readings are provisional.

## Statement and use

Theorem B.6.1.6, pp. 640–641, (B.6.1.22), asks for an exponent
$N>0$ for each fixed number field $F$ and unitary Hecke character
$\chi$, such that $|1/L_f(1+it,\chi)|\le C|t|^N$ at all
sufficiently large $|t|$. The input is an all-large-heights bound
on that one vertical line. It implies neither a bound on a
left vertical edge nor a selected horizontal segment estimate.
Ordinary finite-height boundary nonvanishing is a separate input.
At a shifted Dedekind pole the meromorphic reciprocal extends
with a zero, which does not give a finite nonzero diagonal for
ordinary jet multiplication by the original factor.

The proof of Theorem 7.5.0.1 explicitly cites Theorem B.6.1.6 and
Remark B.1.1.4 on p. 378 for a polynomial bound on the norm of
inverse jet blocks. The line estimate controls the reciprocals
of their diagonal values at large heights: Passing to the
outside-$S$ multiplier adds only finitely many local polynomial
factors of modulus at least $1-q_v^{-1}$ there, with the ramified
factors equal to $1$. Polynomial bounds on the other entries and
bounded block sizes are separate inputs. The line estimate does
not settle the exceptional finite-frequency jet orders or block
invertibility discussed in the [boundary preview](boundary-nonvanishing-preview.md).

## What still needs checking

Masullo's proof uses the trigonometric Euler-product inequality,
a right-of-line lower bound, and a derivative bound to transfer
that lower bound to the boundary. In the printed (B.6.1.23) the
two $L$ terms lack the finite subscript, although the justification
uses the finite Euler product and the later step needs the finite
functions. Check the finite-product inequality for the actual
characters $\chi$ and $\chi^2$ at imaginary parts $t$ and $2t$,
respectively, including the case where squaring removes local
ramification. Separately, (B.6.1.24) only states its upper bound
for $0\le\sigma\le1$; invoking it does not give the uniform
right-of-line bounds needed for (B.6.1.27)–(B.6.1.28).

For the transfer argument the missing estimates are a uniform
polynomial upper bound for $L_f(\sigma+2it,\chi^2)$ and a uniform
polynomial bound for $L_f'(\sigma+it,\chi)$ up to $\sigma=1$,
for $1\le\sigma\le1+\delta$ with fixed $\delta>0$ and large
$|t|$. The needed powers need not have the convexity exponents
printed in (B.6.1.28). A possible way to supply these inputs is
the [fixed-strip estimate](finite-hecke-polynomial-strip-growth.md)
for the actual continuations on a slightly wider strip, with
Cauchy's estimate for the derivative on disks free of poles at
large heights. This is a proposed repair to the cited step, not
a verification of the printed proof or its endpoint.

The accepted Lean declaration
`Masullo.finiteHeckeCharacterEulerProduct_lower_bound` in
`Proofs/Theorems/FiniteHeckeEulerProductLowerBound.lean` takes an
actual unitary Hecke character and bounds the finite Euler product
away from zero on $\Re s=2$. Its argument uses absolute convergence
on the right of the boundary; the signature neither supplies a
bound as $\sigma$ approaches $1$ nor concerns the continuation on
$\Re s=1$. No new Lean result is claimed.
