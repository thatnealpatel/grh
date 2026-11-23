# The zero-location inference needs the half-plane premise and a point check

**Printed passage.** Masullo, *The Music of the Primes*, printed p. 30,
claim in §1.4.5, the sentence beginning “This implies that.” From
holomorphy of $L'_f(s+1/2,\chi)/L_f(s+1/2,\chi)$ on
$\{\Re s>0\}\setminus\{1/2\}$, Masullo asserts that $L_f(u,\chi)$ and
then $L(u,\chi)$ have no zeros on $\Re u>1/2$. He applies the completed
claim to $\bar\chi$ and uses the functional equation to exclude zeros
of $L(u,\chi)$ on $\Re u<1/2$. This finding ends before the next
sentence, “This completes the overview.”

Chapter Markdown and layout extraction located the sentence in the
[digest-verified edition][edition]. Raster OCR checked the prose;
direct inspection of rendered crops checked the two inequalities and
the conjugation bar. On p. 123, layout extraction and raster OCR
located Proposition 3.2.1.3(3)–(4); rendered crops checked the reflected
argument and conjugation in (3.2.1.6), and the open strip in (4).

**Checked scope.** The argument is conditional and the zero-location
claim is **open here**. Use the p. 12 unitary base-point convention
($\chi=1$ in the trivial norm-one component) and require the [preceding
half-plane holomorphy][half-plane] for both $\chi$ and its dual. For a
zero $u_0$ of the non-identically-zero meromorphic $L_f(u,\chi)$,
write $L_f(u,\chi)=(u-u_0)^m g(u)$ near $u_0$, with $m>0$ and $g$
holomorphic and nonzero there. Its logarithmic derivative is then
$m/(u-u_0)+g'(u)/g(u)$, a nonremovable pole. The shift gives a pole at
$s=u_0-1/2$, so the punctured holomorphy excludes all zeros of $L_f$
with $\Re u_0>1/2$ **except possibly $u_0=1$**. It does not show that an
omitted point is a pole of $L_f$, rather than a zero.

For the passage from finite to completed, use the identity
$L=\Gamma_F L_f$, first on $\Re u>1$ by the definitions in §3.2.1 and
then meromorphically. The real factors have Gamma arguments
$(u+b+i\tau)/2$ with $b\in\{0,1\}$; the complex ones have arguments
$u+|n|/2+i\tau$, with $\tau$ real and $n$ integral. All arguments have
positive real part on $\Re u>0$. The Gamma factors and their
exponential normalizations are holomorphic and nonzero there, so
orders of the two functions agree on $\Re u>0$.

The omitted point $u=1$ needs a separate check: The
nonvanishing conclusion of Proposition 3.2.1.3(4), p. 123, *at $u=1$
only*, excludes a zero there for the completed function, so also for
$L_f$. This does not assume the desired exclusion in $1/2<\Re u<1$.
For the trivial representative the simple pole in part (2) also
suffices. For reflection, part (3) gives
$L(1-u,\bar\chi)=\epsilon(u,\chi)L(u,\chi)$ meromorphically, with
$\epsilon$ entire and nowhere zero. It preserves orders, so a
completed zero with $\Re u<1/2$ would give a zero with real part
$>1/2$ for the dual. This does not assert left-side zero exclusion
for the finite factor. The key open input is the half-plane
holomorphy of the same shifted logarithmic derivatives for both
characters, not the local deduction from such holomorphy. The trace
argument still needs a correctly normalized limiting identity with a
holomorphic remainder after removing the actual polar part for
arbitrarily small positive widths, matched to the logarithmic
derivative on the right-hand overlap. The sign error in the earlier
trace identity does not by itself refute the zero-location claim.

**Provenance.** Masullo supplies the argument from the logarithmic
derivative, completion, and reflection. The reviewer identifies the
omitted point and the independent right-edge input, and checks the
conditional argument. At Mathlib pin
`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`,
`meromorphicOrderAt_logDeriv_eq_neg_one` gives order $-1$ when the
original order is neither zero nor top. It does not assert
holomorphy for a Hecke logarithmic derivative.
`Masullo.localHeckeGammaFactor_real` and
`Masullo.localHeckeGammaFactor_complex` in the [completed-product
module][product] identify the actual local Gamma factors for a unitary
character; the same file checks their right-half-plane regularity
using the scalar Gamma lemmas. Its Euler product result is on
$\Re u>1$, not a continuation theorem. In the [trivial-character
reflection module][reflection], `Masullo.completedHecke_one_reflection`
gives a germ equality off $0,1$ for a trivial-character function
with the assumed right Euler-product match, entire pole-clearing
function, and specified representative data. It is not the
functional equation for arbitrary dual characters. Independent Yah
reader `zero-location-reader` (output
`a81d4d79fb38044fbfd2d9442b5a7ba6f7185020`) checked the rendered p. 30
sentence, the omitted-point and dual-character premises, and the Lean
signatures against GRH revision
`f13652ccf255e45200c301912c1291008e930455`. No new Lean theorem is
added, and no zero-location result is established.

[edition]: ../sources/masullo/README.md
[half-plane]: logarithmic-derivative-half-plane.md
[product]: ../../Proofs/Theorems/CompletedHeckeEulerProduct.lean
[reflection]: ../../Proofs/Theorems/CompletedHeckeOneReflection.lean
