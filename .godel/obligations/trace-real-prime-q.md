# The real prime in the rational Chapter 13 trace

**Verdict:** The defining Fourier pairing gives **positive half Haar**
for the unsigned prime. Substitution of the displayed Fourier kernel
into that same definition gives **positive full Haar**. The printed
principal-value identification introduces a separate sign mismatch.
This is a local inconsistency on the actual common test kernel, not a
comparison of spectral sums.

## Source and domain

Use the [digest-matched Masullo edition](../sources/masullo/README.md).
The decisive formulas and their normalization cross-references were
checked in `pdftoppm` pixel crops, read as Braille cells:

- (B.4.4.1)–(2), pp. 619–620, give the **negative** of the additive
  Fourier pairing at the real place, with argument
  $u(z)=\varphi_\infty(1+z)|1+z|^{-1/2}$. The pairing itself is
  $\int J_v\widehat u\,d\nu_v$ by definition. The character reference
  in §B.4.3.1, p. 617, goes via Example A.3.1.8, p. 558, to
  Example A.3.1.5, p. 557, with self-dual Lebesgue measure and
  $e^{-2\pi iz\xi}$. Equation (B.4.3.12), p. 619, is $J_v=\log|\cdot|_v$.
- Definition A.3.2.2(1), p. 560, gives $d\mu_\infty(y)=dy/|y|$ on
  **both** components of $\mathbb R^\times$. Equation (B.4.4.4),
  p. 620, specifies $\mu_{\rm can}=\mu_\infty/M_\infty$, with
  $M_\infty=2$, not a change to the additive Fourier convention.
- The restriction is by the local embedding, as stated after
  (B.4.4.21), p. 625. The norm is the product of local norms by
  (A.1.3.3), p. 541, and descends by Definition A.1.4.1 and the
  ensuing norm discussion, p. 542. Thus the immersed local field
  sees its own normalized absolute value. The rational real norm
  is the usual absolute value by (A.2.2.2), p. 546; the finite
  norm image is $q_v^{\mathbb Z}$ by Remark B.4.4.2, p. 620, with
  $q_v$ the residue field size by Lemma A.3.2.3, p. 560, hence
  $q_v=p$ over $\mathbb Q$.

Take $f=b_1-b_2$ with nonnegative smooth real bumps of mass one,
with compact disjoint supports ordered from left to right inside
$(0,\log 2)$, and $\varphi(c)=f(\log|c|_{\mathbb Q})$. The
[accepted moment audit](trace-moment-codimension-q.md) verifies
membership in $\mathcal D(C_{\mathbb Q})$, the reduction of all
(13.3.1.2) moments to $\int f=0$ on radial tests, and the absence
of an explicit $1/2$ in (13.3.1.4), p. 522. The restrictions at
finite places are identically zero: No $p^m$ lies strictly between
$1$ and $2$. The real restriction $\varphi_\infty(y)=f(\log|y|)$
is supported away from both $0$ and $1$, so $u$ extends by zero
near $-1$, is compactly supported and smooth, and vanishes on a
neighborhood of $0$. In particular it is a Schwartz test for
(B.4.3.13) and (B.4.4.1), and all identity contact terms vanish.
The polar moments need not vanish and are not included in the local
comparison.

## Coefficients on a nonzero test

Put $R(f)=\int_{\mathbb R}u(z)\,dz/|z|$. Translation $y=1+z$ gives
$R(f)$ as the ordinary full-Haar kernel integral. Splitting into
$y=\pm e^x$ gives

$$
R(f)=2\int H(x) f(x)\,dx,\qquad
H(x)=\frac12 e^{x/2}\left(\frac{1}{e^x-1}+\frac{1}{e^x+1}\right)
    =\frac{e^{-x/2}}{1-e^{-2x}}\quad(x>0).
$$

$H$ is strictly decreasing, so $R(f)>0$ for the ordered bumps.
Zero mass does not hide a real coefficient or sign difference.

1. **Defining pairing.** Let $T(u)=\int\log|\xi|\widehat u(\xi)\,d\xi$.
   The accepted [`Masullo.real_log_fourier_off_zero`](../../Proofs/Props/RealPrincipalValue.lean)
   proves absolute integrability on both sides and $-T(u)=R(f)/2$
   for smooth compactly supported complex $u$ vanishing near zero.
   Thus the unsigned prime $P$ in (B.4.4.1)–(2) is $+R(f)/2$.
   An informal check uses
   $-\log|\xi|=\int_0^\infty(e^{-a|\xi|}-e^{-a})\,da/a$ for
   $\xi\ne0$. The first exchange is absolute by the fixed sign of
   the difference at each $\xi$ and integrability of
   $|\log|\xi||\,|\widehat u(\xi)|$. Fourier inversion at zero kills
   the $e^{-a}$ term. The transform of $e^{-a|\xi|}$ is
   $2a/(a^2+(2\pi z)^2)$, so the scale integral on the spatial side
   is $\int_0^\infty 2\,da/(a^2+(2\pi z)^2)=1/(2|z|)$; the second
   exchange is absolute by the support gap.
2. **Printed kernel.** The rendered (B.4.3.13), p. 619, has a
   minus before its cutoff limit, no $1/2$ multiplying the integral
   there, and the other terms are proportional to $u(0)$. For this
   test the limit stabilizes and its right side is $-R(f)$, whereas
   $T(u)=-R(f)/2$. Using that printed right side for $T$ and then
   negating as (B.4.4.1) requires gives $P=+R(f)$, full Haar.
3. **Printed comparison.** The rendered (B.4.4.20), p. 625,
   equates $P$ directly with $\mathrm{PF}_0$ and defines the latter
   by the **right sides** of (B.4.3.13) and (B.4.3.14). With the
   translated argument above this literal prescription is $-R(f)$,
   not $+R(f)$ and not $+R(f)/2$. Even if the full-Haar kernel were
   retained, the prose would need to prescribe its sign-adjusted
   value to agree with route 2. This sign mismatch is separate from
   the factor of two and precedes the external spectral minus sign.

The rendered (B.4.4.16), p. 623, subtracts $P/M_\infty$. Under
route 1 it would subtract $R(f)/4$, halving the already canonical
pairing again; under route 2 it subtracts $R(f)/2$. Under the literal
PF prescription in route 3 it would **add** $R(f)/2$. The p. 522
formula subtracts $P$ without the divisor. In particular, interpreting
the same prime consistently by its definition in both displays does
**not** make the geometric terms equal. The [repaired rational
radial explicit formula in Lean](../../Proofs/Theorems/RationalIdeleRadialExplicitFormula.lean)
subtracts the defining negative log-Fourier pairing once, not half
of it. Its real term agrees on these tests with the definition-first
reading of p. 522, not the definition-first reading of p. 623.

**Independent review:** `rVvatdi` separately inspected the rendered
pp. 619–625 and the character, Haar, and local restriction references.
The review confirmed the full-Haar substitution, the external divisor,
the nonzero two-bump test, and, on checking the p. 625 parenthetical
against the defining minus, the separate sign discrepancy.

## Scope and handoff

The local coefficient calculation needs only a smooth real restriction
compactly supported in $\mathbb R^\times$ away from $1$, not radiality,
mass zero, or $F=\mathbb Q$. The short rational band and
mass correction are what make the witness common to the printed trace
and explicit formula while killing every finite term. No contact term
can repair the detected mismatch. The source verdict combines rendered
readings with the accepted Lean pairing and the informal test transport;
there is no new Lean declaration or proof audit here.

The [raw-Haar pole test](trace-divisor-uniqueness.md#a-pole-test-for-the-raw-haar-reading)
remains conditional for the **kernel-literal** reading of p. 522,
compared with the correctly normalized full-zero distribution on the
wider positive half-line. Raw Haar is not the value of the defining
prime, and a short-band local test does not itself run that pole
argument. Do not subtract the two printed identities as though the
local terms had already been reconciled. This audit does not decide
the capped trace, the full-versus-capped zero sums, or the
[conditional zeta endpoint](../../Proofs/Props/ZetaTestSumComparison.lean).

**Next bounded source check (mapped):** On the same tests, compare
rendered (12.4.1.1), p. 514, and the real term of (12.4.1.25) and
(12.5.1.1), p. 519. Track the prime's reference to Proposition
B.4.3.2 and the passage through $y\mapsto y^{-1}$, which preserves
$|y|^{1/2}/|1-y|$ and $d\mu_\infty$. Check whether the real
coefficient in the cited geometric derivation uses the printed
full-Haar kernel or the defining negative Fourier pairing before
the external $1/2$. This constrains what Chapter 13 can inherit from
Chapter 12; it does not supply the global $s=2$ diagonal comparison
or either spectral equality.
