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

## The Chapter 12 real coefficient

**Verdict:** On the witness above, the sharp scalar displayed in
(12.4.1.24), p. 518, has limit $+R(f)/2$. The real contribution in
(12.4.1.25), p. 519, is $+R(f)/4$ using the **defined** prime.
Substituting the **printed full-Haar kernel** (B.4.3.13), p. 619,
reproduces the scalar coefficient but does not evaluate the defined
prime. This is a discrepancy in the local inference, not a
calculation of the Paley–Wiener trace or the global diagonal.

**Domain and measures.** Theorem 12.4.1.1, p. 514, has the $S$-class,
ramification, and outside-$S$ unit-invariance hypotheses. With
$F=\mathbb Q$ and $S=\{\infty\}$ the ring in §A.1.5.1, p. 543, is
$\mathbb Z$, so the class group is trivial, and there are no ramified
finite places. The test factors smoothly through the positive norm
coordinate, is invariant under the outside-$S$ units, and has compact
support by the rational splitting in (A.2.2.2)–(4), p. 546; see the
[accepted domain check](trace-moment-codimension-q.md). The rendered
Theorem 12.5.1.1, p. 519, requires $\varphi(C_F^1)=0$, not just zero
mass. The support gap ensures this, and the mass condition is for the
shared Chapter 13 test. The band in the proof on p. 520 can be chosen
with $T<2$. The local norms give zero restrictions at all finite
places, as checked above; this does not evaluate the omitted finite
orbital traces.

Here $G=\mathbb R^\times$, $U=\{\pm1\}$, and $J_{F,S}=G/U$ by
Remark 4.3.1.2, p. 175. Definition A.3.4.1, p. 561, gives the local
product measures and disintegration against $dt/t$. For the quotient
$J_{F,S}$, Proposition 12.2.2.2, p. 508, uses counting measure on the
discrete subgroup and the quotient rule (D.1.2.1), p. 747. This uses
the quotient specified by the measures, not the $C_{F,S}$ label in
Definition A.3.4.1(3). The real Haar $dy/|y|$ is
$dt/t$ on **each** ray by Definition A.3.2.2(1), p. 560, with
Lebesgue self-dual for the real character (Example A.3.1.5, p. 557,
and Remark A.3.4.2, p. 562). Its norm-one measure gives each of
$\pm1$ mass one. Quotienting by **counting**, rather than probability
Haar, on $U$ gives $dt/t$ on $J_{F,S}$, and hence
$V=\overline\mu_{S,1}(J_{F,S}^1)=1$. The radial band on a single
representative ray has measure $\log(\lambda\lambda')-\log|w|$.
The $E_{S,0}$ of (A.2.4.5), p. 554, is a **norm-one** domain;
the band calculation uses its radial extension (A.4.1.7), p. 563;
see the [project scalar calculation](trace-scalar.md).
Evaluating (12.4.1.24) as printed does not validate (12.4.1.23) with
its domain literally restricted to $E_{S,0}$.

**Scalar route.** Set $h(y)=f(\log|y|)$ and
$\widetilde\varphi(y)=\mathbf{1}_{y>0}h(y)$. Its counting periodization
is $h$, as required by (12.4.1.4), p. 515. In (12.4.1.17)–(21),
p. 518, $c_S=1$ and
$\eta_\xi(z)=|1+z|^{-1/2}\widetilde\varphi(\xi/(1+z))$.
Sum over **both** signs, each once. The resulting additive test is
$U_*(z)=|1+z|^{-1/2}h((1+z)^{-1})$, extended by zero near $-1$.
It is smooth, compactly supported, and vanishes near $0$, as does
each summand. Thus its Fourier transform is Schwartz with
$\int\widehat U_*(w)\,dw=U_*(0)=0$. For $L=\lambda\lambda'$, the
term $\log L\int_{|w|\le L}\widehat U_*\,dw$ tends to zero by rapid
decay on the omitted tail. The log pairing converges absolutely,
including at $w=0$. Therefore the sum of (12.4.1.24) tends to

$$
-V\int_{\mathbb R}\log|w|\widehat U_*(w)\,dw
=\frac V2\int_{\mathbb R}\frac{U_*(z)}{|z|}\,dz
=\frac{VR(f)}2.
$$

The middle equality uses the accepted `Masullo.real_log_fourier_off_zero`
with the checked smoothness, compact support, and gap. Reversal of
the Fourier sign would reflect $w$ and leave these even-weight
integrals unchanged. For the last equality, set $y=1+z$ and invert
$y\mapsto y^{-1}$, which preserves $dy/|y|$ and
$|y|^{1/2}/|1-y|$. Inversion is not an assumption that $h$ itself is
inversion invariant. This scalar and inversion calculation also works
for any smooth compactly supported profile on the positive norm
coordinate vanishing near norm one. The short band and the two unit
masses are only for the common, nonzero, finite-term-free witness.

**Two readings of the printed next step.** The rendered (12.4.1.25)
uses $V\cdot\frac12\int'_{F_v^\times,\alpha_{v,0}}$ on the inverted
restriction. Definition B.4.4.1, (B.4.4.1)–(2), pp. 619–620,
identifies that prime with the same negative Fourier pairing on
$U_*$. It is $R(f)/2$ *before* the exterior $1/2$. Substituting the
right side of (B.4.3.13), p. 619, instead gives $-R(f)$ for the
pairing and thus $+R(f)$ for the prime before the exterior $1/2$.
The cited Lemmas B.4.4.3 and B.4.4.5, pp. 620 and 622, concern
non-Archimedean places. Proposition B.4.3.2, p. 619, is the remaining
cited dependency and contains the disputed display. Neither the
norm-one quotient volume, inversion, nor a contact term supplies
another factor of two here.

The normalized (12.4.1.1), p. 514, and the geometric left side
(12.5.1.1), p. 519, both retain $\frac12\int'$ with the uninverted
restriction; neither display writes the character subscript. In the
route from (12.4.1.25) the values are thus $R(f)/4$ with the definition
and $R(f)/2$ with the kernel substitution. The reading $R(f)/2$ can
be written as the **defined prime once** on this class; deleting the
extra $1/2$ would repair this scalar comparison if the defined prime
is used. This is not the Appendix B printed $\mathrm{PF}_0$ sign
prescription. The no-extra-divisor (13.3.1.4), p. 522, agrees locally
with this scalar on a definition-first reading, but this does not
license subtracting the printed trace and explicit formulas. The
claim on p. 520 after (12.5.1.1)–(3) about the global $S$-diagonal
and two Mellin terms is a separate, still unproved identification.

**Evidence and review.** The Chapter 12 displays and relevant
normalization references were checked in rendered PDF crops of the
pinned edition. Independent reader `tDvKqpX` separately checked the
scalar via the integrated Laplace kernel
$\int_0^\infty 2\,da/(a^2+4\pi^2z^2)=1/(2|z|)$, checked applicability
of the accepted Lean endpoint to the defining prime at source base
`958d16563bf172c9989f9270ac688c6c707bb0c6`, and checked the printed
kernel substitution from rendered pp. 619–620. The three findings
agree with the calculations above and do not identify the defining
pairing with the printed right side. The reviewer also confirmed
the quotient volume, statement hypotheses, and exterior halves on
pp. 514 and 519. The earlier Chapter 13 domain and Appendix B sign
findings above are inherited from their accepted notes. The scalar
limit and test transport are informal; no Lean changed.

### Lean-checked sharp limit without a support gap

The [sharp Fourier cutoff module](../../Proofs/Props/RealSharpFourierCutoff.lean)
proves `Masullo.real_log_profile_sharp_fourier_tendsto`. For smooth
compactly supported $f:\mathbb R\to\mathbb C$ with $f(0)=0$, take
$u=\texttt{realLogProfileAdditive}(f\circ(-\mathrm{id}))$. The definition
extends $|1+z|^{-1/2}f(-\log|1+z|)$ by zero at $z=-1$; compact log
support makes it zero near that extension point, not necessarily near
$z=0$. With Lebesgue measure and the standard additive Fourier transform,

$$
\lim_{L\to+\infty}\int_{|w|\le L}(\log L-\log|w|)\widehat u(w)\,dw
=\frac12\int_{\mathbb R}\frac{u(z)}{|z|}\,dz.
$$

The reusable `Masullo.real_log_fourier_sharp_tendsto` assumes only
continuity, $u(0)=0$, and integrability of $u$, $\widehat u$,
$\log|\cdot|\,\widehat u$, and $u/|\cdot|$. Fourier inversion at zero
turns the $\log L$ term into a negative omitted tail. For $L\ge1$,
its norm is bounded by the tail integral of
$\|\log|w|\,\widehat u(w)\|$, which tends to zero. The retained log
pairing exhausts the line, so `real_log_fourier_of_zero` supplies the
coefficient. The profile wrapper uses the accepted smooth compact
additive test, its Schwartz lift, and `remainder_div_integrable` with
$u(0)=0$. No gap at norm one or moment assumptions are needed. At
radius zero, `translate_cutoff` and `density_cutoff` identify the
spatial integral with the full two-sign Haar integral of
`realLogProfileHaarKernel (fun t ↦ f (-t))`; neither change of variables
adds a half. Inversion gives the uninverted $R(f)$ as above.

**Source interface and review.** The rendered reading above supplies
the sign sum in (12.4.1.17)–(21), the scalar band in (12.4.1.24),
p. 518, and the counting-measure normalization $V=1$. Reversing the
Fourier sign reflects the symmetric band and does not affect the limit.
The same reading separately supplies the exterior half in (12.4.1.25),
p. 519; the Lean limit does not justify that step with the defined
prime. The rendered passages were inherited, not reread. Independent
exact-source review (`RYTvBVm`, Yah `01a205f3-2f52-7660-aae5-430d791e231d`)
checked both signatures, the applicability of those inherited clauses,
and the Fourier, integrability, and Haar reductions at
`2757bdce50e8b38fe4a09dab9cd19bb761b7a2ee`. The owning build, fresh
joint-import signatures and axioms, and adoption are recorded in Yah
`01a205f3-2f52-7660-aae5-430d791e231d` against the exact candidate.

**Next bounded check:** On the repaired radial domain, check whether the
cutoffs in (12.4.1.12), p. 517, and (12.4.1.15), p. 518, control the
lower edges well enough for the sharp replacement in (12.4.1.22),
p. 518. These weight and replacement clauses are still extraction-only
in the [smooth-band note](trace-geometric.md#smooth-radial-bands-on-the-extended-domain).
The radiality clause of Definition 9.3.3.1(2), p. 427, has a separate
[rendered reading](trace-circle-compression-qi.md#chapter-12-interface);
it does not determine the endpoint rates or which cutoffs Step II uses.
In the same real modulus coordinate, the existing informal comparison
already reduces the repaired weighted scalar to differences of sharp
integrals. It controls the lower terms if $A_+D_+\to0$ and, with a lower
Fourier edge, $B_+C_+\to0$; independently growing cutoffs do not imply
these products vanish. The sharp limit above evaluates the surviving
upper term. Check the printed lower-edge prescription against this
comparison rather than rederive the sharp limit. The identification
of the volume domain in (12.4.1.23), the actual geometric operator, the
global $S$-piece, and the Mellin corrections remain separate premises.
