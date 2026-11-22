# The printed global Mellin reflection over Q

**Result.** For the odd quadratic idele-class character of conductor $3$
and $c=\chi|\cdot|^{-1}$, the continued left side of (3.2.2.2), p. 124,
is positive on the test below. Its printed right side is the negative of
that number. The failure is for the combined printed definitions, not
for the functional equation with the diagonally trivial Fourier kernel.
The specific nonvanishing and analytic continuation are ordinary
mathematics. Lean checks the general change of variables in the pairing.

## What the source prints

Checked against the [digest-pinned edition](../sources/masullo/README.md):
Chapter 3 Markdown and numbered layout located the passages, then
Poppler-rendered page crops were inspected, with pixel-based OCR as a
cross-check. Equation (3.1.1.4), p. 119, prints
$\widehat c=|\cdot|_G c^{-1}$. Equation (3.2.2.1), p. 124, integrates
$f(g)c(g)$ over $\mathrm{GL}_1(\mathbf A_F)$ with $d\mu(g)$ and gives the
initial domain $\sigma(c)>1$. Equation (3.2.2.2), p. 124, asserts exactly
$Z(f,c)=Z(\widehat f,\widehat c)$, with no translate, conjugate on the
integrand's character, or scalar. Part (1) of the proof on p. 126 checks
above-one integrability, invokes its cited continuation theorem, and
asserts (3.2.2.2); it supplies no change of Fourier convention. This is
a check of Masullo's citation step, not a check of the cited text.
The specialization of $|\cdot|_G$ to the idelic norm on $C_F$ in
§3.1.2, p. 120, is a layout reading; the calculation uses the standard
rational idelic norm, including the product formula on $\mathbb Q^\times$.

The identification of his $\widehat f$ with $\mathcal F f(\sigma\,\cdot)$,
where $\mathcal F$ is the repaired Fourier transform and
$\sigma=(1,-1,-1,\ldots)$, uses the earlier
[rendered Fourier check](theta-inversion-q.md#rendered-sign-check-a-translated-box-breaks-the-printed-theta-identity)
of (2.2.4.32), p. 92, and Examples A.3.1.5–8, pp. 557–558. The finite
conjugation is a repair, not a sign read into Chapter 3. The rational
Haar normalization in (A.3.2.2) and (A.3.2.5), p. 560, was checked on
the rendered page in the [relative 1-line note](idele-relative-one-line-q.md).
The broader p. 556 stage-restriction reading remains layout-only. The
calculation uses the actual calibrated rational Haar and its checked
product restrictions; it does not use a general-field identification
from p. 556 or the printed convergence and continuation proof.

## An odd character and an absolutely convergent witness

Let $\eta$ be the nontrivial character on $(\mathbb Z/3\mathbb Z)^\times$.
Use the local components $\chi_\infty(t)=\operatorname{sgn}(t)$,
$\chi_3(3^n u)=\eta(u\bmod 3)$, and
$\chi_p(p^n u)=\eta(p\bmod 3)^n$ for $p\ne3$ and integral units $u$.
They give a continuous quadratic character on the restricted product.
For a diagonal rational $r=\epsilon 3^a\prod_{p\ne3}p^{n_p}$, the
$3$-unit component contributes $\eta(\epsilon)\prod_{p\ne3}\eta(p)^{n_p}$;
this cancels the real sign and the other local factors since they are
quadratic. Thus $\chi$ descends to classes. The finite conductor is
exactly $3$: All other finite unit groups act trivially, and at $3$ it
is nontrivial on the units but trivial on $1+3\mathbb Z_3$. In particular
$\chi(\sigma)=-1$ and $\widehat c=\chi^{-1}|\cdot|^2$ has the same value
at $\sigma$, which has norm one.

Put $h=b\otimes(\chi_3 1_{\mathbb Z_3^\times})\otimes
\bigotimes_{p\ne3}1_{\mathbb Z_p}$, with $b(x)=xe^{-\pi x^2}$, and
$f=\mathcal F^{-1}h$. These are finite sums of adelic boxes with real
Schwartz profiles. At $3$, the factor of $h$ is the difference of the
$1+3\mathbb Z_3$ and $-1+3\mathbb Z_3$ indicators. Its inverse factor
is $3^{-1}1_{3^{-1}\mathbb Z_3}(y)(\psi_3(-y)-\psi_3(y))$ for the
positive residue phase $\psi_3$: Translate the ball, whose Haar
integral is its mass on the annihilator and zero elsewhere. This
inverse factor is constant mod $\mathbb Z_3$ and vanishes except on
the two nonzero cosets. The other finite unit balls are fixed. The real
inverse Fourier profile is Schwartz and odd. The accepted [pointwise Schwartz inverse](../../Proofs/Theorems/RationalAdeleLFFourierInversion.lean)
is the forward integral at the negative argument; in particular
$\mathcal F f=h$. Both zero modes vanish: $f(0)=0$ and $h(0)=0$.
This use of inverse Fourier does not require a ramified local functional
equation or a Gauss-sum value.

With $dt/|t|$ on both real rays and finite multiplicative unit mass
one, partition the finite support of $h$ by valuations, which are
zero at $3$ and arbitrary nonnegative with finite support elsewhere.
Haar translation shows that each unit shell has mass one. The real
integral is positive and absolutely convergent:
$$
2\int_0^\infty t^2 e^{-\pi t^2}\,dt=\frac{1}{2\pi}.
$$
The $3$-factor contributes $1$ because $\chi_3\chi_3^{-1}=1$ on the units.
At $p\ne3$ the local sum is $(1-\eta(p)p^{-2})^{-1}$. The product of the
absolute shell sums converges since $\sum_p p^{-2}<\infty$, and the
signed factors are positive with absolutely summable logarithms. Thus
$$
M:=Z(h,\widehat c)=\frac{1}{2\pi}
       \prod_{p\ne3}(1-\eta(p)p^{-2})^{-1}>0.
$$

## Identify the continued left side independently

On $C_{\mathbb Q}$ write $\Theta_u(k)=\sum_{q\in\mathbb Q^\times}u(qk)$.
The accepted [class theta inversion](../../Proofs/Theorems/RationalAdeleClassThetaInversion.lean)
on the box span gives $\Theta_f(k)=|k|^{-1}\Theta_h(k^{-1})$ since both
zero modes vanish. The checked [two-sided tails](../../Proofs/Theorems/RationalAdeleThetaTails.lean)
give $O(e^{-N|\log |k||})$ for each $N$ for both tests. The quotient
measure has compact norm-one part of mass one and Lebesgue log-norm
factor. Therefore $\int_{C_{\mathbb Q}}\Theta_u(k)\chi(k)|k|^s\,d\bar\mu(k)$
is entire in $s$ by domination on compact parameter sets (including
log-norm powers for differentiation). For $\Re s>1$ it unfolds to
$Z(u,\chi|\cdot|^s)$: Sum over the principal translates of the
positive-real finite-unit fundamental domain with the restriction of
upstairs Haar inducing quotient Haar. For $h$ absolute integrability
is the shell bound above with $2$ replaced by $\Re s$; for $f$ only the
$3$-shell changes (from valuation $0$ to $-1$), with bounded factors
there and real Schwartz decay. Thus this class integral gives the
unique continuation of (3.2.2.1) for these tests. With $k\mapsto k^{-1}$,
which preserves the quotient Haar, repaired theta inversion sends the
class integral at $s=-1$ for $f$ to that at $s=2$ for $h$ with $\chi^{-1}$.
Unfold the latter where it converges absolutely to obtain $Z(f,c)=M$,
without invoking (3.2.2.2).

## Haar translation and scope

For the printed transform, change variables $g=\sigma y$ upstairs.
Because $\sigma^2=1$, Haar is invariant, and $\widehat c$ is
multiplicative, the right side of (3.2.2.2) is
$$
Z(\widehat f_{\rm print},\widehat c)
 =\widehat c(\sigma) Z(\mathcal F f,\widehat c)=-M.
$$
Absolute integrability of the printed right side follows from the same
translation and $|\widehat c(\sigma)|=1$. The opposite values cannot be
changed by a common positive rescaling of multiplicative Haar. Replacing
the printed transform by the repaired one fixes the comparison. If the
printed transform is retained, one must translate it by $\sigma$, or
multiply its pairing by $\widehat c(\sigma)$ on the right. Neither is
printed. More generally $\sigma$ represents the same class as
$(-1,1,1,\ldots)$, by multiplication by the diagonal $-1$. For any rational
idele-class quasi-character the phase in the pairing is exactly its real
parity, independent of the norm twist. The witness tests an odd isotype;
an even isotype has no phase change from this translation. The constant
phase by itself also disappears on logarithmic differentiation. It does
not decide the conductor power, completed product, or contour estimates.

[Lean](../../Proofs/Theorems/RationalAdeleSameSignMellin.lean) checks
`Masullo.integral_rationalAdeleSameSignFourier_mul_char` for arbitrary
adelic input $f:A\to\mathbb C$ and monoid homomorphism
$d:J\to\mathbb C$ on the full rational idele group, with their Borel
structures and calibrated Haar. It uses the accepted Fourier frequency
relation and the norm-one involution, and does not require continuity or
absolute integrability for its equality of totalized Bochner integrals.
It does not formalize this character, its parity, the positive Euler
value, or the analytic continuation argument. Recheck with
`go run ./cmd/godel audit-local <candidate> Theorems.RationalAdeleSameSignMellin -- Masullo.integral_rationalAdeleSameSignFourier_mul_char`
and a fresh import and `#check` of the same declaration.

## Successor checks

The [rendered complex Gaussian check](complex-gaussian-angular.md)
confirms the same-weight zero against the nonzero Gamma value and
separates the opposite-weight scalar repair from the pullback action.
The [finite normalization check](finite-gaussian-tamagawa.md) then
compares the local Tamagawa pairing with the Euler convention at the
place over 2 of $\mathbb Q(i)$. The
[checked modulus-three Fourier shell](hecke-right-line-majorant.md#ramified-local-conductor-power-the-modulus-three-test)
is a separate local result, not an input to either check.
