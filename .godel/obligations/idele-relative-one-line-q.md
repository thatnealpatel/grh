# Failure of idelic Lebesgue integrability on the relative 1-line

## Source checked on rendered pages

In the [pinned edition](../sources/masullo/README.md), Proposition
3.4.2.1, p. 145, calls (3.4.2.1) a **Lebesgue integral** over
$\mathrm{GL}_1(\mathbf A_F)$, asserts it is finite and continuous on
$L_A$, and identifies it with the restriction of $Z(f,c)$. The rendered
statement includes the norm powers $|\cdot|_F^{1+ix}$ with
$x\in\mathbb R\setminus(-A,A)$, without a zero-mode condition on $f$.
The proof passes from (3.4.2.1) to the product of local integrals
(3.4.2.2) and invokes Corollary B.7.2.5, p. 653. The rendered product
in (B.7.2.24) cuts off by $N(\mathfrak p)<x$, not by arbitrary finite
sets of primes. The distinction is not needed for the counterexample:
Even convergence along that norm-ordered exhaustion does not give a
finite complex Lebesgue integral.

For the measure input, compare the norm in (A.1.3.3), p. 541, and
the local finite-unit calibration and global restricted product in
(A.3.2.2) and (A.3.2.5), p. 560. The rational finite discriminant is
one at every place. The [accepted rational Haar note](theta-inversion-q.md#checked-finite-stage-product-of-local-haar-measures)
records the Lean measure comparison for these normalizations. It gives
$dt/|t|$ on the full real factor and mass one on the integral units
in each finite factor, including the product of the units outside a
finite stage.

## Prime shells and the right-half-plane control

Take $F=\mathbb Q$, $f(x)=e^{-\pi x_\infty^2}\prod_p1_{\mathbb Z_p}(x_p)$,
and $c(g)=|g|^{1+2i}$. The test is a Schwartz real function times the
finite integral indicator, of the tensor form allowed in the proof on
p. 145. The product formula lets the norm power descend to idele
classes. It is trivial on the norm-one classes and belongs to the
second part of $L_1$ since $2\notin(-1,1)$; it is not the pole at
$c=|\cdot|$. The integral itself is upstairs, on ideles, not on their
classes. Each normalized Haar shell

$$
E_p=[1,2]\times p\mathbb Z_p^\times\times\prod_{q\ne p}\mathbb Z_q^\times
$$

is Borel by the open single-prime stage embedding. The shells for
distinct primes are disjoint. Multiplicative translation gives
$\mu_p(p\mathbb Z_p^\times)=1$, not $1/p$. On $E_p$, the finite indicator
is one and $|g|=t/p$. For $s=\sigma+i\tau$ the absolute integral on
$E_p$ is therefore

$$
\int_{E_p}\bigl|f(g)\,|g|^s\bigr|\,d\mu(g)
=p^{-\sigma}\int_1^2 e^{-\pi t^2}t^{\sigma-1}\,dt.
$$

At $\sigma=1$ the integral on the right is a fixed
strictly positive factor times $1/p$. By countable additivity of the
nonnegative integral and divergence of the sum of prime reciprocals,
$\int |fc|\,d\mu=\infty$. A finite complex Lebesgue integral would
require $\int |fc|\,d\mu<\infty$. Being a Radon density on compact
sets does not address this global integrability condition.

For the same tensor at $c(g)=|g|^{2+2i}$, convergence on the test
shells alone would not prove the control. On the whole finite integral
support the finite valuation vector consists of nonnegative integers
$k_p$, finitely supported, and is indexed uniquely by $n=\prod_p p^{k_p}$.
Every such finite shell again has mass one and norm $|t|/n$ on the full
signed real factor. Tonelli gives the exact absolute integral

$$
\left(\int_{\mathbb R^\times} e^{-\pi t^2}|t|\,dt\right)
\sum_{n\ge 1} n^{-2}=\frac{1}{\pi}\sum_{n\ge 1} n^{-2}<\infty.
$$

More generally, this tensor is absolutely integrable precisely for
$\sigma>1$: The whole-shell calculation converges there, and the
single-prime calculation with $p^{-\sigma}\ge p^{-1}$ suffices at
$\sigma\le 1$. A unitary twist does not affect any modulus estimate.
These are ordinary mathematical calculations. They are independent of
the additive Fourier convention and do not refute the convergence
of (B.7.2.24) or the analytically continued zeta value. In fact, on
any fixed stage $S$ the integral is absolutely convergent for
$\Re s>0$: At each $p\in S$ one sums the geometric series of integral
valuation shells, and the off-$S$ units contribute one. Its complex
value is the signed real Gaussian Mellin integral times
$\prod_{p\in S}(1-p^{-s})^{-1}$. Thus the Corollary's order would
give an ordered limit of finite-stage integrals at $1+2i$, but that
is a different operation from (3.4.2.1) as printed. The above-one
absolute convergence claimed in Theorem 3.2.2.1(1), p. 124, is not
refuted (comparison to that theorem is based on the text extraction).

## Lean boundary endpoint

[Theorems.RationalIdeleRelativeOneLine](../../Proofs/Theorems/RationalIdeleRelativeOneLine.lean)
uses the unit-mass strip with real coordinate in $[1,e]$, rather than
$[1,2]$, so each of its translates by a single finite uniformizer
has mass one directly. They are disjoint Borel sets inside the tensor's
finite support. The proof lower-bounds the modulus on a prime shell by
$e^{-\pi e^2}/p$. The nonnegative integral of the Gaussian times the
idele norm is infinite on the full rational idele group with calibrated
Haar. Both `not_integrable_rationalIdeleGaussianZetaIntegrand_one_add_two_I`
and `not_integrable_rationalIdeleGaussianZetaIntegrand_of_re_eq_one`
state failure of complex Haar integrability itself, respectively at
$1+2i$ and for every $s$ with $\Re s=1$. They need only the Borel
instances and, in the second endpoint, the real-part equality. The
ordinary calculation above supplies the $2+2i$ control and the exact
threshold; neither is a Lean endpoint of this module.

To reproduce the boundary endpoint audit:

```sh
go run ./cmd/godel audit-local "$CANDIDATE" \
  Theorems.RationalIdeleRelativeOneLine -- \
  Masullo.rationalIdeleGaussian \
  Masullo.rationalIdeleGaussianZetaIntegrand \
  Masullo.norm_rationalIdeleGaussianZetaIntegrand_of_re_eq_one \
  Masullo.lintegral_rationalIdeleGaussian_mul_ideleNorm_eq_top \
  Masullo.not_integrable_rationalIdeleGaussian_mul_ideleNorm \
  Masullo.not_integrable_rationalIdeleGaussianZetaIntegrand_of_re_eq_one \
  Masullo.not_integrable_rationalIdeleGaussianZetaIntegrand_one_add_two_I
```

### Separation from the reflected-line proof

The Gaussian boundary obstruction does not supply a reflected Mellin
comparison. The relevant printed inputs for the next sign check are
(3.2.2.1)–(2), p. 124, and the proof on p. 126; their exact wording and
pairing convention are not verified here. Use the accepted [theta sign
check](theta-inversion-q.md#rendered-sign-check-a-translated-box-breaks-the-printed-theta-identity)
for the source verification of the transform, not as verification of
those later equations.

## Next bounded check

Return to the [odd conductor-three sign test](theta-inversion-q.md#rendered-sign-check-a-translated-box-breaks-the-printed-theta-identity):
Read the reflected character and any finite translation in (3.2.2.2),
p. 124, and its proof on p. 126, and test the value at
$\sigma=(1,-1,-1,\ldots)$ on a nonzero pairing. This would decide whether
the finite reflection changes the phase of the printed pairing. Those
Chapter 3 sign readings are still provisional. The general-field
identification of the Haar unit mass with the finite discriminant,
conductor assembly, completed-product identification, and contour
exhaustion are separate. The [checked finite local pairings](hecke-right-line-majorant.md#finite-local-zeta-pairings-with-the-haar-unit-mass-retained)
retain the unit mass as a parameter. No extension of (3.4.2.1) as a
Lebesgue integral may be used to fill those gaps.
