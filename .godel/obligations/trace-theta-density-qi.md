# One Gaussian generates compact frequency tests in the weight-four theta closure

**Result (ordinary mathematics, not Lean).** Let $G=C_{\mathbb Q(i)}$,
$K=\prod_{w<\infty}\mathcal O_w^\times$, and
$\eta([z,u])=(z/|z|)^4$ in $(\mathbb C^\times\times K)/\mathbb Z[i]^\times$.
Put $a=1/2$, $I=\{0\}$, and Sobolev index $s=4$. Let $M_{1/2}$ be
Masullo's closed twisted theta space (10.1.1.3), PDF p. 434, in the
singleton quotient (10.2.1.1), p. 439. Use the left action
$U_g f(y)=f(g^{-1}y)$ and the full $G^1$-isotype with action character
$\bar\eta|_{G^1}$. Write such functions as $\eta(g)q(\log|g|_F)$ and
transform their profiles by
$\mathcal F_+q(t)=\int_{\mathbb R}q(x)e^{itx}\,dx$, extended on $L^2$.
Then

$$
L(1/2+it,\bar\eta)v(t)\ \in\ \mathcal F_+(M_{1/2}\cap\text{isotype})
\qquad(v\in C_c^\infty(\mathbb R)).
$$

Here $L$ is the continuation of the completed Euler product in
(3.2.1.2)–(5), p. 123, not a raw local Gaussian calibration. The result
also holds for every Schwartz $v$, and the same proof works for any
real twist $a$ and any nonnegative polynomial weight index $s$ in
the singleton space, with $1/2$ replaced by $a$. No strip-norm
inclusion at positive width is claimed.

## Source interface

The SHA-256 of the local PDF matches the [pinned edition](../sources/masullo/README.md).
The worker read Chapter 2, 3, and 10 Markdown, compared numbered layout,
and inspected Poppler pixels for the following definitions and steps:

- (2.2.3.1), p. 81, uses the sum over $F^\times$ on a representative,
  and (2.2.4.23), p. 91, requires $f(0)=\widehat f(0)=0$. Evaluation
  at zero in the adelic Fourier integral convention used in
  (2.2.4.32), p. 92, is the additive integral; the phase sign is
  immaterial there. For the printed phase convention and the distinct
  inversion issue see the
  [accepted rendered sign check](theta-inversion-q.md#rendered-sign-check-a-translated-box-breaks-the-printed-theta-identity).
- (3.2.1.2) and (3.2.1.5), p. 123, combine the finite Euler product
  and the complex factor $(2\pi)^{-(\lambda+|n|/2)}\Gamma(\lambda+|n|/2)$.
  The symbol $\lambda$ here denotes the complex Mellin exponent, not
  the ambient index $s=4$. The normalized norm in the argument
  $\chi_w|\cdot|_w^\lambda$ is $|z|^2$. This uses the rendered
  p. 121 norm convention from the [accepted angular Gaussian note](complex-gaussian-angular.md#rendered-readings),
  not an inference that the ambiguous prose $r^\lambda$ in p. 123
  uses Euclidean radius. The local character is restriction, and
  finite ramification is tested on integer units, as reviewed in the
  [accepted finite normalization note](finite-gaussian-tamagawa.md#source-and-the-two-readings-of-l_v).
- (3.2.2.3), p. 124, is the bilinear quotient-Haar Mellin integral,
  with $c(g)$ rather than its conjugate or inverse. Theorem 3.2.2.1(2a)
  gives absolute convergence and entireness when both zero modes
  vanish. Equation (3.2.2.11), p. 127, unfolds above one to the
  upstairs integral. The calculation below also proves the required
  analytic continuation independently, without (3.2.2.2) or the
  printed adelic inversion formula.
- (10.1.1.1)–(3), p. 434, multiply the theta function by
  $|\cdot|_F^a$ and take the ambient norm closure. We inherit the
  singleton quotient, weight (9.1.2.3), p. 399, and left action
  in §9.3.1, p. 419, from the [accepted angular operator check](trace-spectral-angular-qi.md#test-and-source-interface).
  Its [class-model input](trace-circle-compression-qi.md) applies to
  this same field and pin. In particular, $|[z,u]|_F=|z|^2$ since
  $u$ is a finite unit, and fourth powers are trivial on diagonal
  Gaussian units. No quotient-volume calibration is needed below.

## The zero modes and the completed Mellin factor

Let $b(z)=z^4 e^{-2\pi |z|^2}$ and
$f=b\otimes\prod_{w<\infty}1_{\mathcal O_w}$, a Schwartz–Bruhat tensor.
Clearly $f(0)=0$. The finite additive factors have finite mass, and
$\int_{\mathbb C}b(z)\,dz=0$ for additive Haar: Rotate by $e^{i\pi/4}$,
which changes the sign of $b$. Thus $\widehat f(0)=0$ by Fubini. Neither
vanishing uses a finite self-duality assertion at the place over $2$.

Take the positive radial section $\sigma(x)=[e^{x/2},1]$,
$x=\log|g|_F$. On the class representative $(z,u)$, the finite
indicator in $f(\alpha(z,u))$ selects exactly
$\alpha\in\mathbb Z[i]\setminus\{0\}$: The local components $u_w$ are
units. Consequently $\Phi_F(f)(g)=\eta(g)P(x)$, where

$$
P(x)=\sum_{0\ne\alpha\in\mathbb Z[i]}b(\alpha e^{x/2}).
$$

In particular the twist $|g|_F^{1/2}\Phi_F(f)(g)$ has profile
$q(x)=e^{x/2}P(x)$ and left-action weight $\bar\eta$, since
$U_h(\eta q)=\eta(h)^{-1}\eta q$ for $h\in G^1$. The bilinear Mellin
integral at $c=\bar\eta|\cdot|_F^\lambda$ cancels the pointwise
$\eta$, rather than inserting another copy of it. With quotient Haar
written $d\bar\mu=dm_{G^1}\,dx$, the class integral is
$m_{G^1}(G^1)\int P(x)e^{\lambda x}dx$. Write $C=m_{G^1}(G^1)>0$.

Above one the unfolding (3.2.2.11) can also be computed directly
by integrating each lattice term on the norm line. For
$\Re\lambda>1$, substitution $y=e^x|\alpha|^2$ gives

$$
\int_\mathbb R b(\alpha e^{x/2})e^{\lambda x}dx
= (\alpha/|\alpha|)^4\,|\alpha|^{-2\lambda}
  (2\pi)^{-(\lambda+2)}\Gamma(\lambda+2).
$$

The integral with absolute values is bounded by the same expression
with phase removed and $\lambda$ replaced by $\Re\lambda$; the
sum is finite by the lattice dimension two. Each nonzero integral
ideal has four generators. At a prime $\mathfrak p=(\pi)$, the class
with a uniformizer at $\mathfrak p$ and ones elsewhere has an
integral-unit representative with complex coordinate $\pi^{-1}$:
Divide by the principal idele $\pi$. Its $\bar\eta$ value is
$(\pi/|\pi|)^4$. Both $\eta$ and $\bar\eta$ are trivial on all finite
unit groups, including the place over $2$. Thus the sum over ideals
is exactly the finite Euler product for $\bar\eta$. The Archimedean
angular index is $n=-4$, giving the displayed Gamma factor. In
particular the coefficient for the profile integral, not quotient
Haar, is **four**. The quotient Mellin coefficient is $4C$; it would
be incorrect to equate the raw finite Tamagawa integrals with the
unit-mass Euler factors. The lattice calculation bypasses their
normalization. Conjugating the Gaussian ideals happens to give
$L(\lambda,\eta)=L(\lambda,\bar\eta)$ here; the label is fixed by the
pointwise cancellation, not by a numerical comparison of the two
functions. As a separate normalization check, the reviewer used
(A.3.2.5), p. 560, on the raw idelic route: The complex density
contributes $2\pi$ times the Gamma factor, and the product of finite
unit masses is $1/2$ from the place over $2$. This gives $\pi L$ for
that Haar convention, consistent with $4L$ for the $dx$ profile.

For absolute convergence and continuation directly on the quotient,
Schwartz decay gives $P(x)=O_N(e^{-Nx})$ as $x\to+\infty$ for every
$N$: Sum an inverse lattice power of degree $>\max(2,2N)$.
On the other end, Euclidean Poisson summation on the covolume-one
self-dual lattice $\mathbb Z^2$ gives

$$
P(x)=e^{-x}\sum_{0\ne\alpha\in\mathbb Z[i]}
                 \widehat b_{\mathrm{Euc}}(e^{-x/2}\alpha),
$$

since $b(0)=\widehat b_{\mathrm{Euc}}(0)=0$. Schwartz decay of the
Euclidean transform gives $O_N(e^{-N|x|})$ there as well, using a
lattice power of degree $>\max(2,2N+2)$. The estimates are uniform
on each tail, and local uniform absolute convergence gives
continuity. All compact sets of $\lambda$ admit a single integrable
majorant, also with any fixed powers of $|x|$ for differentiation.
Thus $\int P(x)e^{\lambda x}dx$ is entire. Its above-one value gives
$4L(\lambda,\bar\eta)$ by uniqueness of continuation. The absolutely
convergent Euler product is nonzero in that half-plane, so the
continued function is not identically zero. On the critical line,

$$
\mathcal F_+ q(t)=4L(1/2+it,\bar\eta).
$$

This does not use the adelic Fourier phase away from zero. It also
proves that $q$ belongs to the defining weighted space and indeed is
one of its generating twisted theta profiles. The accepted Lean
[Gaussian calibration above one](../../Proofs/Theorems/DiscriminantNormalizedIdeleHeckeGaussian.lean)
checks absolute integrability and the discriminant-scaled completed
Euler value on the upstairs idele group, under unitary character and
real-part hypotheses. It does not give quotient continuation or the
weighted closure inclusion proved here.

## Averaging in the defining weighted norm

Let $V_r q(x)=q(x-r)$, the profile action of $\sigma(r)$. The
translates remain generating profiles, since for any idele lift $k$
with class $\sigma(r)$, a generating adelic lift for $V_rq$ is
$e^{-r/2} f(k^{-1}\,\cdot)$. Dilation preserves both zero modes
(by evaluation and additive change of variables), and the group is
abelian, so it preserves the indicated isotype. The profile norm
has weight $w(x)=(1+x^2)^2$ and an overall positive Haar constant.
The inequality $1+(x+r)^2\le 2(1+x^2)(1+r^2)$ gives

$$
\|V_r q\|_w\le 2(1+r^2)\|q\|_w.
$$

The translates are strongly continuous: For this $q$, continuity
and the two-sided exponential bounds give weighted dominated
convergence for $r$ in bounded sets. For $v\in C_c^\infty$, or more
generally $v\in\mathcal S(\mathbb R)$, put
$\kappa(r)=(2\pi)^{-1}\int v(t)e^{-itr}dt$. It is Schwartz, so
$\int|\kappa(r)|(1+r^2)dr<\infty$. Therefore

$$
q_v=\frac14\int_{\mathbb R}\kappa(r)V_rq\,dr
$$

is a norm-convergent Bochner integral and lies in the closed isotype
part of $M_{1/2}$: On each bounded interval it is a limit of finite
linear combinations of translates, and the norm tails go to zero.
Both $\kappa$ and $q$ are in $L^1$, so Fubini in the ordinary
convolution gives $\mathcal F_+q_v=vL(1/2+it,\bar\eta)$, with the
shift factor $e^{itr}$. This convolution agrees with the weighted
norm integral, e.g. by the continuous embedding into $L^1$ for
$w=(1+x^2)^2$. For other singleton weights $w=(1+x^2)^{s/2}$ with
$s\ge0$, the bound becomes $2^{s/4}(1+r^2)^{s/4}$; agreement of the
integrals follows by local $L^1$ convergence and the separate global
$L^1$ convolution bound, even when the weighted space does not
embed into $L^1$. The same tail estimates work after any real twist.

## What this settles, and what it does not

On the selected line write $Z(t)=L(1/2+it,\bar\eta)$. On each open
interval $J$ complementary to the real zeros of $Z$, division of
any $C_c^\infty(J)$ test by $Z$ on its support gives a compact smooth
frequency multiplier. Thus the transformed theta closure contains
those off-zero tests. By Plancherel the weighted profile space at
$s=4$ has the $H^2$ norm with squared derivative coefficients
$(1,2,1)$, up to a constant. If $P$ is the orthogonal projection
onto the theta complement, its projected range on each $J$ solves
$(1-\partial_t^2)^2u=0$, by testing orthogonality against these tests.
It has local dimension at most four. This is the local finite-rank
input in the [rational singleton argument](trace-spectral-q.md#translation-and-local-finite-rank),
now proved in this Gaussian isotype, without using a global
totality theorem or the printed singleton kernel.

**Review evidence.** Independent read-only reviewer `theta-qi-review`
(agent `SaPwmgM`, Yah transcript `01a2027a-64c6-7ade-b2e1-38ad1ed74b39`)
read the decisive rendered p. 81, 91, 93, 123, 124, 127, 434, 439,
and 560 passages in the same pinned PDF. The reviewer independently
checked the zero modes, conjugation, Gamma factor, both the $dx$ and
raw Haar unfoldings, the Euclidean Poisson tail, and the weighted
Bochner average in the selected case. The norm, character restriction,
and compact-class conventions are applied from the accepted notes
above, not freshly rendered here. No consequential reading for the
selected inclusion remains provisional. The extension to other
singleton indices and the local rank consequence are derived here,
not additional source claims. Selector Yah:
`01a20278-8e87-7d9d-9cb0-b17805f543a0`.

**Next bounded check:** Obtain a polynomial zero-count bound for
$Z$ from the growth of this completed lattice Mellin integral on
expanding disks, starting at a nonzero real point above one. This
would test summability of the finite-rank rows of $AP$ against the
Schwartz convolution multiplier. For the [actual operator](trace-spectral-angular-qi.md)
in (10.4.2.5), p. 459, the order is $PA=P(AP)$ since convolution
preserves the theta space; no commutation is needed. No trace
class is asserted here. Jet annihilation for arbitrary Gaussian
lifts, evaluation or nonvanishing of the scalar trace, convergence
of any proposed kernel series, and the local-to-global diagonal
comparison are separate. The [singleton kernel warning](trace-spectral-singleton-kernel-qi.md)
is unchanged.

**Deferred comparison:** The inert-prime fiber for
$\mathbb Q(\sqrt{-5})$ would close one arithmetic Euler-factor case.
This check took precedence because it supplies the missing Gaussian
operator premise directly.
