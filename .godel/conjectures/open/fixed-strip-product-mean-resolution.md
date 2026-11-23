---
evidence_revision: bbca37033019090f6f40e6223b5054d382c9d789
---

# Resolution of the absolute product means for a fixed character

**Proposed transfer to test:** Fix $1/2<\beta_0<1$
(the landing uses $7/8$). Keep the actual primes and
characters, but permit a common weight $1/2\le w(p)\le3/2$,
with $w(2)=1$ and coefficient $w(p)\log p$ at every $p^k$.
Require the endpoint and multiplier mass asymptotics
$1+o(1)$ and $(2+o(1))\sqrt Y$, respectively, in Bob's
normalizations. For every $\beta_0<\sigma<1$ require

$$
\left|\frac{1}{U}\sum_{p<U} w(p)\log p\,\psi(p)
 p^{iv}\log(U/p)\right|
\ll_{\beta_0,\sigma} U^{\sigma-1}\log(2m(2+|v|))
 + U^{-1/2}\log^3(2U),
$$

uniformly for $U\ge3$, real $v$, and the distinct quadratic
twist products $\psi$ modulo $m$ in the source. In particular
include $(d_i,d_j)=(1,-4)$ at unbounded odd base conductors.
Do these hypotheses force the sharp sum
$D_w(x)=\sum_{p^k\le x}w(p)\log p\,\chi_4(p)^k$ to be
$O_\epsilon(x^{1/2+\epsilon})$ for every $\epsilon>0$?
Test the alternative that the optimal power, with arbitrary
positive exponent slack, is instead $\beta_0$.

**Source and payoff:** [Bob's product mean and its
consumers](../../bob/fixed-strip-endpoints.md#the-product-mean-at-the-original-endpoint-weight)
use a fixed zero-free strip to bound pair means at the sum
and difference heights. They count twist exceptions, not
the signed sum of one fixed character. The transfer would
turn these arithmetic inputs into a sharper individual
estimate without using Masullo's operator trace. This is a
test of numerical inequalities, not a replacement for the
actual von Mangoldt coefficients or functional equation.

**Discriminating test:** Starting from the unweighted
estimates, test both $w_\pm(p)=1\pm\frac12\chi_4(p)
p^{\beta_0-1}$, uniformly in the cutoff, modulus, and
modulation. Check both probability normalizations and the
sharp multiplier input. Subtract the two sharp $\chi_4$
sums, handling even and odd powers separately. In the other
direction, use Fourier inversion in $\log p$ to undo the
log weight with a smooth cutoff between consecutive integers;
check the required height band and the higher-power error.
