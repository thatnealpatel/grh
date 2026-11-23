---
evidence_revision: bbca37033019090f6f40e6223b5054d382c9d789
outcome: refuted
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

**Decision.** The square-root transfer is false for these
numerical hypotheses. The optimal exponent up to positive
slack is $b=\beta_0$, given the source's unweighted estimate
at that strip. This does not refute Bob's bounded list.

**Witness at every cutoff.** For $w_\pm$ above, the value at
2 is one, and the bounds on the weights hold pointwise. By
partial summation of $\vartheta(t)=\sum_{p\le t}\log p\sim t$,

$$ H_b(t)=\sum_{p\le t}p^{b-1}\log p\sim t^b/b. $$

Since $|\psi(p)p^{iv}|\le1$, the absolute change of the
unnormalized log-weighted mean is bounded by
$\frac12\int_1^U H_b(t)\,dt/t\ll_b U^b$. After dividing by
$U$ this fits (1) for every $\sigma>b$, with no dependence
on $m$, $v$, or the choice of cutoff. The same bound on the
absolute mass change gives endpoint mass $1+o(1)$. For the
multiplier the absolute change before normalization is at
most $\frac12\int_{1^-}^Y t^{-1/2}\,dH_b(t)\ll_b Y^{b-1/2}$,
since $b>1/2$. Thus $S_w\sim2\sqrt Y$. After normalization
the two prime probability measures (endpoint and multiplier)
each differ from their unperturbed counterpart in total
variation by $O_b(X^{b-1})$ for $Y\sim X$. All bounded
pair tests change by $o(1)$ on either height band, including
at the individual endpoint cutoffs. Bounded $w$ preserves the
absolute higher-power error estimates. No reweighted Weil
identity or logarithmic derivative is assumed.

**Sharp separation.** At $p^k$ the signed difference is
$p^{b-1}\log p\,\chi_4(p)^{k+1}$. At odd primes it has
positive sign for odd $k$, and sign $\chi_4(p)$ for even
$k$; at 2 it vanishes. The first powers give $H_b(x)-O(1)$,
and the absolute contribution of all higher powers is at
most $\sum_{2\le k\le\log_2 x}H_b(x^{1/k})
\ll_b x^{b/2}\log x$. Hence the difference is
$(1/b+o(1))x^b$. At least one fixed sign gives magnitude
$\gg_b x^b$ along an unbounded sequence. In contrast, the
perturbation of the *unsigned* odd prime-power mass is
$O_b(x^b+x^{b/2}\log x)=o(x)$ for each sign. The two systems
satisfy the same inequalities, not identical observations.

**Matching sharp upper bound.** For sufficiently large odd
base conductors the distinct admissible twists $1,-4$ give
$\psi=\chi_4$, $m=4$. Use (1) for this pair. With
$N=\lfloor x\rfloor$, $U=2(N+1)$, let $r(t)$ be one on
$[0,\log N]$, zero outside $[-1,\log(N+1)]$, and interpolate
on each intervening interval by the rescaled cubic smoothstep
$3z^2-2z^3$ (reversed on the right). Set $g=r/(\log U-t)$
on the support and zero elsewhere. At every $p<U$,
$g(\log p)\log(U/p)=\mathbf 1_{p\le x}$. In particular there
is no half-weight at a prime cutoff. The denominator is at
least $\log 2$; its reciprocal has bounded first and second
derivative integrals there. The ramps have total variation
two and second-derivative integral $O(N)$ in absolute value,
since the short ramp has width $\log(1+1/N)$. Thus
$\|g\|_1\ll\log U$, $\|g'\|_1\ll1$, and $\|g''\|_1\ll N$.

Fourier inversion expresses the sharp prime sum as
$(2\pi)^{-1}\int\widehat g(v) M_w(U,v;\chi_4)\,dv$, with
$e^{-ivt}$ in the transform and $M_w$ unnormalized.
Integration by parts bounds $|\widehat g(v)|$ by a constant
times $\min(\log U,1/|v|,N/v^2)$. Its integral up to
$|v|\le N^2$ is $O(\log U)$; beyond that the trivial
$|M_w|\ll U$ costs only $O(1)$ in the inversion. Hence (1)
gives $O_{b,\sigma}(x^\sigma\log^2 x+\sqrt x\log^4 x)$.
Only polynomial heights need (1), inside either source band
at comparable cutoff. The higher powers cost $O(\sqrt x\log x)$
by Chebyshev and boundedness of $w$. Choosing $\sigma$ just
above $b$ gives $D_w(x)=O_{b,\epsilon}(x^{b+\epsilon})$.

**Consequence for the proposed use.** The comparison controls
large relative peaks, not a bias of this size in one fixed
character. Both witnesses work simultaneously at all cutoffs,
so chaining the same inequalities cannot improve the power.
A sufficient replacement input is an unnormalized
$O_\delta(U^{1/2+\delta})$ product mean for the *actual*
$(1,-4)$ pair through $|v|\le U^2$, for every $\delta>0$.
The inversion above would then give square-root cancellation
up to exponent slack for this character alone. The two
weights do not test what additional exact arithmetic can do.
