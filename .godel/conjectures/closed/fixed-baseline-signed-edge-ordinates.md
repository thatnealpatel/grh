---
evidence_revision: 8e0f45864088cc246d66567c2b83ccb84f553fd0
outcome: established
---

# Extract rightmost zero ordinates from signed samples

**Proposition to test:** Fix integers $q\ge2$, $m\ge8$,
and $B\ge1$. Write $M=10^{15}$, $a=\log 2$,
$h_m=\mathbf1_{[0,a]}^{*m}$, $k_m=4h_m^{(4)}-5h_m''+h_m$,
and $t_p=\log(p/X)$. Use the same signed deficit
$$H(X)=MX-\sum_{p\nmid q}(\log p)
  [Mh_m(t_p)+\mathbf1_{p\equiv1\bmod q}k_m(t_p)].$$
Let $\theta=\Theta_q$ be the supremum of the real parts
of the nontrivial zeros of the primitive inducers of
characters modulo $q$, including zeta. For each real $t$
put $z=\theta+it$, $d=\varphi(q)$, and
$S(z)=\sum_{\chi\bmod q}\operatorname{mult}_{\chi^*}(z)$,
with multiplicity zero at nonzeros, including the zeta
pole at one. Write $\Phi(s)=\int_0^a e^{sv}dv$ and
$Q(s)=(4s^2-1)(s^2-1)$. The claimed ordinary limit is
$$\lim_{N\to\infty}\frac1{\log N}
  \sum_{n\le N}H(n^B)n^{-Bz}/n
 =\Phi(z)^m[M\operatorname{mult}_\zeta(z)+Q(z)S(z)/d]
  +\mathbf1_{\theta=1/2,\ t=0}(M/2)\Phi(1/2)^m.$$
At every nonreal edge point the coefficient should
separately determine the zeta multiplicity and $S$.
The same visibility is sought at real edge zeros when
$\theta>1/2$. The center at $\theta=1/2$ is blind to
central nonprincipal multiplicities. No attainment or
zero-spacing hypothesis is imposed.

**Source and payoff:** The evidence landing recovers
$\theta$ from positive sampled excess. The window and
deficit residues are from the fixed-baseline criterion
at `f5fbeb09e9b972565848e25ac295f3341a537afd`.
This is a new use of signed samples, not an inference
of ordinates from the positive excess alone. It seeks
aggregate, not individual, nonprincipal multiplicities.
It does not seek deeper zeros or a finite algorithm.

**Discriminating test:** At the worst order $m=8$,
reconstruct the full primitive zero expansion by a
shift to $\Re s=-1/2$. Check residue signs, horizontal
and vertical bounds, and absolute coefficient mass.
Restore the imprimitive exclusions and remove squares
using fixed-class PNT on exactly $b^2=1$ for the
identity term, checking both square constants. Test
whether dominated convergence removes all left zeros,
even with no gap, and whether harmonic sums of the
logarithmic phases isolate exactly $t$ for every fixed
$B$. Check extraction on the entire nonreal locus
$\Im Q=0$ by unconditional zeta nonvanishing there.

## Adjudication

**The ordinary limit holds.** The positive-excess landing supplies
$\theta$, not a Fourier coefficient. The residue computation at the
window pin only treats the open half-strip. To extract the coefficient
on the edge, including on the critical line, we first expand the
signed deficit itself.

### Full sums and the square term

For $f=h_m,k_m$, let $K_f(s)=\int f(v)e^{sv}\,dv$. Convolution and
integration by parts give $K_h=\Phi^m$ and $K_k=Q\Phi^m$. On
$-1/2\le\Re s\le2$ both are $O_m((1+|\Im s|)^{4-m})$ since
$\Phi=(2^s-1)/s$ with a removable value at zero. Complete the prime
sums to powers using $\log p$ at each $p^j$. For the baseline use the
principal character; for the perturbation average over all $d$
characters, since the average of $\chi(p^j)$ selects exactly
$p^j\equiv1\pmod q$. Passing to primitive inducers changes the sums
by $O_{q,m}(1)$: For each $p\mid q$ the log window contains at most
$1+m\log 2/\log p$ exponents, and the windows are bounded.

For each primitive sum the inverse integral on $\Re s=2$ has integrand
$X^s K_f(s)(-L'/L)(s,\chi^*)$, with measure $ds/(2\pi i)$. Indeed
Fourier inversion gives $f(\log(n/X))$ and the Dirichlet series is
absolute there. Shift to $\Re s=-1/2$. Here are the estimates without a
line hypothesis. For each primitive completed entire function (use
$\xi$ for zeta), the real part of its Hadamard log derivative at
$2+iT$ gives
$$\sum_\rho (1+(T-\Im\rho)^2)^{-1}\ll_q\log(2+|T|).$$
Indeed $\Re(2+iT-\rho)^{-1}$ dominates a constant times each weight;
the real parts of the product corrections $1/\rho$ sum absolutely
by order one and bounded real parts. The Euler series and Stirling
bound the completed derivative there. This counts multiplicities in
each unit interval. Choose upper and lower heights tending to infinity
in modulus in unit intervals, avoiding all nearby ordinates of this
finite family by $\gg_q1/\log(2+|T|)$. In the derivative difference
from $2+iT$ at these heights, zeros at distance greater than one in
ordinate contribute $O_q(\log(2+|T|))$ by the displayed bound;
the nearby ones cost $O_q(\log^2(2+|T|))$. Removing the completion
preserves the latter estimate across the horizontals. On the left
vertical the functional equation, Stirling, and the Euler series at
$\Re(1-s)=3/2$ give $L'/L=O_q(\log(2+|\Im s|))$; there is no gamma
pole there. Even at $m=8$ the horizontals vanish for fixed $X$ and
the left integral is $O_{q,m}(X^{-1/2})$ for $X\ge1$.

The full weighted sum thus has pole contribution $MX$ since
$\Phi(1)=1$ and $Q(1)=0$. Its nontrivial zeros contribute
$-\sum_\rho c(\rho)X^\rho$, grouped by distinct points, where
$$c(s)=\Phi(s)^m[M\operatorname{mult}_\zeta(s)+Q(s)S(s)/d].$$
The only trivial zero possibly crossed is at zero and costs $O_{q,m}(1)$.
The unit counts and at least quartic decay give $\sum_\rho|c(\rho)|<\infty$.

In $H$ we subtract the full sum and **add** the omitted powers. With
$T=\sqrt X$, partial summation by the fixed-class PNT gives each
reduced class's square sum for $f$ as
$$\frac{T}{d}\int_1^{2^{m/2}} f(2\log v)\,dv+o(T)
=\frac{T}{2d}K_f(1/2)+o(T).$$
The test function has bounded variation on this fixed interval. All $d$
classes enter for $Mh_m$, but only $b^2=1\pmod q$ for $k_m$. The latter
signed main term vanishes because $Q(1/2)=0$. As a direct order-eight
check, integrate $e^{v/2}P(v)$ on each knot interval using the primitive
$e^{v/2}\sum_{i=0}^7(-1)^i2^{i+1}P^{(i)}(v)$. For $P$ the pieces of
$h_8=\sum_{j=0}^8(-1)^j\binom8j(v-ja)_+^7/7!$, the endpoints sum to
$147712-104448\sqrt2=[2(\sqrt2-1)]^8$; for the pieces of $k_8$ they
sum to zero. For $j\ge3$ one has $p\le(2^mX)^{1/3}$ and
$j\ll_m\log(2X)$, so these powers cost $O_{q,m}(X^{1/3}\log^2(2X))$.
Consequently, with $C=(M/2)\Phi(1/2)^m$,
$$H(X)=\sum_\rho c(\rho)X^\rho+C\sqrt X+o_{q,m}(\sqrt X).$$

### Isolating and decoding the coefficient

Since $1/2\le\theta\le1$, division by $X^\theta$ makes the error $o(1)$.
Every strictly left term tends to zero, dominated in modulus by
$|c(\rho)|$ for $X\ge1$. Thus even without a gap their entire sum
tends to zero. On $X=n^B$, twist by $n^{-iBt}$. An edge term then has
frequency $u=B(\Im\rho-t)$ in $\log n$. For fixed real $u$,
$\sum_{n\le N}n^{-1+iu}=\int_1^N v^{-1+iu}dv+O(1+|u|)$ by integrating
the absolute derivative on unit intervals. The integral is $\log N$
at zero and bounded by $2/|u|$ otherwise. After division by $\log N$
the sums are bounded by $(1+\log N)/\log N$ independently of $u$.
Hence their limits pass through the absolutely summable edge series,
and the harmonic mean of the twisted $o(1)$ also tends to zero. Only
$\Im\rho=t$ survives, with the constant $C$ surviving precisely at
$\theta=1/2$, $t=0$. This proves the displayed ordinary limit, even
for an empty edge and without any spacing condition.

For nonreal $z$, divide the limit by $\Phi(z)^m\ne0$ (since
$|2^z|>1$), obtaining $D$. If $\Im Q(z)\ne0$, then
$$S=d\,\Im D/\Im Q(z),\qquad
\operatorname{mult}_\zeta(z)=(D-Q(z)S/d)/M.$$
Otherwise $\Im Q(x+it)=2xt[8(x^2-t^2)-5]$ forces $t^2=x^2-5/8$,
$x=\theta$. There $|z-1|^2=2x(x-1)+3/8\le3/8$ and $|z|/x<\sqrt2$.
Euler summation gives $\zeta(z)=1/(z-1)+1/2+E$, with
$|E|\le |z|/(2x)$ by the bound $1/2$ on the periodic first Bernoulli
function. Thus $|(z-1)\zeta(z)-1|\le\sqrt{3/8}(1+\sqrt2)/2<1$.
The zeta multiplicity is zero and $S=dD/Q(z)$ since $Q$ has only real
roots. This distinguishes every nonreal edge zero from a nonzero point.
For real $1/2<\theta<1$ the paired eta series likewise excludes zeta
zeros, and $Q(\theta)\ne0$ determines $S$ by the same quotient. The
line at one contains no zeros by classical Dirichlet nonvanishing.
At the exact center zeta is nonzero by eta, but $Q(1/2)=0$: The limit
is only $C$, irrespective of the central nonprincipal multiplicities.
