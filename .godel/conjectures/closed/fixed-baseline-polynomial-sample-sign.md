---
evidence_revision: 1344a39f1fb2c622fafd8f9c813da961976ecdc5
outcome: established
---

# Test one-sided signs on polynomial samples

**Proposition to test:** Retain the absolute $C,D\ge1$ of
`1344a39f1fb2c622fafd8f9c813da961976ecdc5`. For every
integer $q\ge2$ and every fixed positive integer $B$, put
$m=\max(8,\lceil C\log(2q)\rceil)$, $M=10^{15}$,
$a=\log 2$, $h_m=\mathbf1_{[0,a]}^{*m}$, and
$k_m=4h_m^{(4)}-5h_m''+h_m$. With natural logarithms let
$$W_{q,m}(X)=\sum_{p\nmid q}(\log p)
[Mh_m(\log(p/X))
 +\mathbf1_{p\equiv1\bmod q}k_m(\log(p/X))].$$
Joint GRH for the primitive inducers modulo $q$, including
zeta, is equivalent to $W_{q,m}(n^B)\le M n^B$ for every
positive integer $n$ with $n^B\ge(2q)^D$. In the reverse
direction, an arbitrary eventual tail of these signs should
suffice. No uniformity of converse estimates in $B$, signs
between samples, or comparisons of samples are premises.

**Source and payoff:** The polynomial-onset landing proves
strict increase on a full real interval under joint GRH.
The pinned fixed-baseline landing
`f5fbeb09e9b972565848e25ac295f3341a537afd` gives the
unconditional mean and the exact prime-deficit transform.
This operator proposal replaces the continuous witness by
one sparse sequence of one-sided bounds, not by a finite
test or by monotonicity of the sampled values.

**Discriminating test:** Anchor at the last sample and
use the exact polynomial cell length to interpolate a power
lower envelope for $H=MX-W_{q,m}$. Add that envelope and
test whether Landau forces a better zero bound on the open
half-plane beyond the envelope exponent and $1/2$. Check
all pole signs, visibility, and the endpoint at one. From
the resulting open zero-free region alone, shift the
prime-power derivative contour to its right. Check the
multiplier $sK_f(s)$ at order eight, the principal residue,
character averaging, and the prime-power subtraction.
Spend the gap exponent again and verify finite termination
at $1/2$ for every fixed $B$, including boundary zeros.
Verify the forward signs using the unchanged onset and mean.

## Adjudication

**The sampled signs suffice for every fixed integer $B\ge1$.** In
`1344a39f1fb2c622fafd8f9c813da961976ecdc5`, the polynomial-onset
card, lines 148–169, gives strict increase of $W_{q,m}/X$ under
joint GRH on the stated interval. Its limit is $M$ by lines 80–85
of the variable-order card at `f5fbeb09e9b972565848e25ac295f3341a537afd`.
Thus it is strictly below $M$ even at the left endpoint. Restriction
to samples proves the forward direction with no change of constants.
Lines 170–172 of the onset card use full-interval nondecrease in the
reverse direction and do not apply to the sampled premise.

### What a lower bound between samples implies

Fix $q,m,B$ and abbreviate $W=W_{q,m}$, $H=MX-W$. Suppose on
$X\ge A\ge1$ we have $H(X)\ge-KX^b$, with $K\ge0$ and $b<1$.
Put $c=\max(b,1/2)$. The Mellin integral of $H+KX^b$ on this tail
is the pinned transform (variable-order card, lines 144–183) plus
$KA^{b-s}/(s-b)$. The addition has no pole in $\Re s>c$.

Indeed $K_f(s)=\int f(v)e^{sv}dv$ is $\Phi^m$ for $h_m$ and
$Q\Phi^m$ for $k_m$, where $\Phi=(2^s-1)/s$ and
$Q=(4s^2-1)(s^2-1)$. Substitution $v=\log(p/X)$ and character
orthogonality give the transform of $H$ as
$$\frac{MA^{1-s}}{s-1}+\int_0^A W(X)X^{-s-1}dX+
\Phi(s)^m\sum_{\chi\bmod q}\left(M\mathbf1_{\chi=\chi_0}+Q(s)/d\right)
\big((L'/L)(s,\chi)+R_\chi(s)\big),$$
with $d=\varphi(q)$ and $R_\chi$ the $j\ge2$ terms of $-L'/L$.
The integral is entire by support away from zero. The $R_\chi$
converge normally to the right of $1/2$ by comparison on
$\Re s\ge v>1/2$ with $\sum_p(\log p)p^{-2v}/(1-2^{-v})$.
Removed Euler factors have no zeros there. At one the principal
residue is $-M$, canceling $+M$ since $\Phi(1)=1$, $Q(1)=0$;
there are no zeros on $\Re s=1$ by classical nonvanishing.

Each family zero $\rho$ in $1/2<\Re\rho<1$ gives residue
$\Phi(\rho)^m(Mm_\zeta(\rho)+Q(\rho)S/d)$, with $S>0$ the
sum of multiplicities over characters. The prefactor is nonzero.
For real $\rho$ the paired eta series excludes a zeta zero, and the
residue is strictly negative. For nonreal $s=x+it$ only a shared
zeta zero could cancel, since $Q$ has only real roots. Then
$\Im Q=2xt(8(x^2-t^2)-5)$ would vanish. On that locus
$|s-1|^2=2x(x-1)+3/8\le3/8$ and $|s|/x<\sqrt2$. Euler summation
with the periodic first Bernoulli function bounded by $1/2$ gives
$|\zeta(s)-1/(s-1)-1/2|\le |s|/(2x)$. Hence
$|(s-1)\zeta(s)-1|\le\sqrt{3/8}(1+\sqrt2)/2<1$, excluding the
shared zero without any zero-line assumption.

The nonnegative integral has abscissa of convergence $\alpha\le1$
by Chebyshev's bound and bounded windows of fixed support. If
$\alpha>c$, meromorphic continuation at real $\alpha$ is regular
or has a simple pole of negative residue. The latter contradicts
nonnegativity on approach from the right. In the regular case take
$r>\alpha$ so close that the Taylor disk at $r$ reaches a real
$v<\alpha$. The coefficients in $r-s$ are the nonnegative log
moments divided by factorials ($A\ge1$). Monotone convergence at
$v$ gives convergence there, a contradiction. Thus the integral
is holomorphic on $\Re s>c$, where it agrees with the continuation.
Visibility now bounds every family zero by $\Re\rho\le c$. This
argument cannot exclude a pole on the boundary, nor need it.

### From a zero bound back to a derivative bound

The truncated-power formula for $h_m$ uses translates of
$v_+^{m-1}$, so $h_m\in C^{m-2}$ and $k_m\in C^{m-6}$ globally.
Both windows and their derivatives are bounded with support in
$[0,m\log 2]$. In the locally finite sum, $X\,d/dX$ replaces $f$
by $-f'$ even at knots. Chebyshev's $\theta(2^mX)\ll 2^m X$ first
gives $H'=O_{q,m}(1)$ with no zero bound.

Now suppose $\Re\rho\le\sigma<1$ for all nontrivial family zeros.
Choose $\max(1/2,\sigma)<u<1$. Integrating by parts gives
$K_{-f'}=sK_f$, not $(s-1)K_f$. On $u\le\Re s\le2$ the worst
multiplier is $O_m((1+|\Im s|)^{5-m})$, integrable even at $m=8$.
Invert $sK_f(s)X^s(-L'/L)(s,\chi)$ on $\Re s=2$ for the full
$\Lambda(n)\chi(n)$ sum with window $-f'$. This uses the absolutely convergent
Dirichlet series on that line and Fourier inversion for the window.

Here is the log-derivative estimate needed to shift to $u$.
For the order-one primitive completion $\Xi$ (pole factors removed
by $s(s-1)$ for zeta), $\Xi'/\Xi(2+it)=O_q(\log(2+|t|))$ by the
Euler series and Stirling; the functional equation gives this bound
at $-1+it$ too. In the Hadamard difference at those two points the
constants cancel. Writing $y=t-\Im\rho$, $\beta=\Re\rho$, each
zero contributes real part
$$\frac{2-\beta}{(2-\beta)^2+y^2}+\frac{1+\beta}{(1+\beta)^2+y^2}
\asymp (1+y^2)^{-1}.$$
Only $0\le\beta\le1$ is needed. Hence the sum of these weights is
$O_q(\log(2+|t|))$, counting multiplicities. In the difference at
$x+it$ and $2+it$ for $u\le x\le2$, each reciprocal difference is
$O_{u,\sigma}((1+y^2)^{-1})$ since $x-\beta\ge u-\sigma>0$.
Removing the completion terms preserves the logarithmic estimate on
the vertical at $u$ and on the horizontals for $|t|\ge1$. Removed
Euler factors cost at most $\sum_{p\mid q}(\log p)/(p^u-1)$.
This uses the current bound only, not joint GRH or separation from
zero ordinates at the old boundary.

Cubic decay kills the horizontal edges; the vertical at $u$ costs
$O_{q,m,u,\sigma}(X^u)$. Only the principal pole at one is crossed,
contributing $XK_f(1)$. To recover primes, discard powers $p^j$
with $j\ge2$: Their bases satisfy $p\le(2^mX)^{1/2}$, and both
$j$ and $\log p$ are $O_m(\log(2X))$ for $X\ge1$. The resulting
$O_m(\sqrt X\log^2(2X))$ error is $O_{m,u}(X^u)$. The baseline
uses the principal character and the class uses the average of all
$d$ characters, so both omit nonunits. The residue in $XW'$ is
$X(MK_{h_m}(1)+K_{k_m}(1)/d)=MX$. Subtraction and division by $X$
give $H'(X)=O_{q,m,u,\sigma}(X^{u-1})$.

### Close the iteration

Write $\delta=1/B$. In any sufficiently late cell
$n^B\le X<(n+1)^B$, the preceding sample has $H(n^B)\ge0$.
The binomial formula gives $X-n^B\le(2^B-1)X^{1-\delta}$ and
$n^B\ge2^{-B}X$. Integrating the unconditional derivative bound
from this sample gives $H(X)\ge-KX^{1-\delta}$. The first barrier
therefore gives $\sigma_0=\max(1/2,1-\delta)$, with no assumption
that a rightmost zero exists. This finishes $B=1,2$.

For $B\ge3$, while $\sigma>1/2$, use $u=\sigma+\delta/2<1$
(since $\sigma\le1-\delta$). Throughout the cell the integration
variable is comparable to $X$, so the derivative bound times the
cell length gives $H(X)\ge-K'X^{u-\delta}$. The barrier updates
$\sigma$ to $\max(1/2,\sigma-\delta/2)$. In units of $1/(2B)$
the initial bound is $2B-2$, the target is $B$, and each round
subtracts one. Exactly $B-2$ rounds suffice, the last with
$u=1/2+\delta$ and envelope exponent $1/2$. No contour is taken
at $1/2$. Functional-equation reflection within the family gives
joint GRH. Each $B$ is fixed throughout its proof; neither the error
constants nor the start of the sample tail need be uniform. No
intermediate sign, sample comparison, or finite certification of
joint GRH has been used.
