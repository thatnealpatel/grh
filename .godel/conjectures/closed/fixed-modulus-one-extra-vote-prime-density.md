---
evidence_revision: a08d9dfe9adc87383319f9e970b60bd443cfcca2
outcome: established
---

# One extra vote per reduced class and fixed-modulus GRH

Fix any integer $q\ge2$ and let $G=(\mathbb Z/q\mathbb Z)^*$.
For a fixed integer $m\ge4$ put
$h_m=\mathbf 1_{[0,\log 2]}^{*m}$, using ordinary real
convolution. For real $X>0$ write

$$P_a(X)=\sum_{p\equiv a\bmod q}\log(p)h_m(\log(p/X)),
\qquad P(X)=\sum_{a\in G}P_a(X).$$

**Proposition to test:** All nontrivial zeros of every
primitive Dirichlet $L$-function inducing a character
modulo $q$, including $\zeta$, lie on $\Re s=1/2$ if and
only if there exist integers $m\ge4$, $M\ge1$, and a
real $A\ge1$ such that $(MP+P_a)/X$ is nondecreasing on
$[A,\infty)$ for every $a\in G$. The same $m,M,A$ are
used for all classes and may depend on $q$, not on $X$.
Test also whether one can always take $m=4$ in the forward
implication.

**Source and payoff:** This operator proposal uses the
[quartic prime-only criterion](../closed/zeta-prime-only-continuous-density.md)
at the evidence revision. For comparison, the
[critical dilation criterion](../closed/critical-dilation-prime-square-allowance.md)
at `a954fef4e3a0db9c2124fbeb457b881886b18b47` uses a
signed single-character count and a prime-square allowance.
Neither landing asserts the simultaneous comparison. The
payoff would be a joint criterion using only genuine
rational primes with coefficients $M$ and $M+1$, without
a square allowance, chosen phase, or real-axis premise.

**Discriminating test:** Center each density using its
fixed-class PNT limit. Sum the nonnegative deficits and
check whether this forces ordinary RH for the *witness*
order $m$, not just order four. With zeta RH alone,
derive a square-root bound for the total deficit and
check whether conservation gives a two-sided bound in
every class. Invert with each full character and audit
the Mellin endpoints, prime powers, inducing Euler
factors, and visibility of a real zero above the line.
For the other direction, insert $g=-h_4'-h_4$ directly
in the smoothed explicit formula. Test whether the
class terms, including central zeros and squares, have
a finite uniform-in-$X$ derivative bound in the scale
of the pinned positive margin, so that one integer
baseline works at all real arguments on a common tail.

## Adjudication

**The two conditions are equivalent, and order four suffices.** The
converse must keep the order supplied by the comparisons until ordinary
RH has been recovered. It is the *total* prime deficit, not a deficit
for an individual progression, to which the zeta sign argument applies.

Write $d=|G|$, $P_*$ for the sum at the current order over all primes,
and $\Phi(s)=\int_0^{\log 2}e^{st}dt=(2^s-1)/s$, by continuity at zero.
The transform of $h_m$ is $\Phi^m$; in particular $\Phi(1)=1$, and
$\Phi$ has no zeros in $\Re s>1/2$. All windows have $X\le p\le 2^mX$,
so $P=P_*$ identically once $X$ exceeds every prime divisor of $q$.

### What the simultaneous comparisons force

Fix witnesses $m,M,A$. The fixed-modulus PNT gives
$\vartheta_a(Xv)=Xv/d+o(X)$ uniformly for $1\le v\le 2^m$.
Integration against the fixed bounded-variation weight $h_m(\log v)$
by partial summation gives $P_a/X\to\Phi(1)^m/d=1/d$. Each nondecreasing
density is bounded above by its limit $M+1/d$. With $H=X-P$ and
$D_a=X/d-P_a$ this says
$$H_a=MH+D_a\ge0,\qquad \sum_a H_a=(dM+1)H.$$
In particular $H\ge0$. Choose $B\ge A$ beyond all the excluded primes.

Here is the sign implication at this very $m$. For $\Re s>1$, the
Mellin integral of one window over $(0,\infty)$ is $p^{-s}\Phi(s)^m$
by the change $t=\log(p/X)$. Subtract the lower endpoint and separate
the higher powers in the Euler series to obtain
$$\int_B^\infty H(X)X^{-s-1}dX=
\frac{B^{1-s}}{s-1}+\Phi(s)^m\left(\frac{\zeta'}{\zeta}(s)+R(s)\right)
+\int_0^B P_*(X)X^{-s-1}dX,$$
where $R(s)=\sum_p\sum_{j\ge2}(\log p)p^{-js}$. The endpoint term is
entire since only $p\le2^mB$ occur and all windows vanish below
$2^{1-m}$. The powers converge normally for $\Re s\ge\sigma>1/2$ by
comparison with $\sum_p (\log p)p^{-2\sigma}/(1-2^{-\sigma})$.
The residues at one cancel. There is no other real singularity above
$1/2$, by the Euler product above one and the positive paired eta
series on $(1/2,1)$.

If the nonnegative tail had convergence abscissa $b>1/2$, necessarily
$b\le1$. Regularity near $b$ gives a Taylor disk about $u=b+\epsilon$
reaching $b-\epsilon$ for sufficiently small $\epsilon>0$. Its
coefficients in $u-s$ are the moments of $(\log X)^j/j!$ against
$H(X)X^{-u-1}dX$, by convergence slightly left of $u$. All are
nonnegative as $B\ge1$. Summing at $b-\epsilon$ by monotone convergence
contradicts the abscissa. Thus the integral is holomorphic on
$\Re s>1/2$. Each zeta zero there would give a nonzero residue through
$\Phi^m\zeta'/\zeta$. Reflection proves ordinary RH at this stage.

### The square-root estimate and its hypotheses

Use either $f=h_m$ or $g=-h_4'-h_4$ as $f$. Their bilateral transforms
$K_f(s)=\int f(t)e^{st}dt$ are $\Phi^m$ and $(s-1)\Phi^4$,
respectively, the latter by integration by parts. Both are
$O_m((1+|\Im s|)^{-3})$ on $1/4\le\Re s\le2$; both kernels are
continuous at all knots. For a character $\chi$, assume the line
hypothesis **only for its inducing primitive function**. Write
$\delta_\chi=1$ for the principal character and zero otherwise. Then
$$\sum_p (\log p)\chi(p) f(\log(p/X))
=\delta_\chi X K_f(1)+O_{q,f}(\sqrt X). \tag{1}$$
This also applies to the unrestricted zeta sum on ordinary RH alone.

Indeed invert $K_f$ on $\Re s=2$ against $X^s(-L'/L)(s,\chi)$,
where inversion and Euler summation are absolute. This initially counts
all prime powers. Shift to $\Re s=1/4$. The principal pole contributes
$XK_f(1)$; the nontrivial zeros contribute $-\sum_\rho X^\rho K_f(\rho)$
with multiplicities. Neither parity has a trivial zero in the strip.
The extra factors $1-\chi^*(p)p^{-s}$ multiplying the inducing
primitive function to form $L(s,\chi)$ have no zeros or poles there:
Their logarithmic derivatives are bounded there for fixed $q$.

For the shift, take the real part of the completed primitive Hadamard
logarithmic derivative at $2+it$ (use $\xi$ for zeta). The real parts
of the $1/\rho$ corrections are summable by order one and the bounded
real parts of the zeros. Each $\Re(2+it-\rho)^{-1}$ bounds a constant
multiple of $(1+|t-\Im\rho|^2)^{-1}$ from below. Stirling and the
absolute Euler series therefore bound the sum of the latter weights
by $O_q(\log(3+|t|))$. In the difference of product derivatives at
$\sigma+it$ and $2+it$, zeros at ordinate distance greater than one
cost at most this bound. The remaining zeros are at distance at least
$1/4$ on the left edge. Choose upper and lower heights in unit
intervals by deleting neighborhoods of radius $c_q/\log(3+|t|)$ about
nearby ordinates: The local count leaves room for small $c_q>0$.
Removing the completion factors gives logarithmic growth on the left
edge and at most squared logarithmic growth on those horizontals.
Thus the new integral is $O_{q,f}(X^{1/4})$, the horizontals vanish
for fixed $X$, and $\sum_\rho|K_f(\rho)|<\infty$. This uses no zero
spacing. Even a central zero of multiplicity $r$ just contributes
$-r\sqrt X K_f(1/2)$, within the square-root bound.

With $l=m$ for $h_m$ and $l=4$ for $g$, removing squares costs at most
$\|f\|_\infty\vartheta((2^l X)^{1/2})=O_f(\sqrt X)$ by the ordinary
PNT. Powers $j\ge3$ have bases at most $(2^l X)^{1/3}$ and only
$O_l(\log(2X))$ possible exponents, hence total absolute weight
$O_f(X^{1/3}\log^2(2X))$. This proves (1) for genuine primes.

### Conservation exposes each zero separately

Apply (1) just to $P_*$ with $f=h_m$ under the ordinary RH already
proved. Thus $0\le H=O_m(\sqrt X)$ on the tail. Since each $H_a$ is
between zero and their sum, subtracting $MH$ gives
$$-MH\le D_a\le((d-1)M+1)H.$$
No hypothesis on a nonprincipal zero was used to reach this bound.
Now take the full complex character sum $S_\chi=\sum_a\chi(a)P_a$.
Since $\sum_a\chi(a)=d\delta_\chi$, the bound gives
$S_\chi-\delta_\chi X=O_{q,m,M}(\sqrt X)$. Its tail Mellin integral
is holomorphic on $\Re s>1/2$, whereas its expression from $\Re s>1$ is
$$-\Phi(s)^m\left(\frac{L'}{L}(s,\chi)+R_\chi(s)\right)
-\int_0^B S_\chi(X)X^{-s-1}dX-\delta_\chi\frac{B^{1-s}}{s-1}.$$
Here $R_\chi$ inserts $\chi(p)^j$ into $R$. The same endpoint and
absolute power bounds apply, and at one the principal residues cancel.
Every zero $\rho$ to the right of the line would leave residue
$-\operatorname{ord}_\rho L\cdot\Phi(\rho)^m\ne0$, impossible by
uniqueness of continuation. This includes a real exceptional zero;
there is no sign or real-axis nonvanishing requirement on $L$.
The imprimitive factors do not affect this half-plane. Since the
conjugate primitive character also induces a character modulo $q$,
the functional equation excludes nontrivial zeros to the left as well.

### One integer baseline in the other direction

Assume the joint line hypothesis and now fix $m=4$. The quartic
spline is globally $C^2$, and the sums are locally finite. Thus at
*every* real $X>0$, $X^2(P_a/X)'$ is exactly the class prime sum with
kernel $g$. If $T_\chi$ denotes the left side of (1) for $g$,
orthogonality gives $X^2(P_a/X)'=d^{-1}\sum_\chi\overline{\chi(a)}T_\chi$.
In (1), $K_g(1)=0$, even for the principal character. Taking absolute values
and summing over the finite family gives $|(P_a/X)'|\le C_qX^{-3/2}$
on a common tail, directly for the derivative, not by differentiating
an error estimate.

Lines 85–119 of the pinned quartic criterion give
$(P_*/X)'>cX^{-3/2}$ eventually, $c=\Phi(1/2)^4/100$. In its units
the removed squares contribute $+1/4$ and the absolute zero budget is
at most $((3+2\sqrt2)/2)^4(2+\gamma_E-\log(4\pi))/14<0.238$.
As an independent check of the ordinate cutoff, start with the real
interval $[1/2,2]$, evaluate $\zeta(I+14i)$ by FLINT `acb_zeta` at
96 bits on the midpoint-radius ball for $I$, and bisect whenever the
real part is not strictly positive. All 22 terminal balls had positive
real part. On the right edge $\Re s=2$ positivity follows from
$\sum_{n\ge2}n^{-2}<1$. At 128 bits `acb_lgamma` and the real-ball
logarithm give $\theta/\pi\in(-0.568,-0.567)$ for
$\theta=\Im\log\Gamma(1/4+7i)-7\log\pi$. Indeed, in the rectangle
$[-1,2]+i[0,14]$ the completed $\xi$ is positive on the bottom. The
change in argument along the right edge and the right half of the top
is $\pi+\theta+\arg\zeta(1/2+14i)$, where the last argument lies in
$(-\pi/2,\pi/2)$ by positivity. Reflection doubles this change for
the full contour. The zero count is therefore an integer in $[0,1)$.
Conjugation gives the negative ordinates. For the arithmetic budget,
at $n=200$ the Euler–Maclaurin upper bound
$H_n-\log n-1/(2n)+1/(12n^2)$ for $\gamma_E$ and the lower bound
obtained by subtracting $1/(120n^4)$ put the budget between
$0.23796810833$ and $0.23796810837$.

Since $P=P_*$ on the tail, choose an integer $M>C_q/c$, $M\ge1$.
Then all $(MP/X+P_a/X)'$ are strictly positive for all real $X$ past
one threshold. This proves the fixed-order strengthening. The test
uses no signed character weights or prime squares; they enter only
in the proof. Neither unconditional monotonicity nor uniformity in
$q$ follows.
