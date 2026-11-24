---
evidence_revision: 9328b646effbe6e2cc0559c62e40521bab600b48
outcome: established
---

# The fixed order-three ordinary RH prime comparison

Put $a=\log 2$ and $h_3=\mathbf{1}_{[0,a]}^{*3}$, with
convolution in the log variable and support $[0,3a]$.
For real $X>0$, sum over all rational primes and set

$$B_3(X)=\sum_p(\log p)h_3(\log(p/X))-X,\qquad
S_3(X)=\sum_p(\log p)h_3(\log(p^2/X)).$$

**Proposition to test:** Ordinary RH is equivalent to the
existence of a real $A\ge1$ such that for every real $X\ge A$,

$$\sqrt2 B_3(X)-B_3(2X)\le S_3(X).$$

**Source and payoff:** This is an operator strengthening of
the linear case of the [Dedekind prime root comparison](../closed/dedekind-prime-root-critical-dilation.md)
at `e29848af48be97061090219fcb2ea99e27079367`, which permits
a choice of order in the forward implication. The pinned
[signed order-two obstruction](../open/zeta-order-two-prime-comparison.md)
concerns only order two. Order three would identify the
least working order under RH, with the same centering and
square allowance, without deciding the literal order-two
biconditional.

**Discriminating test:** On RH let $D(s)=\sqrt2-2^s$,
$\Phi(s)=(2^s-1)/s$, and $k=\Phi(1/2)$. Verify the
completed-zeta product identity for $C=\sum_\rho|\rho|^{-2}$
with multiplicities on RH. Drop any central term in the
dilated zero sum and use nonreal conjugate pairs to test
whether $2\sqrt2((\sqrt2+1)/k)^3 C\sqrt{C/2}<1/2$, with
rigorous constants independent of a zero table. A strict
margin would suffice by the linear-case asymptotic. Verify
that the fixed-order converse applies at $m=3$, checking the
centering, undilated allowance, and Mellin tail endpoints.

## Adjudication

**Yes.** In the ordinary linear case the normalized allowance tends to
$1/2$. At order three the absolute zero sum is less than $0.492$ on RH.
This gives the required sign for the entire tail, without locating a zero.

### The third factor

Write $r=\sqrt2$. For the entire order-one function
$\xi(s)=s(s-1)\pi^{-s/2}\Gamma(s/2)\zeta(s)/2$, subtract its genus-one
product logarithmic derivatives at $1$ and $0$. The exponential constant
and the regularizing terms cancel. With zeros repeated by multiplicity,

$$\sum_\rho \frac1{\rho(1-\rho)}
=\frac{\xi'}{\xi}(1)-\frac{\xi'}{\xi}(0)
=2\frac{\xi'}{\xi}(1)=2+\gamma_E-\log(4\pi).$$

The difference sum converges absolutely by order one. The second equality
uses the functional equation; the last uses $(s-1)\zeta(s)=1+
\gamma_E(s-1)+O((s-1)^2)$ and $\psi(1/2)=-\gamma_E-2\log 2$.
On RH, $1-\rho=\bar\rho$, so the displayed constant is $C$.
Any central term vanishes in the dilation. Each nonreal zero and its
*distinct* conjugate contribute at least $2/|\rho|^2$ together to $C$.
Use this only for the third reciprocal factor: The sum of the two-factor
weights $|\rho|^{-2}$ already includes both signs. Since $|D|\le2r$ and
$|2^\rho-1|\le r+1$ on the line, this gives

$$\sum_\rho |D(\rho)|\left|\frac{\Phi(\rho)}k\right|^3
\le 2r\left(\frac{r+1}{k}\right)^3 C\sqrt{C/2}<0.492.$$

Here is a reproducible rational certificate for the strict comparison.
Take $N=2^{17}$, $M=10^{12}$, and sum the integers
$h=\sum_{j=1}^N\lfloor M/j\rfloor=12360721484315$.
Then $H_N<(h+N)/M$ and $\gamma_E\le H_N-\log N$ by integral comparison.
Put $p_0=314159/100000$. Machin's formula and the alternating arctangent
series give the rational lower bound

$$\pi>16\sum_{j=0}^3 \frac{(-1)^j(1/5)^{2j+1}}{2j+1}-4/239>p_0.$$

For $x>1$ set $z=(x-1)/(x+1)$ and
$L(x)=2\sum_{j=0}^9 z^{2j+1}/(2j+1)<\log x$. Combining the logarithms,
the rational comparison is

$$C<2+(h+N)/M-20L(2)-L(p_0/2)<231/5000=:c.$$

Put $u=1414214/10^6$, $v=19/125$. By squaring, $u>r$ and
$v>\sqrt{c/2}$. Since $k=2(r-1)$, $(r+1)/k=(3+2r)/2$. Hence an upper
bound for the budget is the exact rational

$$2u((3+2u)/2)^3 c v
=\frac{9601189712128433785498074789}{19531250000000000000000000000}
<492/1000<1/2.$$

### Matching the prime observable in both directions

At `e29848af48be97061090219fcb2ea99e27079367`, lines 72–91 of the
linked linear-case specialization apply before any choice of order.
Indeed $\Phi^3$ is the transform of the continuous third convolution,
with cubic decay on the shift strip. The full Euler sum contributes
$X\Phi(1)^3=X$ from the pole, exactly the centering. Its square sum
is exactly $S_3$, with weight $\log p$; powers $j\ge3$ cost
$O(X^{1/3}\log^2(2X))$. By PNT and partial summation,
$S_3(X)/\sqrt X\to\int h_3(t)e^{t/2}dt/2=k^3/2$. Thus the removed
square term cancels to leading order in $rB_3(X)-B_3(2X)$, whereas
the allowance on the right is **not** dilated. For the slack
$H(X)=S_3(X)-rB_3(X)+B_3(2X)$, the normalized formula is

$$\frac{H(X)}{\sqrt X\,k^3}=\frac12+
\sum_\rho D(\rho)(\Phi(\rho)/k)^3 X^{i\Im\rho}+o(1).$$

The absolute bound is independent of real $X$, giving positive liminf
and hence a threshold for all sufficiently large real $X$.

Conversely fix that order and assume $H\ge0$ on $[A,\infty)$, $A\ge1$.
In lines 95–110 of the same landing, take $P(X)=B_3(X)+X$,
$Q(s)=\sum_p(\log p)p^{-s}$, $R(s)=\sum_{j\ge2}Q(js)$, and
$Y=\zeta'/\zeta$, so $Q=-Y-R$ initially on $\Re s>1$.
Writing $I_U(b,s)=\int_0^b U(X)X^{-s-1}dX$, the tail transform is

$$\begin{aligned}
\int_A^\infty H(X)X^{-s-1}dX
={}&\Phi(s)^3[Q(2s)+D(s)(Y(s)+R(s))]+D(1)A^{1-s}/(s-1)\\
 &-I_{S_3}(A,s)+rI_P(A,s)-2^s I_P(2A,s).
\end{aligned}$$

Indeed a full $p^j$ spline transforms to $p^{-js}\Phi(s)^3$; only the
dilated $P$ changes endpoint to $2A$. The finite integrals are entire
since the uncentered observables vanish near zero. The separate linear
tail cancels the pole at one. Both Euler remainders $Q(2s),R(s)$ converge
normally for $\Re s>1/2$. Every zeta zero there gives a pole, since
$D\Phi^3$ is nonvanishing there; at a real zero the residue is negative.
If the nonnegative tail had convergence abscissa $b>1/2$, a pole at $b$
would give negative divergence from the right. Regularity at $b$ is also
impossible: Expand at $b+\epsilon$ inside a disk of regularity about $b$;
for small $\epsilon>0$ the expansion reaches $b-\epsilon$. The moments
of $\log X$ are nonnegative, so monotone convergence would give a finite
integral at $b-\epsilon$. Thus the transform is holomorphic on
$\Re s>1/2$, excluding every such zero. Reflection gives RH.

Finally $|\Phi(\rho)|\le k$ on RH by the interval integral. Every fixed
integer $m\ge3$ inherits the same normalized bound and converse, with no
common threshold asserted. The signed recurrence at the evidence pin,
lines 38–75, excludes the order-two eventual inequality even on RH.
Three is therefore the least working order **under RH** among $m\ge2$.
The literal order-two biconditional is equivalent to $\neg\mathrm{RH}$,
not decided here. Neither the order-three prime inequality unconditionally
nor an order-three bound for another field follows.
