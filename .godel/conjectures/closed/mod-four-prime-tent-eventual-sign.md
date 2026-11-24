---
evidence_revision: dca062832345d6f827769b6a1af9b923d21e3b0e
outcome: established
---

# Eventual signs of the local mod-four prime tent

Let $\chi_4$ be the primitive real character modulo $4$.
For real $X\ge1$ use only genuine primes and natural logs:

$$P(X)=\sum_{p<X}\chi_4(p)\log p\,\log(X/p),\qquad
W(X)=P(16X)-2P(4X)+P(X).$$

**Proposition to test:** There exists a real $X_0\ge1$
such that $W(X)\le0$ for every real $X\ge X_0$ if and
only if every nontrivial zero of $L(s,\chi_4)$ has real
part $1/2$. No sign of $P$, rate, sampled signs, or
independence of zero ordinates is assumed.

**Source and payoff:** This operator conjecture changes
the weight in the [all-cutoff prime ramp criterion](../closed/mod-four-prime-ramp-eventual-sign.md)
at the evidence revision and the [polynomial-grid criterion](../closed/mod-four-prime-ramp-polynomial-grid-sign.md)
at `e96c4611fa01385ff9c6345f1dc4ab27ec8425f8`. The
original ramp is Bob's [equation (1)](../../bob/fixed-strip-endpoints.md#the-product-mean-at-the-original-endpoint-weight)
at `bbca37033019090f6f40e6223b5054d382c9d789`, with
$(d_i,d_j)=(1,-4)$ and $v=0$, before cutoff normalization.
Neither source asserts this local criterion. It would
identify a weighted comparison of actual residue-class
prime counts in one multiplicative interval that would
imply zero location if proved unconditionally.

**Discriminating test:** Compute the exact supported
weight, its center, and its signs prime by prime. Apply
the same rescalings to the prime-power explicit formula,
preserving multiplicities and the square coefficient and
comparing the square main term with the absolute residue
cost on the zero-line hypothesis. Test whether
$C=\sum_\rho |\rho|^{-2}<2/9$ follows from elementary
rational enclosures at $1$ for the completed beta log
derivative, using the alternating derivative and certified
log series tails rather than sampled zeros. For the other
direction transform the nonnegative tail of $-W$, track
all finite-endpoint terms, and check real regularity and
noncancellation by the kernel before applying Landau and
reflection. A failed absolute budget alone would not
refute the criterion. No single-tiling claim is tested.

## Adjudication

**The equivalence holds for all sufficiently large real translates.** The sign of the cumulative ramp is not an input. The grid card, line 75 at its pin, restricts the all-cutoff sign to $n^k$; it does not difference those signs. Bob's (1) is used for magnitude at lines 45–49, not for this comparison.

### What is being compared

For $u=p/X$, the coefficient of $\chi_4(p)\log p$ is

$$h(u)=(\log(16/u))_+-2(\log(4/u))_++(\log(1/u))_+
       =\max\{0,\min\{\log u,\log(16/u)\}\}.$$

The first equality adds the three prime hinges; the second follows by splitting at $1,4,16$. Thus the endpoints contribute zero. The peak is $\log4$ at $p=4X$, and inside the tent the signs are positive for $1\bmod4$, negative for $3\bmod4$, and zero at $2$.

### From the critical line to the local sign

Write $L=L(s,\chi_4)$ and $Q(U)=\sum_{n<U}\Lambda(n)\chi_4(n)\log(U/n)$. On the line hypothesis, the pinned ramp proof, lines 70–74, gives

$$Q(U)=-\sum_\rho U^\rho/\rho^2 + b\log U+c +O(U^{-1/2})$$

for every real $U>1$, counting multiplicities. The contour is left of $0$ but right of the first trivial zero; the double kernel pole supplies the affine term. Absolute convergence permits termwise differencing. The affine term vanishes, and each zero acquires the factor $(4^\rho-1)^2$. To pass from $Q$ to genuine primes **subtract** the odd squares: Each coefficient is $\log p$, and their ramp is $2\int_1^{\sqrt U}\vartheta_{\rm odd}(t)\,dt/t=(2+o(1))\sqrt U$ by PNT. The main term after differencing still has coefficient $2(4-2\cdot2+1)=2$. Powers of exponent at least three cost $O(U^{1/3}\log^2 U)$ by the Chebyshev bound summed over exponents. Thus

$$ W(X)=-2\sqrt X-\sum_\rho X^\rho(4^\rho-1)^2/\rho^2+o(\sqrt X). $$

The absolute cost is at most $9C\sqrt X$, since $|4^\rho|=2$. The old $C<4/3$ does not settle the sign.

### Rational certificate for the new budget

For the completion $B(s)=(4/\pi)^{(s+1)/2}\Gamma((s+1)/2)L(s)$ put $D=2B'(1)/B(1)$. The paired product at the pin, lines 61–66, gives $C=D$ on the line: A conjugate pair of height $\gamma$ contributes $(1/4+\gamma^2)^{-1}$ to $B'(1)/B(1)$, half its contribution to $C$. Unconditionally,

$$D=\log(4/\pi)-\gamma_E+2L'(1)/L(1).$$

For a short upper certificate for $L'(1)$, write $f(n)=\log(n)/n$. Differentiating the alternating odd series (locally uniform by partial summation) gives $f(3)-f(5)+\cdots$. After $+f(11)$ one must subtract $A=f(13)-f(15)+\cdots$. On $t\ge13$, $f$ is decreasing and convex since $f''=(2\log t-3)/t^3$. Thus $2A-f(13)$ is the alternating sum of the positive decreasing differences $f(13+2j)-f(15+2j)$, and is nonnegative. In particular,

$$0<L'(1)\le f(3)-f(5)+f(7)-f(9)+f(11)-f(13)/2
<217317/1100000<1/5.$$

Here are reproducible integer enclosures. For $n=(2,3,5,7,9,11,13)$ the lower integers for $10^4\log n$ are respectively $(6931,10986,16094,19459,21972,23978,25649)$; add one for each upper integer. To check, put $z=(n-1)/(n+1)$ and sum $S=2\sum_{j=0}^{47}z^{2j+1}/(2j+1)$: Use $S<\log n\le S+2z^{97}/(97(1-z^2))$. In the derivative bound round up the positive terms and down the subtracted terms. Positivity follows by alternation since $f$ decreases from $3$ onward. Also

* $\gamma_E\ge H_{127}-\log128>H_{127}-7(6932/10000)>57/100$, by the lower sums $H_n-\log(n+1)$.
* $L(1)=\pi/4=\arctan(1/2)+\arctan(1/3)>1538665/1959552>25/32$, using $x-x^3/3+x^5/5-x^7/7$ at each argument.
* $\log(4/\pi)<\log(32/25)<1/4$, since $1+1/4+1/32>32/25$.

It follows that $D<1/4-57/100+2(1/5)/(25/32)=24/125<2/9$. On the line, this gives $W(X)\le(-34/125+o(1))\sqrt X$ for all real $X\to\infty$.

In fact $C<2/9$ also holds without the line assumption, though $C=D$ is not needed off the line. Pair $\rho,1-\rho$ in the order-one product about $1/2$; there is no central zero, and evenness kills the linear exponential. Each pair contributes $1/[\rho(1-\rho)]$ to $B'(1)/B(1)$, so $D=\sum_\rho d_\rho$ for $d_\rho=\Re(1/[\rho(1-\rho)])$. Pairing and taking real parts are justified by the zero count at the pin. Write $\beta=\Re\rho$, $t=(\Im\rho)^2$, $a=\beta(1-\beta)$. The Euler product and reflection give $0\le\beta\le1$; real zeros are excluded by alternation and reflection. Then

$$d_\rho=\frac{t+a}{(t+\beta^2)(t+(1-\beta)^2)}\ge\frac1{1+t},$$

since the cross-multiplied difference is $3at+a-a^2\ge0$. A zero and its conjugate already cost $2/(1+t)$ or more, so $D<1/5$ implies $t>9$. Now $|\rho|^{-2}/d_\rho=(t+(1-\beta)^2)/(t+a)<10/9$. Hence $C<(10/9)(24/125)=16/75<2/9$. This cannot replace the use of the line in $|X^\rho|=\sqrt X$.

### From the local sign to the critical line

Suppose $-W(X)\ge0$ for $X\ge A\ge1$. Put $Y=L'/L$ and $H(s)=\sum_p\sum_{k\ge2}\chi_4(p)^k(\log p)p^{-ks}$, normally convergent on $\Re s>1/2$ by the geometric bound on the inner sum. For $\Re s>1$ a single prime hinge has Mellin integral $p^{-s}/s^2$, so $-P$ has transform $(Y+H)/s^2$ from $1$. Under $U=cX$ the lower endpoint becomes $cA$. Thus, for $(w_1,w_4,w_{16})=(1,-2,1)$,

$$\int_A^\infty [-W(X)]X^{-s-1}\,dX=
\frac{(4^s-1)^2}{s^2}(Y(s)+H(s))
+\sum_{c=1,4,16} w_c c^s\int_1^{cA}P(U)U^{-s-1}\,dU.$$

The finite terms are entire; the meromorphic right side is regular at every real $s>1/2$ because $L(s)\ge1-3^{-s}>0$. Landau's argument for the nonnegative tail gives convergence throughout $\Re s>1/2$: At a larger abscissa of convergence, regularity would allow a Taylor series centered just to its right to reach a real point to its left. The coefficients in powers of the center minus $s$ are nonnegative log moments divided by factorials, so monotone convergence would give a finite integral there. Thus the transform is holomorphic in the half-plane. A zero $\rho$ there of multiplicity $m$ would leave residue $m(4^\rho-1)^2/\rho^2\ne0$, since $4^s=1$ only on $\Re s=0$. This contradicts holomorphy. Reflection rules out left-of-line zeros as well.

**What is still open.** For $a=1,3$ write $T_a(y,z)=\sum_{y<p\le z,\ p\equiv a\bmod4}\log p$. The exact tent is the integral of the indicator of $tX<p\le16X/t$ over $1\le t\le4$ against $dt/t$. Thus the unconditional input still needed is

$$\int_1^4 T_3(tX,16X/t)\,\frac{dt}{t}\ \ge\
\int_1^4 T_1(tX,16X/t)\,\frac{dt}{t}$$

for every sufficiently large real $X$. This is one weighted comparison of genuine primes per translate, not a pointwise inequality for every $t$, an unweighted majority, or a condition on a single disjoint tiling. The proof establishes the equivalence, not this inequality unconditionally.
