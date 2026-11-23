# The second term of the unsigned window norm detects RH

The leading prime norm does not distinguish the character phases. Can one at least refine its unsigned edge cheaply enough to decide the critical conductor window? There are two obstructions: The additive norm estimate is already RH-strength, and the unsigned comparison itself is negative on low-energy tests along a sequence at criticality.

Let $X=e^D$, $E=\sqrt X$, and on $L^2[0,D]$ let $T$ be the sum of the two zero-extended translations by $\pm\log n$, with coefficient $\Lambda(n)/\sqrt n$, over $n<X$. No primes are omitted. As $D\to\infty$, the following are equivalent:

1. The Riemann hypothesis for $\zeta$.
2. $\|T\|=E+D+O(1)$.
3. $\|T\|\le E+O(D^2)$.

These are paper estimates. The [unconditional norm estimate](../adhoc/prime-translation-norm.md) is $\|T\|=(1+o(1))E$. None of these unsigned estimates gives cancellation in a signed Weil form.

## An endpoint lower bound and its Mellin obstruction

Write $\psi(t)=\sum_{n\le t}\Lambda(n)$, $B(X)=\sum_{n\le X}\Lambda(n)\log(X/n)$, and $F(X)=B(X)-X$. Take $f(x)=e^{-x/2}$, $g(x)=f(D-x)$, and $w=f+g$ on the window. The [endpoint correlation identity](endpoint-arithmetic-test.md) gives its exact quotient

$$
 Q(E)=\frac{B(X)/E+2\sum_{n\le X}\Lambda(n)/n-2\psi(X)/X
 +E^{-1}\sum_{n\le X}(\Lambda(n)/n)\log(X/n)}{1-X^{-1}+D/E}.
$$

Classical PNT with its zero-free-region remainder gives $\psi(X)/X=1+o(1)$, $B(X)/X=1+o(1/D)$ by $B(X)=\int_1^X\psi(t)\,dt/t$, and $\sum_{n\le X}\Lambda(n)/n=D+O(1)$ by partial summation. The last sum in the numerator, before division by $E$, is $O(D^2)$. Expanding the denominator therefore gives the unconditional estimate

$$ Q(E)=E+F(X)/E+D+O(1). \tag{1} $$

In particular (3) implies $F(X)\le K\sqrt X\log^2 X$ eventually. For $\Re s>1$ direct integration gives

$$ \int_1^\infty F(X)X^{-s-1}dX=-\frac{\zeta'(s)}{s^2\zeta(s)}-\frac{1}{s-1}. \tag{2} $$

The pole at 1 is removable, and $\zeta$ has no real zero in $(0,1)$. Apply Landau's singularity theorem for the Mellin transform of the nonnegative tail of $K\sqrt X\log^2 X-F(X)$. If its abscissa were greater than $1/2$, that real point would be singular. But (2), the transform $2K/(s-1/2)^3$, and the entire contribution of a bounded initial interval give analytic continuation there. Hence the integral is holomorphic on $\Re s>1/2$. A zeta zero there would give an uncanceled pole by (2). Reflection gives RH. This argument uses only an **upper** norm bound.

## A corrected Schur weight under RH

Assume RH. We use the classical pointwise estimate $|\Delta(t)|\ll\sqrt t(1+\log^2 t)$ for $t\ge1$, where $\Delta(t)=\psi(t)-t$, and Cramér's mean square $\int_Y^{2Y}\Delta(t)^2dt\ll Y^2$ for $Y\ge1$ (see [Brent, Platt, and Trudgian](https://arxiv.org/abs/2008.06140)). On each dyadic interval Cauchy–Schwarz gives $\int_Y^{2Y}|\Delta(t)|dt/t\ll\sqrt Y$. Summing gives $F(X)=O(E)$, so (1) gives the lower bound $\|T\|\ge E+D-O(1)$. For the upper bound one must control all tests.

Define $h(z)=e^{-z/2}|\Delta(e^z)|$ for **all real** $z$, and $r(x)=h(x)+h(D-x)$ on the window. With $U(s)=\sum_{n\le e^s}\Lambda(n)/n=s+O(1)$, the translation identity is $Tf=f[U(D-x)+\psi(e^x)]$ almost everywhere. Add its reflection. The main terms of $\psi$ give exactly $Ew$, the terms from $U$ are at most $(D+C_0)w$, and the remaining error is at most $r$. Also $T1\ll e^{x/2}+e^{(D-x)/2}=Ew$ by partial summation. Thus

$$ Tw\le(E+D+C_0)w+r,\qquad T1\ll Ew. \tag{3} $$

We claim $Tr\le cE$ on the entire interval with an absolute constant. The pointwise bound gives $\|r\|_\infty\ll 1+D^2$. The mean square gives the stronger local-average bound $\int_J h(s)ds\ll1$ for every interval $J$ of length at most 3: Above zero use $\int_{\log Y}^{\log(2Y)}h(s)^2ds=\int_Y^{2Y}\Delta(t)^2dt/t^2\ll1$, and below zero use $h(s)=e^{s/2}$. With $\tau=E^{-1}$, monotonicity of $\psi$ gives for $0\le z\le D$

$$ h(z)\ll 1+\tau^{-1}\int_{z-\tau}^{z+\tau}h(s)ds. \tag{4} $$

Indeed, average forward by at most $\tau$ for $\Delta(e^z)\ge0$, and backward otherwise. The drift after dividing by $e^{z/2}$ is $O(e^{z/2}\tau)=O(1)$. It is important not to zero-extend $h$ in (4).

For $n<X^{2/3}$ the total cost in $Tr$ is $O((1+D^2)X^{1/3})=o(E)$. For the other samples use dyadic shells $K\le n<2K$, $X^{2/3}/2\le K\le X$. Each of the at most four types of sample has argument $z=a\pm\log n$ in $[0,D]$, for fixed $a$ at each row. The constant term of (4) costs $O(\sqrt K)$ per shell. In the integral term interchange the sum and the integral. For each $s$, the allowed $n$ lie in an interval that can be padded to length $L\asymp K\tau$ near the shell. Here $L\gg X^{1/6}$ and $L\ll\sqrt K$. Brun–Titchmarsh in an interval bounds its prime Mangoldt mass by $O(L\log(2K)/\log L)=O(L)$. For each exponent $m\ge2$ consecutive $m$-th powers in the shell are spaced by at least $\sqrt K$. These powers contribute $O((1+L/\sqrt K)\log^2(2K))=O(L)$ over all exponents. The $s$ range has length at most $\log 2+2\tau$, so its integral of $h$ is bounded. The integral term therefore costs $O(L/(\tau\sqrt K))=O(\sqrt K)$. The geometric shell sum is $O(E)$, proving the claim.

Now take $W=w+r/E+c/E$, using $Tr\le cE$. By (3),

$$ TW\le (E+D+C_1)w+r+c\le(E+D+C_1)W $$

for absolute $C_1\ge0$. Weighted Schur for the symmetric nonnegative translations bounds $|\langle Tu,u\rangle|$ by $\int(TW/W)|u|^2$ for every test. This proves the upper bound with coefficient one on $D$ and completes the equivalence.

## What fails at the critical unsigned comparison

There are arbitrarily large $X$ with $F(X)>-\sqrt X$. Otherwise $-F(X)\ge\sqrt X$ on a tail, with convergence abscissa at least $1/2$; Landau would force a real singularity at or above $1/2$, contrary to (2). At $E=\sqrt X$ along this sequence, (1) gives $Q(E)\ge E+D-O(1)$. Bertrand's postulate gives a prime $q$ with $\log q=E+O(1)$. The change in $F(E^2)/E$ is $o(1)$: The locally absolutely continuous function has derivative $(2\psi(E^2)-B(E^2))/E^2-1=o(1)$ almost everywhere by PNT. Thus the same lower bound holds at the exact critical size $E'=\log q$, $D'=2\log E'$.

The unmodulated $w$ has Gamma quotient $O(1)$ in both parities, by its uniform $O((1+|y|)^{-1})$ Fourier decay and norm bounded below. Its correlations are nonnegative, and $q>(\log q)^2$ removes no active prime. Charging absolute prime correlations against the full conductor plus Gamma on **this same test** gives at most $-D'+O(1)$ along the sequence. Contracting and mollifying in the log-weighted Fourier norm as in the [endpoint note](endpoint-arithmetic-test.md) gives smooth interior tests with strict negative unsigned comparison. This does not exhibit a negative **signed** Weil test. Even at exact criticality the unsigned strategy fails, not merely its current error estimate.
