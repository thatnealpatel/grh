# Testing high endpoint witnesses at a small integer combination of heights

The height entering the prime estimate need not be either witness height, their sum, or their difference. For example, at $A=9/5$ two distinct twists cannot both fail at $y_i=3q^{3/5}$ and $y_j=q^{3/5}$, respectively. The $3:1$ relation yields an upper bound $(2+\sqrt2)/4+o(1)$ for a weighted mean which the Gamma term forces to be at least $8/9-o(1)$. This tests part of the remaining range; it does not bound the number of failing twists over the whole range.

Use the [individual-cutoff endpoint setup](fixed-strip-endpoints.md): $\xi$ is real primitive of conductor $q\to\infty$, $1<A<2$, $X=(A\log q)^2$, $D=\log X$, and distinct fundamental discriminants $|d|\le X^\theta$ are coprime to $q$, with $\theta>0$ fixed. Include $d=1$. Write $c_d=q|d|$, $b_p=X^{-1}\log p\log(X/p)$ for $p<X$, and $h_d(y)=\Re\sum b_p\xi(p)\chi_d(p)p^{iy}$. Assume the $7/8$ strip for primitive nonprincipal quadratic characters **and for zeta**, both covered by the [external theorem identified there](fixed-strip-endpoints.md#what-supplies-the-hypothesis). All transfers below are paper arguments.

## Odd coefficients: An exclusion independent of the base conductor in the prime estimate

Take fixed positive odd $a,b$, put $k=a+b$, and write $v=ay_i-by_j$. Either height may first be negated because each $h_d$ is even. For $t\in\mathbb R$ set $\tau(t)=\operatorname{dist}(t,2\pi\mathbb Z)$ and define

$$ g_k(t)=\cos(\tau(t)/k),\qquad G_k(t)=\tfrac12(g_k(t)+g_k(t+\pi)),\qquad I_k(X,v)=\int_0^1 G_k(v\log(Xu))\log(1/u)\,du. $$

Uniformly in the heights and distinct indices, with $M=[|d_i|,|d_j|]$, we have

$$ \frac{a h_i(y_i)+b h_j(y_j)}{k}\le I_k(X,v)+O_k\big(X^{-1/8}\log(2M(2+|v|))\big)+o(1). \tag{1} $$

Here and below $h_i=h_{d_i}$. The final $o(1)$ is uniform for fixed $A,\theta,k$. In particular, if $\log(2+|v|)=o(X^{1/8})$, the entire error tends to zero. With $u_k=\cos(\pi/(2k))$, the applicable caps on $I_k$ are

| Residual $v$ | Upper bound or limit |
| --- | --- |
| Any $v$ | $I_k\le u_k$ |
| $|v|D\to0$ | $I_k\to u_k^2=(1+\cos(\pi/k))/2$ |
| $|v|\to\infty$ | $I_k\to (k/\pi)\sin(\pi/k)$ |

Indeed $G_k(t)=u_k\cos((\tau(t)-\pi/2)/k)$, and $\log(1/u)\,du$ has mass one. Dominated convergence gives the tight-resonance limit. In the last limit the nonconstant Fourier modes integrate to zero in the limit by (3) below; the constant is the circle average of $g_k$.

**Where Gamma changes the decision.** From the individual-cutoff identity, failure ($Q_d(y)\le0$) needs $A h_d(y)\ge1+\log(2+|y|)/\log c_d-o(1)$. In particular $h_d\le1+o(1)$ rules out even one failure above $q^{A-1+\epsilon}$ for fixed $\epsilon>0$. In the remaining range one may replace $\log c_d$ by $\log q$ in this ratio at cost $o(1)$. Put $s_l=\log(2+|y_l|)/\log q$. Two failures require the left side of (1) to be at least

$$ B=\frac{a(1+s_i)+b(1+s_j)}{kA} \quad\text{up to }o(1). \tag{2} $$

If $B$ exceeds the applicable cap by a fixed positive margin, the pair is excluded at $\log(2+|v|)=o(X^{1/8})$, or even at $\log(2+|v|)\le\lambda X^{1/8}$ for sufficiently small fixed $\lambda$ depending on the margin and $k$. There is no assertion at equality. At heights $|y_l|=q^{r+o(1)}$ for the same $r\ge0$, $B=(1+r)/A+o(1)$. In the opening example take $a=1,b=3$: The residual is zero even though the ordinary sum and difference are of order $q^{3/5}$. A different example is $a=b=1$, $A=9/5$, $y_i=q^{1/5}+\exp(X^{0.12})$, $y_j=q^{1/5}$. The diverging-residual cap $2/\pi$ is strictly below $2/3$, whereas the universal cap $1/\sqrt2$ is not.

**Proof of (1).** On $p\nmid qM$ put $z_l=\xi(p)\chi_{d_l}(p)p^{iy_l}$. Let $x,y$ be the absolute principal angles of $z_i,z_j$ and $t$ the circular distance of $z_i^a\overline{z_j}^{\,b}$ from $1$ (absolute principal angle). The triangle inequality on the circle gives $ax+by\ge t$. Reduce $x,y$ to equality, which can only increase $a\cos x+b\cos y$. On that segment $x+y\le t\le\pi$; the derivative in $x$ is $a(\sin y-\sin x)=2a\cos((x+y)/2)\sin((y-x)/2)$. Thus $x=y=t/k$ maximizes the sum, including the possible flat case. This bounds the weighted mean pointwise by $g_k(\arg(z_i^a\overline{z_j}^{\,b}))$.

With both coefficients odd, the product is $\psi(p)p^{iv}$, where $\psi=\chi_{d_i}\chi_{d_j}$ has nonprincipal inducer of conductor dividing $M$. This cancellation of $\xi$ uses reality. Erasing or restoring the primes dividing $qM$ costs $O(D\log(qM)/X)=o(1)$ in weight, including in subsequent bounded angular tests. Expand $g_k(t)=c_0+2\sum_{j\ge1}c_j\cos(jt)$. Piecewise smoothness and continuity, or direct integration on $[0,\pi]$, give $c_j=O_k((1+j)^{-2})$. Odd modes use the [nonprincipal residue estimate (1)](strip-edge-height.md#a-uniform-residue-bound-on-the-original-weight) at $jv$. Even modes, including zero, use the principal estimate

$$ \sum_{p<X} b_p p^{it}=\frac{X^{it}}{(1+it)^2}+O\big(X^{-1/8}\log(2+|t|)+X^{-1/2}\log^3(2X)\big),\qquad \frac{X^{it}}{(1+it)^2}=\int_0^1(Xu)^{it}\log(1/u)\,du. \tag{3} $$

For (3) shift the integral of $-(\zeta'/\zeta)(s-it)X^s/s^2$ to $\Re s=1/16$. Along with the zero residues there is the pole at $1+it$, contributing **positive** $X^{1+it}/(1+it)^2$ before normalization. The entire completed zeta function $s(s-1)\pi^{-s/2}\Gamma(s/2)\zeta(s)$ has the Hadamard log-derivative difference at $2+iw$ and $-1+iw$ used in the nonprincipal proof. The two extra rational log-derivative terms are bounded at these points. This yields $\sum_\rho (1+(w-\Im\rho)^2)^{-1}\ll\log(2+|w|)$. Reflection puts all nontrivial zeros in $1/8\le\Re\rho\le7/8$; thus their residues total $O(X^{7/8}\log(2+|t|))$ in absolute value. On the new vertical, subtract the completed log derivative at $2+iw$: Separation in real part bounds the difference by the same inverse-square zero sum, and the Gamma and rational terms cost $O(\log(2+|w|))$. The new integral is $O(X^{1/16}\log(2+|t|))$. Horizontal heights avoiding zero ordinates as in the linked shift make the truncated horizontal costs vanish; the kernel pole and trivial zeros were not crossed. Remove higher prime powers at cost $O(X^{-1/2}\log^3(2X))$ after normalization.

The Fourier errors sum since $\sum |c_j|\log(2+j)<\infty$. Only even modes have a main term, exactly the modes of $G_k$. Substitution of (3) gives (1), with the remaining errors $O_k(X^{-1/2}\log^3(2X)+D\log(qM)/X)$. The pole main term cannot be dropped, even at very high individual heights, when the residual is small.

## One odd and one even coefficient: Which index could escape?

Now fix positive odd $a$ and positive even $b$, and fix $R=R(q)\ge2$ with $\log R=o(X^{1/8})$. On $[-XR,XR]$ the [signed-pair bound](strip-edge-height.md#spend-a-fixed-margin-not-an-o1-estimate) gives $h_i(w)+h_j(w')\le1+o(1)$ for distinct indices and independently chosen $w,w'$. Hence outside at most one index $d_*$, $\sup_{|w|\le XR}h_i(w)\le1/2+o(1)$, with a uniform error: Take the two suprema separately. This exceptional index is fixed for the whole enlarged band, not chosen afresh at each multiple of $v$.

For $|v|\le R$, the angular proof still holds, but the product on units is now $\xi(p)\chi_{d_i}(p)p^{iv}$. Its positive odd modes have real mean $h_i(jv)$ up to the erased prime mass. Direct cosine integration gives for $j\ge1$

$$ c_j=\frac{(-1)^{j+1}\sin(\pi/k)}{\pi k(j^2-k^{-2})}. $$

All odd coefficients are positive. Moreover $4\sum_{j>0\ \mathrm{odd}}c_j=g_k(0)-g_k(\pi)=1-\cos(\pi/k)$. For $j\le X$ the odd modes are in the enlarged band, while the discarded Fourier tail costs $O_k(X^{-1})$. Even modes still give $I_k(X,v)+o(1)$ by (3). Consequently if the **odd-coefficient index** $d_i$ is not exceptional, then

$$ \frac{a h_i(y_i)+b h_j(y_j)}{k}\le I_k(X,v)+\frac{1-\cos(\pi/k)}4+o(1). $$

The resulting universal cap is $1-(1-u_k)^2/2<1$, and the tight-resonance cap is $(3+\cos(\pi/k))/4$. When (2) beats the applicable cap by a fixed margin, an eligible failing pair must therefore have $d_i=d_*$ if it exists. This neither requires $d_*$ to fail nor requires it to be different from the base.

Even without discarding an index there is a test when the residual oscillates. Bound the unknown sign pointwise by the better of its two possibilities: $\max(g_k(t),g_k(t+\pi))=\cos(\operatorname{dist}(t,\pi\mathbb Z)/k)$. This continuous piecewise smooth function has Fourier coefficients $O_k((1+j)^{-2})$ by integration by parts on the smooth arcs (the first derivative has bounded variation). It is applied just to $t=v\log p$, so all frequencies now use (3). If $|v|\to\infty$ and $\log(2+|v|)=o(X^{1/8})$, only its circle average $(2k/\pi)\sin(\pi/(2k))<1$ survives. This cap applies even to $d_i=d_*$; at $v=0$ the same sign maximum is $1$, which is why the band exception matters for tight mixed-parity resonances.

## What remains

There is no uniform exclusion here for two nonresonant heights. For instance take $A=9/5$, $y_i=q^{1/5}$, $y_j=q^{3/5}$. Their required individual means are only $2/3-o(1)$ and $8/9-o(1)$; every fixed positive-coefficient signed combination above has magnitude $q^{3/5+o(1)}$. Even with the larger Gamma threshold, the strip error in (1) is of order $X^{3/8}$ there. This is a test case, not a pair of failing twists. A sufficient arithmetic target on that pair is an upper bound **strictly below $5/9$ by a fixed margin** for the average of the two real $b_p$-weighted $\psi$ means at $y_i+y_j$ and $y_i-y_j$: Their combined contribution has to make up the excess $2/3+8/9-1=5/9$ in the signed-pair bound. No separate absolute-value saving on each mean is logically required.

There is also a conductor-free necessary condition on the larger witness alone. Since the character values are real and of modulus at most one, Cauchy–Schwarz gives $h_j(y_j)^2\le(\sum b_p)\sum b_p\cos^2(y_j\log p)$. Thus the required $8/9-o(1)$ forces $\Re\sum b_p p^{2iy_j}\ge 47/81-o(1)$. A one-sided bound strictly below this constant would already exclude the pair. Formula (3) has the same $X^{3/8}$ error at $2y_j$. Nor does the [Ford estimate used on integer sums](relative-height-weil-list.md) give this conclusion: Besides lacking the prime weight, at length $X$ its saving exponent $\log^3 X/\log^2|2y_j|$ tends to zero. These are two distinct tests for the nonresonant range, neither settled by the cited estimates. Neither the all-height endpoint list nor an unrestricted Weil floor follows from the resonant tests.
