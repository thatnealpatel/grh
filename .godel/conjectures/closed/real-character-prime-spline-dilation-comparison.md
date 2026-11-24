---
evidence_revision: d3675071daa1e1afbff4107024f1a9943855a43b
outcome: established
---

# Two-scale prime spline comparisons for fixed real characters

Fix any primitive nonprincipal real Dirichlet character
$\chi$, without a real-axis nonvanishing hypothesis. Let
$h_m=\mathbf{1}_{[0,\log 2]}^{*m}$ under ordinary real
convolution, and for $X>0$ set

$$W_m(X)=\sum_p\chi(p)\log p\,h_m(\log(p/X)).$$

For each integer $j\ge1$ put $a_j=1/2+1/(j+2)$,
$c_j=2^{a_j}$, and $V_{j,m}(X)=c_jW_m(X)-W_m(2X)$.

**Proposition to test:** The following are equivalent:

1. Every nontrivial zero of $L(s,\chi)$ has real part
   $1/2$.
2. For every $j\ge1$ there are an integer $m\ge2$ and
   $X_0\ge1$ such that $V_{j,m}(X)\le0$ for all real
   $X\ge X_0$.

The order and threshold may depend on $\chi,j$, and the
threshold on the order. There is no sign requirement on
$W_m$ itself and no uniformity in $j$ or the conductor.

**Source and payoff:** This operator-proposed comparison
replaces the one-scale sign in the pinned
[fixed-character criterion](../closed/real-character-prime-spline-eventual-sign.md),
whose converse assumes real-axis nonvanishing. Bob's
[endpoint estimate (1)](../../bob/fixed-strip-endpoints.md#the-product-mean-at-the-original-endpoint-weight)
at `bbca37033019090f6f40e6223b5054d382c9d789` is a
magnitude bound under a different premise, not this
comparison. The question is whether comparing two true
local prime sums can encode zero location without the
extra real-axis premise. Neither landing asserts this
repair.

**Discriminating test:** On the critical-line hypothesis,
compute the square and central-zero bias after dilation,
and test whether the noncentral terms can be made smaller
than the surviving margin for each fixed $j$ by a fixed
order. In the reverse direction, compute the tail Mellin
transform of $-V_{j,m}$ with its finite endpoint terms.
Test whether the multiplier $(c_j-2^s)K(s)^m$, where
$K(s)=(2^s-1)/s$, can permit a real zero above $a_j$ to
be the first singularity of a nonnegative tail. Separate
the domain of integral convergence from meromorphic
continuation, locate possible complex cancellations on the
boundary, and test the passage from each $a_j$ to $1/2$
without any uniformity in the orders.

## Adjudication

**The two conditions are equivalent.** For one $j$, the comparison excludes the entire open half-plane $\Re s>a_j$. The key is not to assume that a real zero is rightmost: Test the real abscissa of the nonnegative tail itself.

### From one comparison to a zero-free half-plane

Fix $j$, write $a=a_j$, $c=2^a$, and take $m$ and $A=X_0\ge1$ from the comparison. Put $W=W_m$, $V=V_{j,m}$. On $\Re s>1$ the full transform of $-W$ against $X^{-s-1}dX$ is

$$H(s)=K(s)^m\left(\frac{L'}{L}(s,\chi)+R(s)\right),\qquad
R(s)=\sum_p\sum_{\ell\ge2}\chi(p)^\ell\log p\,p^{-\ell s}.$$

Indeed $t=\log(p/X)$ gives $p^{-s}K(s)^m$ for a single spline by convolution. Absolute prime summability permits integration term by term, and removing the higher powers from $L'/L$ gives the indicated plus sign. Write $I_D(s)=\int_0^D W(X)X^{-s-1}dX$. This is entire for every finite $D>0$: Only finitely many primes enter and $W$ vanishes for $X<2^{1-m}$. Changing variables in the *truncated* dilate gives

$$\begin{aligned}
F_A(s)&=\int_A^\infty[-V(X)]X^{-s-1}dX\\
&=c(H+I_A)-2^s(H+I_{2A})\\
&=(c-2^s)H(s)+\int_0^A V(X)X^{-s-1}dX.
\end{aligned}$$

The endpoint correction is entire. The formula continues $F_A$ meromorphically to $\Re s>1/2$: On $\Re s\ge\sigma>1/2$, $R$ converges normally by comparison with $\sum_p(\log p)p^{-2\sigma}/(1-2^{-\sigma})$. The only possible poles are simple, at zeros $\rho$ of $L$, with residue $\operatorname{ord}_\rho(L)(c-2^\rho)K(\rho)^m$ unless canceled.

Let $b\le1$ be the real convergence abscissa of the nonnegative tail, possibly $-\infty$. The integral is holomorphic on $\Re s>b$ by domination on smaller half-planes of convergence. Meromorphic uniqueness from $\Re s>1$ identifies it with the continuation on $\Re s>\max(b,1/2)$, so the latter has no poles there. Suppose $b\ge a$.

* If regular at $b$, the continuation is holomorphic on a disk of radius $4\epsilon$ about $b$ for some $\epsilon>0$. At $u=b+\epsilon$ its Taylor coefficients in $u-s$ are $\int_A^\infty(-V)X^{-u-1}(\log X)^n dX/n!$, all nonnegative. Differentiation uses convergence at $b+\epsilon/2$. The series is finite in value at $b-\epsilon$. By monotone convergence of the exponential series under the integral, that value would be a convergent tail integral at $b-\epsilon$, contradicting the abscissa.
* Otherwise $b$ is a real zero with an uncanceled pole. At $b=a$ the factor $c-2^b$ would cancel it, even for a multiple zero since $L'/L$ has only a simple pole. Thus $b>a$, and the residue is strictly negative because $K(b)=\int_0^{\log 2}e^{bt}dt>0$. The pole then gives $F_A(u)\to-\infty$ for real $u\downarrow b$. Each such $u>b$ is **inside** convergence, where $F_A(u)\ge0$. This rules out the pole.

Hence $b<a$. For $\Re\rho>a$, $|2^\rho|>c>1$, so neither $c-2^\rho$ nor $K(\rho)$ vanishes. Such a zero would force a pole inside holomorphy. On $\Re\rho=a$ the only possible cancellations occur at $\rho=a+2\pi i n/\log 2$ for integers $n$; a single comparison need not see those zeros. Every point with real part $>1/2$, including each such boundary point, lies strictly above some $a_j$. Applying that comparison and then the functional equation for this real character gives condition 1. No rightmost zero was selected.

### From the critical line to each comparison

Under condition 1 use lines 73–91 of the one-scale criterion at the evidence revision. With $k=K(1/2)$, $r=\operatorname{ord}_{1/2}L$, and $z_\gamma=K(1/2+i\gamma)/k$, its constant in $W_m(X)/(\sqrt X\,k^m)$ is $-(1/2+r)$. Indeed squares are subtracted from the prime-power formula; their coefficient before subtraction is $\int_0^\infty h_m(2\log v)dv=k^m/2$ by $t=2\log v$ and convolution. The central residue is $-rk^m$ in units of $\sqrt X$. The pinned fixed-order remainder after normalization is $o_{\chi,m}(1)$ for real $X\to\infty$, including spline knots.

Applying that formula at $X$ and $2X$ yields

$$\frac{V_{j,m}(X)}{\sqrt X\,k^m}
=-(c-\sqrt2)(1/2+r)
-\sum_{\gamma\ne0}(c-2^{1/2+i\gamma})X^{i\gamma}z_\gamma^m+o_{\chi,j,m}(1).$$

Here $|z_\gamma|<1$ for $\gamma\ne0$ because the phase $e^{i\gamma t}$ is nonconstant on the box with positive density $e^{t/2}/k$. The inverse-square zero sum and $K(1/2+i\gamma)=O((1+|\gamma|)^{-1})$ give $\sum_{\gamma\ne0}|z_\gamma|^2<\infty$, counting multiplicities. For each fixed $j$, $c>\sqrt2$. By dominated convergence choose one integer $m\ge2$ with $(c+\sqrt2)\sum_{\gamma\ne0}|z_\gamma|^m<(c-\sqrt2)/4$. Only now take $X$ large enough to make the remainder smaller in modulus than $(c-\sqrt2)/4$. Thus $V_{j,m}(X)<0$ eventually, with neither an order uniform in $j$ nor a sign premise on $W_m$.

This repairs the real-abscissa step for the **dilated comparison**, not for the original one-scale sign. It does not independently establish the comparisons for any character.
