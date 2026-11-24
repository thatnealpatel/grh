---
evidence_revision: 78373235736b7eb16ce70384763b67bdce8cc9d8
outcome: established
---

# Eventual local prime spline signs for fixed real characters

Fix any primitive nonprincipal real Dirichlet character
$\chi$ with $L(u,\chi)\ne 0$ for every real $1/2<u\le 1$.
Set $h=\mathbf{1}_{[0,\log 2]}$ and $h_m=h^{*m}$ using
ordinary convolution on $\mathbb R$, for integers $m\ge2$.
For real $X\ge1$ let

$$W_m(X)=\sum_p\chi(p)\log p\,h_m(\log(p/X)).$$

**Proposition to test:** Every nontrivial zero of
$L(s,\chi)$ has real part $1/2$ if and only if there exist
an integer $m\ge2$ and a real $X_0\ge1$ such that
$W_m(X)\le0$ for every real $X\ge X_0$. The order may
depend on $\chi$, not on $X$. The weight uses only genuine
primes in the fixed-ratio interval $[X,2^mX]$ once $m$
is chosen. No uniform or effective choice is requested.

**Source and payoff:** The pinned [mod-four tent proof](../closed/mod-four-prime-tent-eventual-sign.md)
uses a two-box convolution of width $\log 4$ and a
conductor-specific absolute residue budget. Bob's
[endpoint equation (1)](../../bob/fixed-strip-endpoints.md#the-product-mean-at-the-original-endpoint-weight)
at `bbca37033019090f6f40e6223b5054d382c9d789` uses the
unnormalized log ramp, before division by the cutoff, at
$v=0$ for an individual real quadratic character. Neither
landing asserts this extension. It asks whether increased
smoothing order replaces the small residue budget while
retaining a fixed-ratio comparison of actual primes.

**Discriminating test:** Derive the multiplier $K(s)^m$,
where $K(s)=(2^s-1)/s$, and an explicit formula with a
uniform-in-$X$ remainder for each fixed $m$, including
both parities, trivial zeros, and boundary terms. Remove
prime powers, checking the sign and normalization of the
square term and the exclusions at primes dividing the
conductor. On the critical-line hypothesis test strict
contraction of $|K(1/2+it)|/K(1/2)$ for every $t\ne0$
and summable domination over zeros as $m$ grows. Keep any
central zero with its multiplicity and actual sign. In
the converse for a single order, transform the eventual
nonnegative tail of $-W_m$, isolate entire endpoint
terms, and check real regularity and noncancellation of
zero poles before applying Landau and reflection. Test
precisely where real-axis nonvanishing is needed.

## Adjudication

**The equivalence holds.** The square bias and a central zero both favor strict negativity. For each fixed character the other zeros contract relative to that bias as the box order increases. This replaces the numerical budget at lines 69–90 of the mod-four proof. It does not infer a sign from Bob's magnitude estimate (1).

### Explicit formula at a real translate

Write $d=\log 2$, $q=\operatorname{cond}(\chi)$, $a=(1-\chi(-1))/2$, and $Y=L'/L$. Convolution gives

$$\int h_m(t)e^{st}\,dt=K(s)^m,\qquad K(s)=\int_0^d e^{st}\,dt=(2^s-1)/s,\quad K(0)=d.$$

For $m\ge2$ the weight is continuous, piecewise polynomial, and zero at the endpoints of its support $[0,md]$. Inverting the transform on $\Re s=2$ gives $h_m(t)$ even at the knots, since the transform there is integrable. Summing at $t=\log(n/X)$ against $\Lambda(n)\chi(n)$ is absolutely justified by the Euler product. The result is the integral of $-Y(s)X^sK(s)^m\,ds/(2\pi i)$ upwards on that line.

Shift to $\Re s=-1/2$. Here are details for the decay and the residues. Use the standard entire order-one completion $B(s)=(q/\pi)^{(s+a)/2}\Gamma((s+a)/2)L(s,\chi)$ and its functional equation. On the new line, reflection to $\Re s=3/2$, absolute Euler convergence there, and the gamma logarithmic derivative give $Y(-1/2+it)=O_\chi(\log(3+|t|))$. Neither gamma argument meets a pole there. In the strip of the shift, $K(s)^m\ll_m(1+|\Im s|)^{-m}$.

For the horizontal edges, let $\rho=\beta+i\gamma$ run over the zeros of $B$ with multiplicity. They have $0\le\beta\le1$, and $B(0)\ne0$ by reflection at $1$. Its order-one product gives $\sum_\rho |\rho|^{-2}<\infty$. At $2+it$ the real logarithmic derivative of the product gives

$$\sum_\rho (1+|t-\gamma|^2)^{-1}\ll_\chi\log(3+|t|).$$

Indeed $\Re(2+it-\rho)^{-1}$ majorizes a constant times each summand, $\sum_\rho\Re(1/\rho)$ converges absolutely, and $B'/B$ there is $O_\chi(\log(3+|t|))$. Thus there are $O_\chi(\log j)$ ordinates in $[j-1,j+2]$ for large $j$. Remove intervals of sufficiently small radius $c_\chi/\log j$ about each to choose $T_j\in[j,j+1]$ outside them. On this edge subtract $B'/B(2+iT_j)$ from $B'/B(\sigma+iT_j)$ in the product: The zeros within unit ordinate distance contribute $O_\chi(\log^2 j)$ by separation, and the remaining differences are bounded by the displayed sum times an absolute constant. Subtracting the gamma terms gives the same $O_\chi(\log^2 j)$ bound for $Y$ throughout the edge; conjugation covers $-T_j$. The horizontal integrals vanish at each fixed $X$. On the infinite new vertical the absolute integral is $O_{\chi,m}(X^{-1/2})$ with a constant independent of $X\ge1$.

The gamma factor has one pole in the strip if $a=0$, at zero, and none if $a=1$. Since $B(0)\ne0$, this accounts for a simple trivial zero of even $L$; all other trivial zeros lie to the left. The kernel is entire, and $L$ has no principal pole. The resulting identity is

$$\sum_n\Lambda(n)\chi(n)h_m(\log(n/X))
 =-\sum_\rho X^\rho K(\rho)^m-\mathbf1_{a=0}d^m+O_{\chi,m}(X^{-1/2}).$$

The zero sum converges absolutely at fixed $X$ by the inverse-square sum. No endpoint half weights or kernel residues enter.

### From prime powers to the sign

Put $T=\sqrt X$ and $k=K(1/2)=2(\sqrt2-1)$. The squares have character value one away from $p\mid q$ and zero there. By PNT, $\vartheta_q(u)=\sum_{p\le u,\ p\nmid q}\log p=u+o(u)$; the omissions cost at most $\log q$. Partial summation with $f_m(v)=h_m(2\log v)$ gives a square contribution of $T J_m+o_{\chi,m}(T)$, where $J_m=\int_0^\infty f_m(v)\,dv$. Indeed $f_m$ has bounded variation and is supported on $[1,2^{m/2}]$, on which $\sup_v|\vartheta_q(Tv)-Tv|=o_m(T)$ for fixed $q,m$ and real $T\to\infty$. To check the coefficient directly, $J_1=\sqrt2-1$; in the convolution with the next box, set $v=e^{t/2}w$ for box variable $0\le t\le d$. This gives $J_{m+1}=kJ_m$, hence $J_m=k^m/2$. Exponents $j\ge3$ cost in total $O_m(X^{1/3}\log^2(2X))$: A contributing base is at most $(2^mX)^{1/3}$, there are $O_m(\log(2X))$ possible exponents, and $h_m$ is bounded. Subtract these powers, including the **positive** square term, to isolate the genuine primes.

Assume now that every nontrivial zero is on the line, and put $r=\operatorname{ord}_{1/2} L$. For $z_\gamma=K(1/2+i\gamma)/k$ we obtain

$$\frac{W_m(X)}{\sqrt X\,k^m}
 =-\tfrac12-r-\sum_{\gamma\ne0}X^{i\gamma}z_\gamma^m+o_{\chi,m}(1).$$

In particular a central zero contributes with its multiplicity, not as an oscillatory error. Let $d\mu(t)=e^{t/2}dt/k$ on $[0,d]$. Then

$$1-|z_\gamma|^2=\iint(1-\cos(\gamma(t-u)))\,d\mu(t)d\mu(u)>0\qquad(\gamma\ne0),$$

since the cosine differs from one on an open set of positive measure. This is the strict triangle inequality needed even for very small nonzero ordinates. Also $|z_\gamma|\le(\sqrt2+1)/(k|1/2+i\gamma|)$, so the squares are summable. Dominated convergence for counting measure with multiplicities gives $\sum_{\gamma\ne0}|z_\gamma|^m\to0$. This bounds the absolute oscillation for *all* real $X$, irrespective of phase alignment. Choose $m$ to make the sum less than $1/4$, then take $X$ large for this one order. The resulting sign is strictly negative. No estimate for the explicit-formula or PNT error with growing $m$ is used.

### From one fixed-order sign to zero location

Conversely, suppose $-W_m(X)\ge0$ for $X\ge A\ge1$ for a single $m\ge2$. Extend the prime sum by its definition to $X>0$; it is locally bounded and zero on $(0,2^{1-m})$. The transform of each weight against $X^{-s-1}dX$ on $(0,\infty)$ is $p^{-s}K(s)^m$, by the substitution $t=\log(p/X)$. For $\Re s>1$ absolute convergence and the Euler product therefore give

$$F_A(s)=\int_A^\infty[-W_m(X)]X^{-s-1}dX
 =K(s)^m\left(Y(s)+\sum_p\sum_{j\ge2}\chi(p)^j\log p\,p^{-js}\right)
 +\int_0^A W_m(X)X^{-s-1}dX.$$

The last term is entire by support away from zero. The prime-power correction converges normally on $\Re s>1/2$ by comparison with $\sum_p(\log p)p^{-2\sigma}/(1-2^{-\sigma})$ on each $\Re s\ge\sigma>1/2$. Thus a zero $\rho$ in the open half-plane leaves a pole of residue $\operatorname{ord}_\rho(L) K(\rho)^m$: It is nonzero because $2^s=1$ requires $\Re s=0$.

The continuation is regular at every real $s>1/2$ by the real-axis premise and the Euler product. If the integral had abscissa $b>1/2$, take a disk of regularity about $b$ and a real center $c>b$ close enough that the Taylor series there reaches a real point $b-\epsilon$ in the disk. In powers of $c-s$ its coefficients are the nonnegative log moments of the tail at $c$, divided by factorials; differentiation is justified by convergence strictly to the left of $c$. Summing them at $b-\epsilon$ and using monotone convergence gives a finite integral there, contrary to the abscissa. Hence the tail defines a holomorphic function on $\Re s>1/2$, excluding the zero poles by uniqueness of continuation. Reflection excludes nontrivial zeros on the other side.

Without the real-axis premise, a real zero $\beta>1/2$ could supply precisely the singularity Landau requires at the abscissa. Its residue is positive since $K(\beta)>0$. This is a limitation of that converse, not a character counterexample. Equivalently, without a standing premise, the line assertion is equivalent to the **conjunction** of the real-axis nonvanishing and the eventual sign for some fixed order. This proves neither condition unconditionally. There is no conductor-uniform order or threshold asserted, and no change to the fixed-strip comparison.
