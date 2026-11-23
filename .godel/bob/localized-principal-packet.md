# Localizing the zeta packet for the principal test

Let $y=q^{3/5}$, $X=((9/5)\log q)^2$, $D=\log X$, and $t=2y$. Use $S_X(t)=X^{-1}\sum_{p<X}(\log p)\log(X/p)p^{-it}$; conjugating the convention in the [sampling result](sampled-principal-peaks.md) preserves real parts and moduli. Assume the same [external $7/8$ strip for zeta](fixed-strip-endpoints.md#what-supplies-the-hypothesis) as in the [unsmoothed packet bound](endpoint-zero-packets.md). Define

$$ B_J(t;c)=\sum_{|\gamma-t|\le J,\ \beta>1/2+c/D}\frac{1}{1+(\gamma-t)^2} $$

on nontrivial zeros $\beta+i\gamma$, with multiplicities. If $\Re S_X(t)\ge47/81-o(1)$, then for each fixed $c>0$ with

$$ \cosh c<\frac{571343}{319032}=1.7908642\ldots,\qquad B_{C_c\log D}(t;c)\gg_c X^{1/8}. \tag{1} $$

Here $C_c$ is fixed before taking $q\to\infty$. This improves both the window $X^{3/8}D$ and the old range $\cosh c<47/27$. In particular a failure at $y$ incurs this cost, regardless of the smaller height. The reverse implication is not proved.

## A filter with a priced prime-side error

Put $r=8/7$, $h=\log r$, and let $V,W$ be independent equiprobable $\pm h$. Set $Z=V+W$, $m(s)=\mathbb E e^{sV}$. First average the cutoff as $\mathbb E[e^Z S_{Xe^Z}(t)]$. With $v=\log(X/p)$ its weight replaces $v_+$ by $\mathbb E(v+Z)_+\ge v_+$, leaving the normalization $1/X$ fixed. By PNT the total increase of the prime weights is $m(1)^2-1+o(1)$, using the original mass $1+o(1)$ at each of the three cutoffs. This bounds the *absolute difference of the sums*, not the sign of a trigonometric sum. Restoring prime powers costs $o(1)$.

For another fixed parameter $0<\epsilon<1/4$ multiply the Mellin kernel by $g(s)=\exp(1-\cos(\epsilon s))$. On the imaginary axis this is the Fourier transform of a real even signed kernel $k_\epsilon(w)=\epsilon^{-1} k(w/\epsilon)$ with integral one. Indeed $k$ is the inverse transform of $\exp(1-\cosh u)$, in the convention $\widehat k(u)=\int e^{-iuw}k(w)dw$. Shifting the inverse contour by $\pm i$ gives $|k(w)|\ll e^{-|w|}$ since $\cos(1)>0$. Hence its bilateral Laplace transform is $g(s)$ for $|\Re s|<1/\epsilon$, by analytic continuation. The replacement of $v_+$ by $k_\epsilon*v_+$ costs $O(\epsilon e^{-|v|/(2\epsilon)})$ pointwise: Subtract $v$ for $v>0$, using mass one and first moment zero, then integrate only the crossing tail. For $v\le0$ only the other crossing tail enters. At $Y=Xe^Z$ the total cost after summing against $\Lambda(n)/X$ is $O_h(\epsilon)$ with a constant independent of small $\epsilon$. Indeed for $n\le Y$ use $\sum_{n\le Y}\Lambda(n)\ll Y$; for $2^jY<n\le2^{j+1}Y$ sum $O(2^jY\,2^{-j/(2\epsilon)})$. No PNT in a short interval is needed.

The twice-modified sum has Perron integrand $-(\zeta'/\zeta)(s+it)X^{s-1}m(s)^2g(s)/s^2$ on $\Re s=2$ (Laplace inversion of the convolved ramp). Shift to $1/16$ as in the [strip contour](endpoint-zero-packets.md#price-the-part-near-the-critical-line). The new factors are bounded on the slab: $|m(s)|\le e^{2h}$ and $|g(s)|=\exp(1-\cos(\epsilon\Re s)\cosh(\epsilon\Im s))$. Thus the same separated horizontals and $o(1)$ vertical bound apply. The zeta pole costs $O_h(t^{-2})$. In the original sum we can consequently charge the prime-side cost $m(1)^2-1+O_h(\epsilon)+o(1)$ and the absolute modified zero residues

$$ X^{\beta-1}\frac{|m(\beta+iu)|^2 |g(\beta+iu)|}{\beta^2+u^2},\qquad u=\gamma-t. $$

Outside $J=2\epsilon^{-1}\log D$, $|g|\le\exp(1-\tfrac12\cos(\epsilon)D^2)$. The reflected strip $1/8\le\beta\le7/8$ and the inverse-square count $\sum_\rho(1+u^2)^{-1}\ll\log(2+t)$ make this entire tail $o(1)$. Inside $J$, off-line pairs with $|\beta-1/2|>c/D$ cost $O_h(X^{-1/8}B_J)$ by reflection at the same ordinate. It remains to price the other local zeros with their leading constant.

## The measure relevant to the filter

Argue by contradiction along a sequence with $B_J=o(X^{1/8})$. Call zeros inside $J$ with $|\beta-1/2|\le c/D$ good, and divide their ordinate counting measure in $u$ by $\log t$, obtaining $\mu_q$. We claim $\mu_q\to du/(2\pi)$ against continuous kernels bounded by $C/(1+u^2)$.

For every fixed $a>1/2$ and $v\in\mathbb R$, apply the completed Hadamard identity in the [packet note](endpoint-zero-packets.md#price-the-part-near-the-critical-line) at $\sigma+i(t+v)$, $\sigma=1/2+a$. The sum over all zeros of $(\sigma-\beta)/((\sigma-\beta)^2+(u-v)^2)$ equals $\tfrac12\log t+O_{a,v}(1)$ by Stirling and the absolutely convergent Euler product. Omitting the bad local pairs costs $O_{a,v}(B_J)=o(\log t)$. Omitting the outer tail costs $O_{a,v}((\log(2+t)+\log(2+J))/J)=o(\log t)$ by the unit counts in the packet note. On good zeros replace $\sigma-\beta$ by $a$ at cost $O_{a,v,c}(D^{-1}/(1+u^2))$ per kernel. Therefore $\int a/(a^2+(u-v)^2)\,d\mu_q\to1/2$.

The unit counts give vague subsequential compactness and translation-bounded limits (on any fixed unit interval the limiting count bound after normalization is absolute). The same tail bound outside $R$ divided by $\log t$ is $O(1/R)$ in the limsup. Thus every vague limit has the displayed Poisson integral equal to $1/2$ for all $a>1/2$ and all $v$. For each $v$ it is holomorphic in $a$ on $\Re a>0$ by domination on compact subsets, so the identity holds for every real $a>0$. Dividing by $\pi$ gives the Poisson approximate identity: Testing against compactly supported continuous functions and sending $a\downarrow0$ identifies the limit as $du/(2\pi)$ (outside an enlarged support the convolved test is $O(a/(1+u^2))$). Uniqueness and the tail bound prove the claim. This argument needs $J\to\infty$, not a rate of convergence of the measures.

On good zeros use $|g|\le G_\epsilon=\exp(1-\cos\epsilon)$. Replacing $|m(\beta+iu)|^2/(\beta^2+u^2)$ by $K(u)=|m(1/2+iu)|^2/(1/4+u^2)$ costs an *additive* $O_{h,c}(D^{-1}/(1+u^2))$, by bounded support of $V$. Leave $X^{\beta-1}$ untouched and sum reflected pairs, whose numerators average to at most $X^{-1/2}\cosh c$, also valid for each line zero. The good charge is at most $G_\epsilon\cosh(c)(\log t)/\sqrt X\int K\,d\mu_q+o(1)$. Using $\int e^{iuz}(1/4+u^2)^{-1}du=2\pi e^{-|z|/2}$, the limiting integral is

$$ \frac1{2\pi}\int K(u)du=\mathbb E\exp((V+W-|V-W|)/2)=\frac{3/r+r}{4}=\frac{211}{224}. $$

The prime mass increase is $m(1)^2-1=225/12544$, and $\log t/\sqrt X\to1/3$. Thus along any such small-packet sequence the limsup of $|S_X(t)|$ is at most

$$ \frac{225}{12544}+O_h(\epsilon)+G_\epsilon\frac{211}{224}\frac{\cosh c}{3}. $$

The limit of this upper price as $\epsilon\downarrow0$ is strictly below $47/81$ precisely in the range of (1). Fix $\epsilon=\epsilon(c)$ small enough to retain a strict gap **before** choosing a putative small-packet sequence. If there were no eventual positive lower multiple of $X^{1/8}$ along the principal peaks, one could extract just such a sequence, a contradiction. This proves (1), not a uniform exclusion of peaks.

The same proof works for a fixed modulus threshold $s$ at $t=2y$ or $6y$ if $225/12544+(211/224)\cosh(c)/3<s$. Thus the [two-harmonic alternative](sampled-principal-peaks.md#if-the-first-harmonic-barely-passes-price-the-third) also admits the shorter window. The immediate arithmetic test, without either product mean, is now a bound for the local packet (1), for example at $c=1$; even $o(X^{1/8})$ only on a sequence of putative failures would rule that sequence out. Neither the strip nor the Poisson limit used under the small-packet assumption supplies this missing bound.

**After Work.** The [exceptional-base replay](exceptional-base-review.md) found no need for a new family sieve. A separate [three-ordinate certificate](three-ordinate-endpoint.md) reduces the single-witness test at $A=3/2$; it does not price the signed local residues here at $A=9/5$. That remains the individual test.
