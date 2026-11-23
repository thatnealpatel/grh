# A dyadic test using differences of adjacent tuple counts

A common-dip failure lasts for a whole short window, though its large shifts may change with height. This gives a test of the **same frozen tuple counts for every center in a dyadic block**. It does not prove that those counts pass the test.

Use the untwisted whole-band sums of the [dyadic moment note](dyadic-prime-pair-moments.md). Freeze at $X=(3\log(U/2))^2$, $D=\log X$, take $1\le d\le5D$, fix $0<a<1/16$, $\gamma>0$, and put $h=\lceil(2+\gamma)\log U/D\rceil$. At fixed $d$ let $\mu=(\sum_p w_p\delta_{\lambda_p})^{*h}$ be the positive measure of one-sided tuple sums, of mass $A_d^h$. Put $\delta=2/U$, $m_\ell(x)=\mu([x,x+\ell))$, $T_\ell(v)=(1-|v|/\ell)_+$, and $B_\ell=\iint T_\ell(y-z)\,d\mu(y)d\mu(z)$. Define

$$Q_d=\frac{1}{2\delta}\int_{\mathbb R}|m_\delta(x)-m_\delta(x+\delta)|^2\,dx. $$

**Necessary cost.** If any $t\in[U,2U]$ fails the fixed-radius test at level $\varepsilon$ (at least $\varepsilon D(t)$ large moving real sums at every height in $F=[t-bX(t)/D(t),t+bX(t)/D(t)]$), then on $\gg_\varepsilon D$ distinct shifts,

$$ Q_d\gg_{b,\varepsilon}\frac{X}{D}\frac{a^{2h}}{U}. \tag{1} $$

Consequently it suffices, for one fixed $a,\gamma$ as above and **each** fixed $\eta>0$, to show that only $o_\eta(D)$ shifts exceed $\eta(X/D)a^{2h}/U$ along the dyadic blocks. There is no conductor parameter in this sufficient estimate. It could be stronger than needed: Large $Q_d$ need not come from the same window, or even from the block.

**Identity.** Write $\operatorname{sinc} v=\sin(v)/v$ and use the angular transform $\int K(u)e^{iu\nu}\,du$. The nonnegative kernel

$$K(u)=\frac{\operatorname{sinc}^2(u/U)-\operatorname{sinc}^2(2u/U)}{U}=\frac{\sin^4(u/U)}{U(u/U)^2}$$

has transform $(\pi/2)(2T_\delta-T_{2\delta})$. It vanishes at height zero and is $\gg1/U$ on $[U-o(U),2U+o(U)]$. For ordered pairs of atoms the overlap of their two length-$\ell$ cells of possible starts has length $\ell T_\ell(y-z)$, so $\int m_\ell^2=\ell B_\ell$. Expand $m_{2\delta}(x)=m_\delta(x)+m_\delta(x+\delta)$ to get

$$\frac2\pi\int K(u)|Z_d(u)|^{2h}\,du=2B_\delta-B_{2\delta}=Q_d.$$

On $F$, freezing at $U$ costs $O(D^2/\sqrt X)=o(1)$ per shift, as in the dyadic note. Thus the fractions of $F$ with $|Z_d|>a$ sum to at least $\varepsilon D/2$ eventually. Those shifts with fraction less than $\varepsilon/20$ account for at most $\varepsilon D/4$; each other fraction is at most one. Integrate on these latter shifts and use $|F|\asymp bX/D$ to obtain (1). This does not raise a freezing error to the power $2h$, or lose a factor $1/h$ by persisting from one point. The same window argument improves the threshold for the original translated nonnegative kernel on its common-dip branch; it does not improve the general single-spike implication there.

**What still needs pricing.** The pair multiplier $2T_\delta-T_{2\delta}$ is negative for $2\delta/3<|\nu|<2\delta$. Its zero-frequency part costs $\le U^{-1-\gamma/2+o(1)}$ by the permutation diagonal, negligible against (1). All nonzero supported differences still require at least $(\log U-O(1))/(2D)$ unmatched starts per side by rational spacing. But cells of length $\delta/2$ covering the one-sided span $O(hD/X)$ already give $B_\delta\gg XA_d^{2h}/(UhD)$ by Cauchy. This exceeds (1)'s scale by $\gg(A_d/a)^{2h}/h$ on the $\gg D$ genuine shifts with $A_d>1/4$. Do not bound the two neighboring counts separately. At the literal outer endpoints, each layer of width $2\delta$ contains only the repeated extreme start, since successive individual frequencies are at least $d/X^2$ apart. Its squared mass is at most $(8D^2/X)^{2h}$. This does not price edges of internal clusters.

The kernel also sees distant ordinates. For fixed $0<\sigma<2/3$, the total contribution at $|u|\le U^{2/3-\sigma}$ is $O(U^{-1-3\sigma+o(1)})$ using $K\le u^2/U^3$ and $A_d^{2h}\le U^{o(1)}$ by the two-form bound. For $|u|\ge U^{2+\sigma}$ it is $O(U^{-1-\sigma+o(1)})$ using $K\le U/u^2$. Both are negligible; the intervening range outside $F$ has not been priced at (1).

**Why not concentrate the kernel on $F$ instead?** A nonnegative probability density of angular bandwidth $\Omega$ has supremum at most $\Omega/\pi$ by Fourier inversion, since $|\widehat K|\le1$. Bandwidth $O(1/U)$ puts at most $O(X/(DU))$ of its mass in $F$. Conversely, if $\int_F K\ge3/4$, then $|e^{-it\nu}\widehat K(\nu)-1|\le b(X(t)/D(t))|\nu|+1/2$. On each mass-rich shift there are $\gg X/D^2$ positive-weight starts by the weight cap, hence two distinct starts within $O(D^2)$. They give $0<|\lambda_p-\lambda_r|\ll D^3/X^2$ by differentiation. Padding the two sides with identical starts, this **one replacement** has $|\widehat K|\ge1/2-o(1)$. A genuinely short nonnegative test cannot filter out all short replacements; this does not say they supply enough weight or have a particular sign.

**Next experiment.** At one frozen block, seek an estimate for the *difference* of the adjacent counts at their actual scale $2/U$, summed in square before taking an upper bound. Any approximation by a smooth tuple density must also price the squared difference of its residual at (1), including internal cluster boundaries. Failure of this stronger dyadic test would return us to the translated test at named centers, not disprove the common dip. See the [decision and failed alternatives](tuple-window-review.md).
