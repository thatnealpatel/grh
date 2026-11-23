# The critical radius for the signed zero test

The infimum of the leading coefficients in the [log-window filter](log-window-filter.md) is attained, up to a bounded additive term, **by a fixed multiplier**. Keep the hypotheses and notation of the [signed test](adjacent-zero-counts.md): $t=2q^{3/5}$, $X=(3\log(t/2))^2$, $D=\log X$, $u=\gamma-t$, and the global zeta strip $1/8\le\beta\le7/8$. Suppose $\Re S_X(t)\ge47/81-o(1)$. Fix $c>0$, $b_0=1/2+c/D$, and

$$0<\eta<m_c=47/81-225/12544-(211/224)\cosh(c)/3.$$

There are an entire $M$, independent of $q$, and a constant $K$ such that for all sufficiently large peaks the conclusions (1), (2), and the one-sided core projection of (7) of that test hold with

$$J=\frac{\log D}{2\pi}+K.$$

In particular the signed right-hand sum exceeds $\eta$ with the zero-residue minus sign, and some adjacent half-wavelength count difference in this window has modulus $\gg X^{1/8}/D$. The [bounded analytic absolute-tail obstruction](log-window-filter.md#obstruction-for-a-bounded-analytic-absolute-tail-certificate) gives the reverse inequality $J\ge(\log D)/(2\pi)-O(1)$ for its class of certificates. It does not bound what is possible with cancellation.

## Two frequencies and a narrowing contour

Let $h=\log(8/7)$, $d=3/4$, and set

$$M(s)=\cosh^2(hs)\exp\{\lambda(1-\cos(2\pi(s-d)))+\nu(1-\cos(\pi(s-d)))\},\qquad A(s)=M(s)/s^2.$$

First fix $\nu>0$ small, then $\lambda>0$ small. The critical frequency $2\pi$ has no decay on the two lines $1/2,1$, and grows too rapidly just outside them for the old parallel-line shift. The second frequency supplies room to move the contour beyond both lines by a distance that shrinks as $|u|$ grows. Write $f(u)=\operatorname{sech}(\pi u)$. In the closed region

$$1/2-2a f(u)\le\sigma\le1+2a f(u)\qquad(s=\sigma+iu)$$

we have $\cos(\pi(\sigma-d))\ge1/2$ and $\cos(2\pi(\sigma-d))\ge-4\pi a f(u)$ for small $a>0$. Since $f(u)\cosh(2\pi u)\le2\cosh(\pi u)$, choose fixed $a$ so small that $8\pi a\lambda\le\nu/4$ and the left boundary is above $1/4$. After removing $\cosh^2(hs)$, the multiplier has modulus at most

$$e^{\lambda+\nu}\exp\{-(\nu/4)\cosh(\pi u)\}. \tag{8}$$

In particular $A,A'$ have a uniform inverse-square envelope times $O_{\nu,\lambda}(\exp\{-(\nu/8)\cosh(\pi u)\})$ there. For the derivative, a fixed power of $e^{2\pi|u|}$ can be absorbed by weakening the damping. On the entire right zero strip $1/2\le\beta\le7/8$ there is the **additional** factor $\exp\{-\lambda\sin(2\pi(\beta-1/2))\cosh(2\pi u)\}$ in this last bound for $A,A'$: Here the critical cosine is nonnegative, and the second cosine alone supplies the damping in (8).

## The prime side at the boundary of convergence

Let $W(z)$ be the inverse Laplace integral of $A(s)$ on $\sigma=1$. For $W_0$ omit both exponential factors. Given $\epsilon>0$, the parameters can be fixed in the stated order so that

$$|W(z)-W_0(z)|\le\epsilon e^z(1+|z|)^{-3}. \tag{9}$$

Indeed on this line the $L^1(du)$ differences of the multipliers **including $1/s^2$**, and of their first three derivatives in $u$, can all be made arbitrarily small. For the $\nu$ perturbation alone, derivatives of its exponential are bounded uniformly as $\nu\downarrow0$, since $\cos(\pi(1-d))>0$ and each derivative costs a polynomial in $\nu\cosh(\pi u)$. Derivatives of the difference tend pointwise to zero and have, after the rational and hyperbolic factors are included, an integrable inverse-square majorant. For the $\lambda$ perturbation at fixed $\nu$, the critical exponential has modulus $e^\lambda$ on the line. Derivatives cost at most a fixed power of $1+e^{2\pi|u|}$ for $0<\lambda\le1$, absorbed by the fixed $\nu$ damping. Dominated convergence followed by inversion and three integrations by parts gives (9).

At $z=\log(X/n)$, Chebyshev's bound on each unit block of $z$ gives $X^{-1}\sum_{n\text{ in block}}\Lambda(n)e^z=O(1)$. Thus (9) costs $O(\epsilon)$ even with an extra $1+|z|$. For $W_0(z)=\mathbb E(z+Z)_+$, where $Z$ is the sum of two independent equiprobable $\pm h$, the prime replacement cost is $A_h+o(1)$, $A_h=225/12544$, as in the [original prime comparison](log-window-filter.md#filter-and-prime-comparison); its absolute mass with the extra $1+|z|$ is bounded by Chebyshev as well. Consequently the frozen prime-power observable $T_M(t)=X^{-1}\sum_n\Lambda(n)n^{-it}W(\log(X/n))$ has real part at least $47/81-A_h-O(\epsilon)-o(1)$ at a peak. Moreover $T_M(t-v)=e^{ivD}T_M(t)+O(|v|)$ uniformly: Use $|e^{iv\log n}-e^{ivD}|\le |vz|$.

## Explicit formula on the curved lines

In the inverse transform for each $n$, move the line at $1$ to $r(u)=1+a f(u)$ by (8). Integrals on curves use $ds$, including the derivative of the real part. There the Euler series is absolutely integrable against the kernel for each fixed $X$: $\sum\Lambda(n)n^{-r(u)}\ll_a f(u)^{-2}$ by comparison with $\sum(\log n)n^{-r(u)}$, and (8) beats this loss. This gives the usual integral of $-(\zeta'/\zeta)(s+it')X^{s-1}A(s)$ for $T_M(t')$, including at $t'=t-v$ with $0\le v\le 2\pi/D$.

Shift to $\alpha_l(u)=1/2-l f(u)$ for a suitable $l\in[a,2a]$. The integral on this curve is $o(1)$, uniformly in these $t'$. Here is the averaging detail needed since there is no fixed power saving over the full curve. Use the local log derivative expansion from the [strip contour](log-window-filter.md#explicit-formula-and-tail): At these left real parts it is a sum of inverse distances to the zeros within one unit of $t'+u$ as an absolute upper bound, plus $O(\log(2+|t'+u|))$. On the full slab the local log derivative expansion also has the pole term $-1/(s+it'-1)$, bounded on the left curves and on the distant horizontals used here. Average in $l$ and integrate over $j\le u\le j+1$, $j\in\mathbb Z$. In each local pole term changing from $l$ to $\sigma$ costs at most $C_a e^{\pi|j|}$. The resulting integral of $|\sigma+it'+iu-\rho|^{-1}$ on the rectangle of bounded sides is $O(1)$ per nearby zero by two-dimensional integrability. There are $O(\log(2+|t'+j|))$ such zeros. By (8), bounding $|ds/du|$ by a constant, the contribution of the block to the averaged absolute integral is at most

$$C X^{-a f_j}\frac{\log(2+|t'+j|)}{\sqrt X}\exp\{\pi |j|-c_1 e^{\pi |j|}\},\qquad f_j=\min_{[j,j+1]} f>0,$$

with fixed $c_1>0$. The logarithmic ratio is $O(1+\log(2+|j|))$ for these heights. Since $f_j\asymp e^{-\pi|j|}$, half the double-exponential decay together with $X^{-a f_j}$ gives $O(e^{-c_4\sqrt D})$ by the arithmetic-geometric mean inequality, uniformly in $j$; the remaining envelope is summable. Thus the averaged integral is $O(e^{-c_4\sqrt D})$. Choose $l$ off the countable set of curves passing through zeros, with the integral at most twice its averaged bound. On finite truncations take the usual separated upper and lower heights for $t'+\Im s$, where the log derivative is $O(\log^2(2+|t'+\Im s|))$ over the slab. Estimate (8) removes the horizontal integrals. The zeta pole is crossed, contributing $O(t^{-2})$ by (8) at $1-it'$. Neither trivial zeros nor the kernel pole are crossed. The resulting zero sum has the minus sign and is absolutely convergent on the crossed set for each fixed $X$.

The choice of curve does **not** require estimating height variations of its zero counts. All zeros with $\beta\ge1/2$ are crossed. Put $B_D=(\log D)/(4\pi)$. On $|u|\le B_D$, even with shifts $0\le v\le2\pi/D$, $a f(u+v)\gg_a D^{-1/4}>D^{-1/2}$ eventually. Every zero there with $\beta\ge1/2-D^{-1/2}$ is crossed for every choice of curve. Crossed zeros deeper to the left cost $O(e^{-\sqrt D}\log t/\sqrt X)$ by the inverse-square bound in (8). At $|u|>B_D$, the crossed zeros with $\beta\le b_0$ have total cost $o(1)$, by (8), $X^{\beta-1}\le e^c/\sqrt X$, and the unit zero count. We can therefore use exactly the fixed complementary set

$$U=\{|u|\le B_D,\quad 1/2-D^{-1/2}\le\beta\le b_0\}$$

besides **all** right zeros with $\beta>b_0$, up to a uniform $o(1)$. In particular, reflected pairs with $|\beta-1/2|\le c/D$ remain intact on the core of this complementary set.

## Recover the sharp radius and the projected test

Use either the point mass at zero or the two-box measure $\mu$ from [(5) of the signed test](adjacent-zero-counts.md), with $H=\pi/D$ and $\int e^{ivD}\,d\mu=1$. By (9) and the frozen variation estimate, averaging costs $O(H)$ on the prime side. On $U$, replacing the shifted amplitude $A(\beta+i(u+v))$ by $A(\beta+iu)$ costs a summed $O_c(H)$, using the derivative envelope throughout the short segment in the narrowing region. Leave the phase intact. Bound the unshifted amplitude using (8) by $e^{\lambda+\nu}|\cosh(hs)|^2/|s|^2$. Now the [positive test and pairing](adjacent-zero-counts.md#charge-all-but-the-right-hand-zeros-once) apply unchanged: Replace the last ratio by $\Re\Phi(s)$ to summable $O(D^{-1/2}/(1+u^2))$ error per amplitude, pair the central strip at fixed $u$, and charge any remaining left zeros at $X^{-1/2}$. Positivity on the whole strip gives a total absolute charge $\le e^{\lambda+\nu}(211/224)\cosh(c)/3+o(1)$. More explicitly, with $C$ the absolute prime comparison constant in (9), require $C\epsilon+(e^{\lambda+\nu}-1)I_h\cosh(c)/3<m_c-\eta$. First budget less than half this slack for each term, then decrease $\nu$ and, at fixed $\nu$, decrease $\lambda$ as above.

For the right-hand tail put $x=\beta-1/2$. On $0\le x\le3/8$, $\sin(2\pi x)\ge c_2 x$ for a fixed $c_2>0$. For instance $c_2=4\sqrt2/3$ works by concavity of the sine on this interval. After fixing $\lambda$, take $\lambda c_2 e^{2\pi K}/2>1$; then $\lambda c_2\cosh(2\pi w)\ge D$ whenever $|w|\ge J-2H$, eventually. Thus **pointwise at each layer** the critical factor cancels $X^x$. The secondary factor remains to pay for logarithms and differentiation. In particular, uniformly there,

$$X^{\beta-1/2}(|A(\beta+iw)|+|A'(\beta+iw)|)\ll (1+w^2)^{-1}\exp\{-c_3\cosh(\pi w)\}.$$

Since $\cosh(\pi(J-2H))\gg\sqrt D$, the tail of the averaged or unaveraged right sum at $|u|>J$ is $o(1)$ by the unit counts and $\log t/\sqrt X=O(1)$. This proves the asserted signed sum. The same estimate on the successive unit blocks gives the absolute-tail certificate (6) of the log-window note. This $M$ is bounded on the closed strip $[1/2,1]$ and nonzero at $d$, as required by its obstruction.

Finally apply the exact layer and adjacent-box identity (7) of the signed test **before truncation**, with $F_b(w)=X^{b-1+iw}A(b+iw)$. In its tail, $\partial_b F_b$ costs at most an additional $1+D$ in the last envelope, and the two-box normalization costs $1/H$; both are absorbed by $\exp(-c_3\cosh(\pi w))$. Thus for the core $dw$ integral $I$ in that identity, $-(D/4)\Im I>\eta$ eventually, retaining the strict slack above. In the core $A,A'$ have bounded inverse-square envelopes, so integrating $D X^{b-1}$ over $[b_0,7/8]$ still costs at most $X^{-1/8}$. This gives the same lower bound $\gg X^{1/8}/D$ on a count difference with $|w|\le J$. It matters that the excess power $X^x$ over the critical-line budget tends to one as $x\downarrow0$ for fixed $X$: The compensation is layer by layer, not the product of a worst power and a worst damping taken at different layers.

**Scope.** This attains the limiting localization scale for the absolute-tail certificate, not an upper bound for the individual core projection. Any further unbounded reduction of the radius in this class would need information absent from that certificate, such as cancellation in the outer sum. The original and critical filters need not have equal projections.
