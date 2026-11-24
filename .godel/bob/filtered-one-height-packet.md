# A three-cutoff signed packet at depth 1.20, at the first height alone

At a [real high-endpoint failure](sampled-principal-peaks.md#if-the-first-harmonic-barely-passes-price-the-third) let $R=(9/5)\log q$, $V=R^2$, $D=\log V$, and $t=2q^{3/5}$. The following test stays at $t$. It changes the prime weight, not the value of the [original screen](uncut-census-window.md). Use $c=1.20$, $l=.02$, $h=.15$, $s_0=.5001$, and $\delta=.001$. For a zero put $b=\beta-1/2$, $x=\gamma-t$, $w=\beta+ix$. Define

$$Q(w)=V^{w-1}e^{lw}\cosh^2(hw)\,g(w)/w^2,\qquad g(w)=\exp(1-\cos(\epsilon w)),\qquad G=\exp(1-\cos\epsilon),$$
$$E(z)=4s_0^2 e^{l/2}\frac{\cosh h+\delta+\cos(2hz)}{2(s_0^2+z^2)}.$$

For fixed sufficiently small $\epsilon>0$, every sufficiently large failure requires the following **net** charge, with multiplicities:

$$ \sum_{\substack{b>1.20/D\\1.5/D<|x|\le(2/\epsilon)\log D}}
\left[-\Re Q(w)-\frac{G\cosh(1.20)}{R}\Re E(x+ib)\right] > .0018. \tag{1} $$

In particular the right-hand packet is nonempty. No $7/8$ strip, small-packet assumption, or limiting distribution of shallow ordinates is needed. The earlier [filtered ramp](localized-principal-packet.md) takes an absolute prime perturbation price and uses an ordinate limit conditional on a small packet. The [all-dilations ceiling](dilated-harmonic-ceiling.md) precludes paying even depth $1.175$ from the angular mean by taking the best *individually priced* ramp. Here three ramps are combined **before** taking their zero-side modulus. We certify their smaller joint envelope by a function with nonnegative real part throughout the zero strip, not just by its integral on the line.

## Pay for the combined weight on the original failure datum

Put $z=\log(V/p)$, $u=|\cos((t/2)\log p)|$, and $d\mu=V^{-1}\sum_p (\log p)\delta_{\log(V/p)}$. Let $H_1,H_2$ be independent equiprobable $\pm h$, $L=l+H_1+H_2$, and $f(z)=\mathbb E(z+L)_+$. The prime sum tested is $P_q=\int f(z)(2u^2-1)d\mu$. Failure forces $\int z_+ u\,d\mu\ge8/9-o(1)$; it does not force the same mean after changing the cutoff. Cauchy-Schwarz with $f$ gives

$$ P_q\ge P-o(1),\qquad P=\frac{2(8/9)^2}{\mathcal L}-e^l\cosh^2 h,\qquad \mathcal L=\int_0^\infty \frac{z^2}{f(z)}e^{-z}dz.$$

Indeed $f>0$ for $z\ge0$, and PNT gives the denominator limit and the mass limit $\int f e^{-z}dz=\mathbb E e^L$. Both fixed weights grow at most linearly at $+\infty$, where Chebyshev and partial summation give a uniform $O((1+B)e^{-B})$ tail beyond $B$. PNT is not applied to $u$. On $0\le z\le2h-l$, $f(z)=3(z+l+2h/3)/4$; above that knot it is $z+l$. This gives $P>.57285$.

Use the [even Mellin tent identity](opposite-phase-bands.md#use-the-unused-half-of-the-log-axis) at each cutoff $V e^L$, always at $t$. Multiply its normalized sum by $e^L$ to keep the denominator $V$, then average. The positive Mellin endpoints combine as $\mathbb E e^{Lw}=e^{lw}\cosh^2(hw)$. In particular the real coefficient is summed *before* absolute values are taken. The result is

$$ P_q=-\Re\sum_{\beta\ge1/4} Q(\beta+ix)+O(\epsilon)+o_\epsilon(1). \tag{2} $$

For clarity, the three unsmoothed tents at $\log n\ge0$ are precisely $(\log(V/n)+L)_+$. The signed convolution price from the linked proof is uniform up to fixed factors $e^L$, since all three tents are 1-Lipschitz and have upper support $D+L$. Prime powers are $o(1)$. In the contour shift the two lower numerator terms of each bilateral tent cost $O(\log t/V)$ on $\beta\ge1/4$, and on $\beta<1/4$ one uses the *whole* tent at cost $O(D^2 V^{-3/4}\log t)$. Both are $o(1)$, as are the pole and the integral on $\Re w=-1/4$. No lower endpoint of the tent was omitted near $w=0$.

## A positive budget on the full strip

On the real axis the shallow residue envelope before $g$ and $V^{\beta-1}$, evaluated at $\beta=1/2$, is exactly

$$ K(x)= e^{l/2}\frac{\cosh h+\cos(2hx)}{2(1/4+x^2)}\le E(x). $$

This uses $|\cosh(h(1/2+ix))|^2=(\cosh h+\cos(2hx))/2$ and $s_0>1/2$. Positivity of $K$ on the line is **not** sufficient for using the full zero budget. In fact $\Re E(x+ib)\ge0$ for $|b|\le1/2$. After removing positive factors, the sign is that of

$$ \cosh h+\delta+\cos(2hx)\cosh(2hb)-\frac{2xb}{s_0^2+x^2-b^2}\sin(2hx)\sinh(2hb). $$

The coefficient of the sine before $\sinh(2hb)$ has modulus at most $1/|x|$ for $x\ne0$. For $|x|\le4$ the cosine is nonnegative and the sine term costs at most $2h\sinh h<1$, also at $x=0$. For $|x|\ge4$, the trigonometric combination has modulus at most $\sqrt{\cosh^2 h+\sinh^2(h)/16}\le\cosh h+\sinh^2(h)/32<\cosh h+\delta$. Thus there are no negative unmeasured contributions.

The translated full Weil formula gives

$$ R^{-1}\sum_\rho\Re E(x+ib)= I/3+o(1),\qquad I=\frac1{2\pi}\int E(x)dx=s_0 e^{l/2}(\cosh h+\delta+e^{-2hs_0})<.94608.$$

Indeed $E$ is holomorphic with inverse-square decay on a fixed strip strictly wider than $|\Im z|\le1/2$. Its Fourier transform is a fixed linear combination of $e^{-s_0|\xi|}$ and its translates by $\pm2h$, by the Poisson transform. Consequently the full prime sum is $O_{s_0,h}(\sum_n\Lambda(n)n^{-1/2-s_0})=O(1)$ independently of $t$. The two pole terms at the translated arguments are $O(t^{-2})$. In the [translated gamma integral](verified-height-principal-band.md#translated-formula-with-a-finite-error) one may replace the symbol by $\log t$ at cost $O(1)$ by Stirling: The difference is $O(1+\log(2+|x|))$ against the inverse-square envelope. Now $\log t/R\to1/3$. Real parts are invariant under $b\mapsto-b$ for this real even kernel. The fixed displacement $s_0-1/2$ matters for absolute Euler convergence.

## Spend this budget only on the discarded terms

For $|b|\le D^{-1/2}$ the envelope $|e^{lw}\cosh^2(hw)/w^2|$ differs from $K(x)$ by $O(D^{-1/2}/(1+x^2))$, uniformly in $x$, by differentiating at widths bounded away from zero. Likewise $E(x)=\Re E(x+ib)+O(D^{-1/2}/(1+x^2))$ there for large $D$. At $|b|\le c/D$ average $V^{\beta-1}$ over the reflected pair at the same $x$ before bounding: The factor per zero is at most $\cosh(c)/R$, also on the line. Hence the shallow part in (2) costs at most $(G\cosh(c)/R)\sum_{\rm shallow}\Re E(x+ib)+o(1)$. The errors sum since $\sum_\rho(1+x^2)^{-1}=O(R)$ by the exterior trace at $2+it$.

On $-D^{-1/2}\le b<-c/D$ use the same bound per left member (its individual factor is at most $e^{-c}/R$). On $b<-D^{-1/2}$ with $\beta\ge1/4$ the envelope is $O((1+x^2)^{-1})$ and the depth factor is at most $e^{-\sqrt D}/R$, so their entire cost is $o(1)$. The remaining right zeros outside $J=(2/\epsilon)\log D$ cost $o(1)$ by $|g|\le \exp(1-D^2/4)$ there, $V^{\beta-1}\le1$, and the same inverse-square count. These estimates allow the shallow and left budgets to be replaced by the *full* budget **minus** the contributions of the local deep right zeros, since every term in the budget is nonnegative. Combining with (2) yields the lower margin $P-G I\cosh(c)/3-O(\epsilon)-o_\epsilon(1)$ on the net local right charge. For $|x|D\le1.5$ the phase of $Q(w)$ is $Dx+O(1/D)$ for $\beta\ge1/2$: The other factors have bounded argument derivatives near $x=0$, uniformly at these widths, and are positive real at zero. Thus $-\Re Q(w)\le0$ there eventually, and removing the center preserves the lower bound even after the budget subtraction.

The [scalar checker](check-filtered-packet.py) verifies $P-I\cosh(1.20)/3>.00184$, the strip positivity constants, and the individual prices. Fix $\epsilon$ small enough first to retain (1), then take $D$ large. This is not an effective finite conductor threshold. Replay with `sage -python .godel/bob/check-filtered-packet.py`.

**How much of the gain is real?** The prime lower bound is sharp for this filter in the angular-mean relaxation. Take $u=(8/9)z_+/(\mathcal L f(z))$ where $f>0$ and zero elsewhere. This is admissible since $f(z)\ge z_+$ and $(8/9)/\mathcal L<.91$; substitution gives mean $8/9$ and price exactly $P$. Even the uninflated real-axis envelope $K$ has $I_0=\int K/(2\pi)=e^{l/2}(e^h+3e^{-h})/4$, and $3P<I_0\cosh(1.205)$ by the checker. Thus lowering strip inflation alone cannot take *this* filter and absolute shallow price to $1.205$. This comparison law is not a prime or zero realization.

**Decision.** At a remaining candidate one can test (1) at $2q^{3/5}$ instead of testing both heights for a shallower packet. Use the combined signed envelope and its pole budget, not the sum of three separately priced obstructions. A uniform upper bound $.0018$ for this statistic would exclude the endpoint failure; nothing here estimates it on an exceptional conductor. In particular it is not an improved upper bound on $Z$. The finite Euler calibration concentrated at scaled depth 40 is not excluded simply by requiring depth $1.20$.

**After Work:** The [reflected price](filtered-reflection-price.md) uses the same census but keeps the signed left companion and subtracts both copies of the budget. Use its stricter statistic $S_*$ for the upper-bound experiment. On the all-deep model the new statistic tracks the actual combined prime price minus its full budget; this calibration does not exclude a failure.
