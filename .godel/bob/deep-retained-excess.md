# The signed excess after charging for depth

Use the [original two-band Weil test](weil-phase-bands.md), at its moving $t=2q^{3/5}$, $R=(9/5)\log q$, $V=R^2$, and $D=\log V$. Write $H$ for its retained signed charge. This note gives a smaller sufficient upper-bound problem and an almost-all bound for actual zeta zeros. Neither is a uniform exclusion.

For a reflected pair put $p=k(\sigma-\beta)+k(\sigma-1+\beta)$ at $\sigma=1+1/D$, with $k(d)=d/(d^2+x^2)$. For fixed $C\ge1$ set $a_C=2(\cosh C-1)$, and define

$$ E_C=\frac1R\sum_{\substack{\text{retained right members}\\c>C}}\big[-\Re Z^2-a_C p\big]. $$

Use **both** exact phase bands in $1.5/D<|x|\le J$, original complex smoothing, and one summand per same-ordinate pair. Even a favorable pair can contribute negatively to $E_C$.

**Upper bound.** At every prescribed height, $H\le (\cosh C-1)/3+E_C+o(1)$. In particular, $E_1\le0.0519$ uniformly would suffice for $H\le0.233$ eventually. At an actual large real high-endpoint failure there is the stronger necessity

$$ E_C\ \ge\ \frac{47}{81}-\frac{\cosh C}{3}-O(\epsilon)-o(1). \tag{1} $$

For example, $E_1>0.0658$ and $E_{1.15}>0.001$ for sufficiently small fixed $\epsilon$ and sufficiently large failures. These are different tests of the same failure; their margins do not add.

Indeed, on $c\le C$, $|r(x-ib)|^2\le\exp(1-\cos(\epsilon C/D))=1+O_C(D^{-2})$ for large $D$. The uniform amplitude and pair comparison in the linked proof give $|P|^2\le(1+O_C(1/D))p$. Thus $-\Re Z^2\le(a_C+O_C(1/D))p$ throughout this depth by the exact identity $-\Re Z^2=-2|P|^2(1+\cosh c\cos\theta)$. This uses a shrinking depth **only to price the complement**, not as a zero-free hypothesis. Charge each shallow retained pair this price, and restore the same price on the deep retained pairs by subtracting it inside $E_C$. Positivity of $p$ allows extending the price to the single budget $W_\sigma/R\le1/6+o(1)$. This proves the upper bound. The leftover $O_C(1/D)$ per unit of budget costs $o(1)$, not an error proportional to $\cosh c$.

For (1), start instead from the **full** charge at the failure, at least $47/81-1/3-O(\epsilon)-o(1)$. The center and line are nonpositive, and the outer tail costs $o(1)$. In the annulus the only additional entries to pay for are the gray pairs. At $c\le C$ these have already been priced by the same pointwise bound. At $c>C$ they cost at most $2(K-1)(\exp(1-\cos(\epsilon/2))+O(1/D))p\le a_Cp$ for $K=\cosh(0.28)$ and small $\epsilon$. Apply the **same budget once to this union**, obtaining (1). The strict margins use $(\cosh 1-1)/3<0.18103$ and $\cosh(1.15)/3<0.57914$.

## Where the genuine upper bound holds

Let $Q\le q\le2Q$ be integers, $D_*=2\log((9/5)\log(2Q))$, and $J_*=(2/\epsilon)\log D_*$. For any fixed $u>0$, the number of samples having even one right zero with $c>u$ in the annulus is at most

$$ Q\exp\!\left[-(4u/5-o(1))\frac{\log Q}{D_*}\right]. \tag{2} $$

Such a zero has $\beta>\sigma_0=1/2+u/D_*$ and $0<\gamma\le T=2(2Q)^{3/5}+J_*$. Each zero covers $O(1+J_*Q^{2/5})$ sample heights by their minimum spacing. Use the [Chourasiya and Simonič explicit Ingham bound](https://arxiv.org/abs/2507.15184), first corollary and its displayed specialization to $[0.500,0.625]$. Here $T\ge3\cdot10^{12}$ and $\sigma_0$ lies in that interval eventually. Its bound is $O(T^{3(1-\sigma_0)/(2-\sigma_0)}\log^3 T+\log^2 T)$ with absolute constants. The exponent is $1-2(u/D_*)/(3/2-u/D_*)$; using $\log T=(3/5)\log Q+O(1)$ gives (2), including the cost of the polylogarithms. No assumption on independent sampling of zeros and conductors is used.

With $u=0.28$, $H=0$ outside (2), since there are no retained pairs. With $u=1.12$, the upper bound above gives $H\le(\cosh(1.12)-1)/3+o(1)<0.233$ outside the **smaller** exceptional set (2). At $u=1.15$ equation (1) instead places every sufficiently large failure in (2). The count concerns zeta proximity, not a better dyadic count of twist failures than the [character estimates](principal-block-search.md#projection-and-limits). Even this smaller exceptional set can contain prescribed failing samples.

## An identity that isolates the deep zeros of zeta

One can access the depth selection without first locating the individual zeros. Choose $s_0=1/2+C/D$ unequal to any zero real part (almost every $C$ works at each sample), and set $s_1=1+1/D$. At ordinate $v$ write $W_s(v)=\sum_\rho k_{s-\beta}(v-\gamma)$, with the numerator **signed** on an interior vertical. This is the real completed logarithmic derivative by the same Hadamard identity; the kernel argument is written explicitly here. With $P_h(x)=k_h(x)/\pi$, $h=s_1-s_0>0$, one has the positive difference

$$ W_{s_1}(v)-(P_h*W_{s_0})(v)=
\sum_{\beta>s_0}\big[k_{s_1-\beta}(v-\gamma)+k_{s_1+\beta-2s_0}(v-\gamma)\big]. \tag{3} $$

In fact $P_h*k_d=\operatorname{sgn}(d)k_{h+|d|}$ for $d\ne0$. The smoothed sum of the absolute kernels converges since all $h+|s_0-\beta|$ are bounded above and below at fixed $D$ and the completed exterior Poisson sum converges. Thus the cancellation is termwise exact, including multiplicity; no lower bound on the distance to all zero real parts is needed. For each deep right zero the centered kernel on the right of (3) has Fourier transform $2\pi e^{-h|\xi|}\cosh((\beta-s_0)|\xi|)$. The depth in this hyperbolic cosine is **relative to the interior vertical**, not the critical line. In particular (3) is neither $E_C$ nor its majorant after a phase projection. At frequency $D$, $e^{-hD}=e^{C-1}/R$, so an $O(1)$ exterior trace error cannot just be discarded when undoing the smoothing at that frequency.

**Decision.** On exceptional samples, keep the subtraction $a_Cp$ and the opposite-band costs if testing $E_C$. A global density estimate alone does not test its sign there. [Shared-ordinate density models](shared-ordinate-weil-model.md) explain why even much more precise local data, without the depth assignment, need not identify $H$. The [constant depth transfer](interior-trace-depth-transfer.md) further keeps the entire translated trace at $s_0=1/2+1/D$ fixed and moves $E_1$ across both targets on typical samples. It does not give a low excess at a failure.
