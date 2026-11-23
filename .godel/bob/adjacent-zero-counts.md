# A signed residue budget and an adjacent-count test

Let $y=q^{3/5}$, $t=2y$, $X=((9/5)\log q)^2$, and $D=\log X$. Assume the [external global $7/8$ strip for zeta](fixed-strip-endpoints.md#what-supplies-the-hypothesis), hence $1/8\le\beta\le7/8$. Write $u=\gamma-t$ for each nontrivial zero $\rho=\beta+i\gamma$, counting multiplicity. Use $S_X(t)=X^{-1}\sum_{p<X}(\log p)\log(X/p)p^{-it}$, the conjugate of the convention with $+it$. Suppose along a sequence $q\to\infty$ that $\Re S_X(t)\ge47/81-o(1)$, as required by an [endpoint failure at $y$](endpoint-zero-packets.md#spend-the-gamma-margin).

**Conclusion.** Put $h=\log(8/7)$, $A_h=225/12544$, $I_h=211/224$, and fix $c>0$ with

$$ m_c:=47/81-A_h-I_h\cosh(c)/3>0,\qquad\text{equivalently}\qquad \cosh c<571343/319032. $$

For any fixed $L>1/(2\pi)$ and $0<\eta<m_c$, one can choose a [log-window filter](log-window-filter.md) and $J=L\log D+O_{L,c,\eta}(1)$ such that at every sufficiently large peak in the sequence,

$$ -\Re\sum_{\substack{|u|\le J\\\beta>b_0}} X^{\beta-1+iu}\frac{M(\beta+iu)}{(\beta+iu)^2}>\eta,\qquad b_0=1/2+c/D. \tag{1} $$

In particular **at $c=1$ any margin below $0.07780110\ldots$ is available**. There is no small-packet premise and no count alternative. The minus sign and the multiplier $M$ are part of the test. The sum uses only right-hand zeros, not their reflected partners. We also obtain a requirement on the *variation* of their counts. Put $H=\pi/D$, let $N_b(I)$ count zeros with $\beta>b$ and $u\in I$, and set

$$ E_b(w)=N_b((w-H,w])-N_b((w-2H,w-H]). $$

There must be a cutoff $b_0\le b<7/8$ and a right endpoint $|w|\le J$ with

$$ |E_b(w)|\gg_{L,c,\eta} X^{1/8}/D. \tag{2} $$

The two intervals have half the wavelength of the residue phase. No prescribed sign of the raw count difference follows. Neither statement implies a peak from a zero configuration.

## A positive analytic test on the full zero strip

The main point is to price the oscillatory **amplitude** from the first cutoff smoothing without assuming the other zeros are sparse. Define

$$ \Phi(s)=\frac{\cosh(hs)\cosh(h(1-s))}{s(1-s)},\qquad K_h(u)=\Phi(1/2+iu)=\frac{|\cosh(h(1/2+iu))|^2}{1/4+u^2}. $$

We claim $\Re\Phi(\beta+iu)\ge0$ for the full strip. Set $x=\beta-1/2$, $P=1/4-x^2+u^2$, and $Q=2xu$, so $s(1-s)=P-iQ$. Up to the strictly positive factor $2(P^2+Q^2)$ the real part is

$$ P\big(\cosh h+\cosh(2hx)\cos(2hu)\big)-Q\sinh(2hx)\sin(2hu). $$

For $|u|\ge1$, $|Q|/P\le3/4$, and $|\sinh(2hx)|\le(3/4)\sinh h$ by convexity. Thus $\cosh^2(2hx)+(Q/P)^2\sinh^2(2hx)\le1+(1+9/16)(9/16)\sinh^2 h<\cosh^2 h$. Cauchy–Schwarz bounds the possibly negative trigonometric terms by less than $P\cosh h$ in modulus. For $|u|<1$, $\cos(2hu)>0$, while $|Q\sinh(2hx)\sin(2hu)|\le(3/2)h\sinh(h)u^2<P\cosh h$. This proves the claim. Nonnegativity just on the critical line would not justify the next use of a subset of the zeros.

The test gives the sum rule

$$ \frac1{\log t}\sum_\rho\Re\Phi(\rho-it)\ \longrightarrow\ \frac1{2\pi}\int_{\mathbb R} K_h(u)\,du=I_h. \tag{3} $$

To verify it, replace the denominator by $(s+\delta)(1+\delta-s)$ for fixed $0<\delta<1/8$ and call the result $\Phi_\delta$. Integrate $\Phi_\delta(s)\,\xi'/\xi(s+it)$ for the entire zeta completion around the verticals $r=1+\delta/2$ and $1-r$; neither kernel pole is enclosed. For fixed $t$ the separated horizontals used in the [contour proof](log-window-filter.md#explicit-formula-and-tail) vanish by the inverse-square kernel decay and the $O_\delta(\log^2(2+|t+\Im s|))$ bound away from zero ordinates. By reflection and conjugation the resulting zero sum is twice the real part of the upwards right-line integral divided by $2\pi i$ (that is, $2\Re\int \Phi_\delta(r+iu)(\xi'/\xi)(r+i(t+u))\,du/(2\pi)$). On that line the Euler product and Stirling give $(\xi'/\xi)(r+iz)=\tfrac12\log(2+|z|)+O_\delta(1)$, including its bounded imaginary part. For fixed $u$, $\log(2+|t+u|)/\log t\to1$, and a dominating envelope after normalization is $O_\delta((1+\log(2+|u|))/(1+u^2))$. Shifting the integral of $\Phi_\delta$ alone back to $1/2$ therefore gives (3) with the shifted test. Now $|\Phi_\delta-\Phi|\ll_h\delta/(1+u^2)$ throughout the zero strip, including its center. Since $\sum_\rho(1+u^2)^{-1}\ll\log(2+t)$, the error is $O_h(\delta)$ on either side after normalization. Let $\delta\downarrow0$. Finally $|\cosh(h(1/2+iu))|^2=(\cosh h+\cos(2hu))/2$, and the Fourier integral of $(1/4+u^2)^{-1}$ is $2\pi e^{-|v|/2}$. Thus $I_h=(e^h+3e^{-h})/4$ as claimed. Equation (3) tests a fixed function of the **complex** zero, not the growing-frequency residue phase against an ordinate limiting measure.

## Charge all but the right-hand zeros once

Use the [filter construction and prime comparison](log-window-filter.md#filter-and-prime-comparison): For $k=1/L$, fix $0<a_0<a_1<1/2<1<r'<2$ with $k(r'-a_0)<\pi$, $d=(a_0+r')/2$, and set

$$ M(s)=\cosh^2(hs)\exp\{\lambda(1-\cos(k(s-d)))\},\qquad F_b(u)=X^{b-1+iu}A_b(u),\quad A_b(u)=M(b+iu)/(b+iu)^2. $$

Take $\lambda>0$ small and fixed. The modified prime-power sum $T_M(t)$ has $\Re T_M(t)\ge\Re S_X(t)-A_h-o_{\lambda\downarrow0}(1)-o_{q\to\infty}(1)$; the first error is uniform in $q$. The [shift](log-window-filter.md#explicit-formula-and-tail) gives $T_M(t-v)=-\sum_{\beta>a_1} F_\beta(u+v)+o(1)$ uniformly for $0\le v\le2H$ at the frozen cutoff. The choice of the shifted vertical can depend on $v$, but the residue selection $\beta>a_1$ does not. On $[a_0,r']$ the second multiplier has absolute value $\le e^\lambda$. Its double-exponential decay, also after differentiation, gives

$$ |A_b(u)|+|\partial_b A_b(u)|+|\partial_u A_b(u)|\ll (1+u^2)^{-1}\exp(-c_*e^{k|u|}),\qquad c_*>0. \tag{4} $$

Constants here may depend on the fixed filter. The factor $O(e^{k|u|})$ from differentiating is absorbed by decreasing $c_*$. Choose the additive constant in $J$ large enough that truncating the right side of the shift at $|u|\le J$ costs $o(1)$, even with the shifts $v$, and even with an extra $D$ factor. Indeed $X^{-1/8}\log t=O(e^{3D/8})$ and $e^{kJ}=e^{k(J-L\log D)}D$.

Use either no height average ($\mu=\delta_0$), or the complex measure

$$ d\mu(v)=\frac{a}{H}\big(1_{[0,H)}(v)-1_{[H,2H)}(v)\big)\,dv,\qquad a=\frac{\pi}{4i}. \tag{5} $$

Both have $\int e^{iDv}\,d\mu(v)=1$; the latter has total variation $\pi/2$. Thus $\int T_M(t-v)\,d\mu(v)=T_M(t)+O(H)$, **before** comparing to the original cutoff: For each $n$ use $|e^{iv\log n}-e^{ivD}|\le2H|\log(X/n)|$. In the inverse weight for $T_M$ one may bound $|W_\lambda(z)|\ll e^{a_0z}$ for $z\ge0$ and $\ll e^{r'z}$ for $z<0$. These bounds follow by inversion on the two lines, and the convergent Chebyshev dyadic sums in the prime comparison remain convergent with the extra $|z|$. In particular $A_h$ is paid **once**, not multiplied by $\pi/2$.

For $a_1<\beta\le b_0$, replacing $\int F_\beta(u+v)\,d\mu(v)$ by $F_\beta(u)$ costs $O(H X^{\beta-1}/(1+u^2))$ per zero, by (4) on the **amplitude only** and the normalized phase. The total error is $o(1)$ since $X^{b_0-1}=e^c/\sqrt X$ and $\log t=\sqrt X/3+\log 2$. Zeros with $a_1<\beta<1/2-1/\sqrt D$ cost $O(e^{-\sqrt D}\log t/\sqrt X)=o(1)$ even absolutely. On the remaining set $U=\{1/2-1/\sqrt D\le\beta\le b_0\}$, the amplitude $|\cosh(h(\beta+iu))|^2/(\beta^2+u^2)$ and $\Re\Phi(\beta+iu)$ both differ from $K_h(u)$ by $O_h(D^{-1/2}/(1+u^2))$ uniformly, by bounded derivatives with the same inverse-square envelope. On $|\beta-1/2|\le c/D$, pair reflected zeros at the same ordinate: Their $X^{\beta-1}$ average is at most $X^{-1/2}\cosh(c)$, also valid on the line. All other zeros of $U$ are on the left, and individually cost at most $X^{-1/2}$ in this numerator. Consequently the absolute charge on $U$ is at most

$$ \frac{e^\lambda\cosh(c)}{\sqrt X}\sum_U \Re\Phi(\beta+iu)+o(1)\ \le\ e^\lambda I_h\cosh(c)/3+o(1). $$

The inequality uses positivity and the **whole-zero** identity (3), regardless of the number of excluded zeros. Choosing $\lambda$ small enough before taking limits, the prime comparison and shift now give, for either measure,

$$ -\Re\sum_{\beta>b_0,\ |u|\le J}\int F_\beta(u+v)\,d\mu(v)>\eta. \tag{6} $$

Choose $\lambda$ with strict slack so that subsequent $o(1)$ errors do not spend the margin. The point mass gives (1). The same amplitude argument also applies to the original [two-smoothing filter](localized-principal-packet.md) with its original $C_c\log D$ radius: Replace $e^\lambda$ by $G_\epsilon$ and the filter perturbation by $O_h(\epsilon)$.

## Move the difference onto the zero counts

Use (5) and restore the whole right-hand sum in (6) at cost $o(1)$. For each $\beta>b_0$ insert $F_\beta=F_{b_0}+\int_{b_0}^\beta\partial_b F_b\,db$. Changing variables to $w=u+v$ in each adjacent box gives exactly

$$ \sum_{\beta>b_0}\int F_\beta(u+v)\,d\mu(v)=\frac{a}{H}\int_{\mathbb R}\left(F_{b_0}(w)E_{b_0}(w)+\int_{b_0}^{7/8}\partial_b F_b(w)E_b(w)\,db\right)dw. \tag{7} $$

Endpoints in $w$ or in the layer integral are null sets; the separate base term counts strictly $\beta>b_0$. Absolute convergence and Fubini follow from (4), $\partial_b F_b=X^{b-1+iw}(D A_b+\partial_b A_b)$, and the unit count $|E_b(w)|\ll\log(2+t+|w|)$ for $2H<1$. In particular (7) did not truncate the counts at the window edge and create an artificial jump there.

The total $L^1(dw)$ cost of $F_{b_0}$ plus the integral in $b$ of that of $\partial_b F_b$ is $O(X^{-1/8})$: Integrating $D X^{b-1}$ costs $X^{-1/8}-X^{b_0-1}$, not another factor $D$. Pointwise in $w$ the analogous bound is $O(X^{-1/8}(1+w^2)^{-1}\exp(-c_*e^{k|w|}))$. Hence the part of (7) at $|w|>J$, including $1/H$, is $O(H^{-1}X^{-1/8}\log(2+t)\exp(-c_*e^{kJ}))=o(1)$ by the choice of additive constant. On $|w|\le J$ the magnitude is at most

$$ C H^{-1}X^{-1/8}\sup_{b_0\le b<7/8,\ |w|\le J}|E_b(w)|. $$

Combining this with (6) proves (2). The precise one-sided requirement is on the integral: If $I$ is the $dw$ integral on the core of (7), then $-(D/4)\Im I>\eta-o(1)$. Taking a supremum is not necessary if this projection can be bounded directly.

**What remains.** A uniform $o(X^{1/8}/D)$ discrepancy at these heights for these right-hand counts would exclude the peak, even if the unsigned packets were large. Here $X^{1/8}/D\asymp (\log t)^{1/4}/\log\log t$. Compare [Maples and Rodgers, *Bootstrapped zero density estimates*](https://arxiv.org/abs/1404.3080). Their CLT allows the fixed adjacent-box test at scale $H$ ($n(T)=H\log T/(2\pi)\to\infty$ and $n(T)=o(\log T)$ with the length frozen at $T\asymp t$), but counts **all** real ordinates at a uniformly random height. Their $L^k$ zero-density proposition does restrict $\beta>b$: Its length parameter $H\log T$ lies in $[1,T^{1/4}]$ here, but its bound on count increments is integrated in the center. Neither theorem supplies (or contradicts) the necessary discrepancy at an individual exceptional conductor. Nor would cancellation between a right-hand discrepancy and other layers in an all-zero count prove the needed bound. No uniform upper bound for (1) or for the signed integral in (7) has been proved here.

**After Work.** The [count-dispatch replay](count-dispatch-review.md) compares two ways to derive *necessary* discrepancies; neither bounds (7) from above. A separate [initial-harmonic budget](initial-harmonic-budget.md) reduces the number of centers in the $1<A<\pi/2$ single-endpoint test, not the individual-height obligation here at $A=9/5$. The [individual-projection model](individual-projection-model.md) shows that even a globally sparse right-hand set can give a large projection consistent with the fixed-width Poisson bounds and all fixed harmonic moment tests. The [critical-radius filter](critical-radius-projection.md) removes the strict inequality in the coefficient of $\log D$ in the necessary test, not the need for arithmetic control inside that radius.
