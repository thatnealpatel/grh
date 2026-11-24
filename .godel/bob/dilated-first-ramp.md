# Change the cutoff, not the prescribed ordinate

At a [real high-endpoint failure](sampled-principal-peaks.md#if-the-first-harmonic-barely-passes-price-the-third), write $y=q^{3/5}$, $R=(9/5)\log q$, $V=R^2$, and $m=8/9$. Define $S_W(t)=W^{-1}\sum_{p<W}(\log p)\log(W/p)p^{it}$ and the exterior-budget normalized traces

$$ C_j(l)=e^{l/2}\Re S_{e^l V}(2jy). $$

At the **same** height $2y$ as the original screen, $C_1(1/20)>.58603136-o(1)$ is necessary. In the continuum relaxation of just the failure's angular-mean datum, even using all dilations of that first real harmonic has sharp minimax value between $.58603230294$ and $.58603230297$. In contrast, two signed dilated traces at different harmonics satisfy

$$ \max\{C_1(.03),-C_3(.2)\}\ge .5895467121-o(1). \tag{1} $$

The improvement is in units of the same archimedean price, not the unscaled prime means. In particular the [undilated all-harmonic ceiling](high-endpoint-harmonics.md) does not cap this test. None of these inequalities is an upper bound on $Z$ in the [original uncut screen](uncut-defect-price.md).

## One ramp: Exact abstract saddle

Put $z=\log(V/p)$, $u=|\cos(y\log p)|$, and $d\mu_V=V^{-1}\sum_p(\log p)\delta_{p/V}$ in the coordinate $x=p/V=e^{-z}$. The original datum is $\int z_+u\,d\mu_V\ge m-o(1)$; the scaled $j$-trace is $e^{-l/2}\int (z+l)_+T_{2j}(u)\,d\mu_V$. Here $T_n(\cos v)=\cos(nv)$. In fixed weights not involving $u$, PNT gives the limiting measure $dx=e^{-z}dz$ (orientation reversed). For the weights here one may first restrict to $x\ge\eta$: On $x\le\eta$, all are $O(1+\log(1/x))$, with prime integral $O(\eta(1+\log(1/\eta)))$ by Chebyshev and partial summation. They vanish at a finite upper cutoff. No PNT is applied to the phases.

For fixed $h>0$, Cauchy-Schwarz with the quadratic weight $(z+h)_+$ bounds the integral of $(z+h)_+u^2$ below by $(m-o(1))^2/(L(h)+o(1))$, where

$$ L(h)=\int_0^\infty \frac{z^2}{z+h}e^{-z}dz=1-h+h^2 e^h\Gamma(0,h). $$

Since $T_2(u)=2u^2-1$ and $\int_{-h}^\infty(z+h)e^{-z}dz=e^h$, this proves $C_1(h)\ge B(h)-o(1)$ with $B(h)=2m^2e^{-h/2}/L(h)-e^{h/2}$. The [ball checker](check-dilated-first-ramp.py) evaluates $B(1/20)$, and brackets a zero $h$ of $B'$ in $(.0507336319726,.0507336319728)$ by opposite signs. It gives the stated enclosure of $B(h)$ throughout the bracket and $A_0=m/L(h)<.9300$. A sign bracket alone would not prove global optimality.

For the matching upper bound in the continuum relaxation, choose the following profile: $u(z)=A_0 z/(z+h)$ for $z\ge0$, zero for $-h\le z<0$, and $1/\sqrt{2}$ for $z<-h$. This is in $[0,1]$ and attains equality in the datum and in the $h$-trace bound. Let $f(l)$ denote the $C_1(l)$ integral with this profile and $dx$. Then $f(h)=B(h)$ and $f'(h)=0$, since $f(l)\ge B(l)$ near $h$ by the same inequality, and differentiation of the ramp integral has no endpoint term. Write $M=\int_0^\infty T_2(u)e^{-z}dz$ and $N=\int_0^\infty zT_2(u)e^{-z}dz$. On $0\le l\le h$,

$$ f(l)=e^{-l/2}[N+1+(M+1)l-e^l]. $$

The sign of $f'(l)$ is that of $(M+1)(2-l)-(N+1)-e^l$, strictly decreasing since $M\ge-1$. Consequently $f$ increases up to $h$. For $l\ge h$ the added region has $T_2(u)=0$, so $e^{l/2}f(l)$ is affine. The value and slope at $h$ yield $f(h+s)=B(h)(1+s/2)e^{-s/2}$, decreasing to zero.

For smaller cutoffs $l=-r\le0$, write $f(-r)=e^{-r/2}J(r)$ with $J(r)=\int_0^\infty v e^{-v}Q(v+r)dv$ and $Q(s)=2A_0^2s^2/(s+h)^2-1$. This $J$ is increasing and concave. For concavity note $Q''(s)$ changes sign once, from positive to negative at $s=h/2$. At $r=0$, integration by parts gives $J''(0)=\int_0^\infty(v-1)e^{-v}Q'(v)dv<0$. Indeed $Q'(v)=4A_0^2hv/(v+h)^3$; after dividing by $4A_0^2$ the positive part is at most $h/e$ and just $[h,2h]$ contributes at most $-(1-2h)e^{-2h}(2/27)<-h/e$ for $.05<h<.051$. For $r>0$ the weight on $Q''(s)$ relative to $s e^{-s}$ is $e^r(1-r/s)_+$, increasing in $s$. Comparing with its value at the sign change preserves the nonpositive integral. Hence $J'(r)-J(r)/2$ is nonincreasing. It is already negative at zero since $f'(0)>0$ by the first interval formula (the ramp gives the same derivative from both sides). Thus $f(-r)$ decreases with $r$. It is positive there since $J(0)=N\ge2m^2-1$ by Jensen under $ze^{-z}dz$. These comparisons prove $\sup_{l\in\mathbb R}|f(l)|=B(h)$, and with the lower bound at $h$ prove the minimax assertion, even allowing randomized conditional phase laws in the relaxation. This profile is not asserted to occur on primes.

## Two ramps: A lower certificate

Take $w=197/200$, $\lambda=69/20$, $l_1=.03$, and $l_3=.2$. Let $H(z)$ be the minimum over $0\le v\le1$ of

$$ w e^{-l_1/2}(z+l_1)_+T_2(v)-(1-w)e^{-l_3/2}(z+l_3)_+T_6(v)-\lambda z_+v. $$

Apply the inequality defining the minimum **before** taking the limit, then add back the failure datum. The weighted average of the two signed traces is at least $\lambda m+\int H(z)e^{-z}dz-o(1)$ by PNT on the continuous fixed envelope. The [rational certificate](check-two-dilated-ramps.py) bounds this last scalar below by $.5895467121$. On a grid of spacing $1/512$ in $v$, the nearest sample to an interior minimizer costs at most $\sup P''/(8\cdot512^2)$; endpoints are included. Here $T_2''=4$ and $(-T_6)''=-960v^4+576v^2-36\le252/5$. Between the ramp knots $H$ is a minimum of affine functions of $z$, so endpoint lower bounds give lower chords, not upper chords. The checker integrates them with outward weight bounds and integrates a separate affine lower bound for the whole tail $z\ge8$. This proves (1) without arithmetic phase equidistribution or an optimality claim for the two ramps.

## Price at the cutoff that produced the peak

For the first, positive test at $W=e^hV$, put $D'=\log W$, $a'=1/D'$, $A'=1/2+a'$. Define $X_h$ and $Z_h$ by the [uncut price](uncut-defect-price.md) at $D'$, but with **original** denominator $R$ in both functionals (equivalently multiply the own-cutoff functionals by $e^{h/2}$). At $t=2y$ the [translated prime formula](short-buffered-packet.md#price-the-smoothing-on-the-original-prime-side) has main price at most $\log(t/(2\pi))/\sqrt W$ before multiplication, hence $1/3+o(1)$ after it; its smoothing error remains $O_h(\epsilon)$. The pole price uses $W_{A'}(0)/R\le1/6+o(1)$ by the exterior identity at $1+1/D'$, since $D'^2=o(R)$. All relative-depth and line prices in the uncut proof are pointwise at $D'$. Thus the same shallow-complement argument charges $\alpha$ on that single budget and gives

$$ Z_h\ge X_h-o_\epsilon(1)\ge B(h)-\cosh(1)/3-O_h(\epsilon)-o(1). $$

For $h=1/20$ the margin before errors exceeds $.07167115$. This does not change the threshold on the *undilated* $Z$. It requires the smoothed interior trace at the new supporting depth, with its own right limit. The pointwise remainder and single-budget rules are unchanged; all ordinates enter before smoothing.

For either sign in (1) there is also a short-window test without changing the sign inside a positive-test proof. Use the [even Mellin tent](opposite-phase-bands.md#use-the-unused-half-of-the-log-axis) at its own $W_j=e^{l_j}V$, $D_j=\log W_j$, and $t_j=2jy$. Write $w_\rho,\phi_\rho$ for that note's residue weight and phase with $W_j,t_j$. For fixed $c>0$, the combined near-line and far-left absolute price at $|\beta-1/2|\le c/D_j$ and $1/4\le\beta<1/2-c/D_j$ is at most $G\cosh(c)/3+o(1)$ **after** multiplication by $e^{l_j/2}$, where $G=\exp(1-\cos\epsilon)$. Indeed the reflected shallow comparison to the exterior kernel has coefficient $(2G/\sqrt{W_j})(\cosh c+O_c(1/D_j))$, the far-left monotone comparison gives $e^{-c}$ in place of $\cosh c$, and their disjoint costs use just $W_{1+1/D_j}(t_j)\le R/6+o(R)$ in real-part coordinates. The $\beta<1/4$ and $|\gamma-t_j|>(2/\epsilon)\log D_j$ errors remain $o(1)$ for fixed dilation. By (1), in at least one branch $(j,s)=(1,+1),(3,-1)$ the remaining right zeros have

$$ e^{l_j/2}\sum_{\substack{\beta>1/2+c/D_j\\|\gamma-t_j|\le(2/\epsilon)\log D_j}} w_\rho(-s\cos\phi_\rho)\ge .5895467121-G\cosh(c)/3-O(\epsilon)-o(1). $$

Here $\log(2+t_j)=R/3+O(1)$ for both branches. Do not remove the central ordinates in the negative test or add the budgets of the two branches. At $c=1$ a margin $>.0751$ survives for sufficiently small fixed smoothing. Taking $c=1.17$ still forces a nonempty packet. At the **single** prescribed height $2y$ the first ramp alone forces a packet for $c=1.164426$ by the same tent estimate and the ball check. These are necessities, not uniform bounds on exceptional heights. The [mean bound](uncut-screen-mean.md) estimates the original $Z$ away from such exceptions in measure; it cannot be specialized to the branch of a failure.

**After Work.** A [single conditional phase law](dilated-harmonic-ceiling.md) now bounds the gain available from this comparison even with every real dilation and every harmonic. The two-test depth $1.17$ survives, but endpoint angular mean alone cannot clear the packet payment at $1.175$. At a remaining exception, seek information beyond this mean, not additional ramp parameters to reach that depth.
