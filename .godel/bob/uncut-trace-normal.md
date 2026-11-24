# The uncut failure test and the missing real boundary term

A failure can be tested without the discontinuous bands, but not just by dropping the opposite-band cost while retaining the favorable band. Use the **full signed** test. Put $a=1/D$, $A=1/2+1/D$, $b=\beta-1/2$, $x=\gamma-t$, $\alpha=2(\cosh 1-1)$, $F=g_\epsilon B^2$ as in the [two-band test](weil-phase-bands.md), and

$$ f(z)=-[F(z)+2\alpha k_A(z)]/R,\qquad X=\sum_{b>a}\Re f(x-ib). $$

The sum counts a deep reflected pair at its right member, over all ordinates. Indeed $2\Re k_A(x-ib)=k_{A-b}(x)+k_{A+b}(x)=p$. On the whole shallow complement the pointwise [depth price](deep-retained-excess.md) gives $-\Re F\le(\alpha+O(1/D))p$ per pair, and the line charge is nonpositive. Thus the full charge is at most $X+\alpha W_A(0)/R+o(1)$, with $W_d(y)=\sum k_{d-b}(y-x)$ now indexed by displacement from the line. Since $W_A(0)/R\le1/6+o(1)$, a large high-endpoint failure still requires

$$ X\ge 47/81-\cosh(1)/3-O(\epsilon)-o(1). \tag{1} $$

This is a failure test, not an upper bound on $H$ at every sample. The [hard-cut mesh ambiguity](trace-mesh-phase-cut.md) is not a counterexample for this new functional: Its four varying layers are all deep and their full analytic pairing cancels.

## A formula on real verticals

Choose $1/2<e<A$ so that the price pole is outside the strip. At $d=a,e$ use $r_d(y)=\Re f(y-id)$ and $J_d(y)=\int_{-\infty}^y\Im f(v-id)\,dv$. The imaginary part is odd and integrable. Equivalently $J_d=-\int_0^d r_w\,dw$, by the Cauchy-Riemann equations and decay. Set

$$ M_d=\int W_d r_d+N_d,\qquad N_d=\langle\partial_d W_d,J_d\rangle. $$

Take the normal derivative locally off supporting depths, pairing with a smooth ordinate cutoff before removing it. Then

$$ 2\pi X=M_e-M_a. \tag{2} $$

Here is a per-zero verification. In the Fourier convention $\widehat f(\xi)=\int e^{-iy\xi}f(y)\,dy$, put $u=|\xi|$. The symbols on $f$ of $r_d,J_d$ are $\cosh(du),-\sinh(du)/u$ by horizontal contour shifts (continuous value at zero). For a zero of depth $b\ne d$ the Poisson and normal kernels have symbols $\pi\operatorname{sgn}(d-b)e^{-|d-b|u}$ and $-\pi u e^{-|d-b|u}$. Its total operator on $f$, evaluated at $x$, therefore has symbol

$$ \pi e^{-|d-b|u}\,[\operatorname{sgn}(d-b)\cosh(du)+\sinh(du)]
=\begin{cases}\pi e^{bu}&d>b,\\-\pi e^{-bu}&d<b.\end{cases} $$

Subtracting the two boundaries leaves $2\pi\cosh(bu)$ exactly for $a<b<e$, zero otherwise. This gives (2), including the sign of the normal term. A boundary carrying zeros uses $M_{a+}$, the limit of the entire boundary expression from the right; this excludes $b=a$.

For convergence, $r_d,J_d$ and their first two derivatives have inverse-square decay or better at fixed parameters, by the shifted price kernel and the rapidly decreasing $F$. Pairing $k_{d-b}$ with $r_d$ costs $O((1+x^2)^{-1})$ uniformly in $b$, by the $L^1$ mass and the far tail of the kernel. For the normal kernel write $\partial_d k_{d-b}(w)=\partial_w[-w/((d-b)^2+w^2)]$. Integrate by parts against $J_d$ with smooth cutoff $\chi(y/T)$ equal to one near zero. The resulting test $j=(J_d\chi)'$ has zero integral, $j=O((1+|y|)^{-3})$, and $j'=O((1+|y|)^{-4})$, uniformly for $T\ge1$. Near $|y-x|<1$ subtract $j(x)$ by oddness. For $|x|>4$, on $|y|<|x|/2$ subtract the kernel at $-x$ at cost $O(|y|/x^2)$; the omitted constant integrated there costs $O(|x|^{-3})$ since $\int j=0$. The remaining region $|y|\ge |x|/2$, $|y-x|\ge1$ costs $O(|x|^{-2})$ by the tail of $j$. These bounds are uniform as $b\to d$. The unit-interval zero count permits summation and cutoff removal. The per-zero formula, or the same uniform bounds, justifies the one-sided boundary limit. No ordinary derivative of an infinite global pairing across a dense set of depths is assumed.

The exterior term is available from a completed Euler trace in absolute convergence. Given $W_a$ off supporting depths, a **lower** bound for $N_a$ gives an upper bound for $X$: It must make $(M_e-\int W_a r_a-N_a)/(2\pi)$ smaller than (1), with room for the errors. No such arithmetic bound is proved here.

## Why the normal term is not redundant in the continuous test

Use the [finite Euler model](interior-trace-depth-transfer.md) with total densities in units of $\lambda$. Use layers at scaled depths $c=0,.99,1.01,40$, with baseline densities $(.32,.24,.21,.23+U(v-1))$; $U$ has symbol $\operatorname{sech}(40\xi/D)$. This gives the same analytic functional $\lambda\int vf$ by horizontal shifts. Let $\omega=D-2$, $m=\omega/D$, $C_c=\cosh(mc)$, and perturb the densities by $\pm .04 h_c\cos(\omega x)$, where

$$ \kappa=\cosh(.01m)/\cosh(39m),\quad S=C_{1.01}-\kappa C_{40},\quad h_{1.01}=1,\quad h_{40}=-\kappa, $$
$$ h_{.99}=(1-\kappa-S)/(C_{.99}-1),\qquad h_0=-1+\kappa-h_{.99}. $$

The sum of coefficients and their $C_c$ moment vanish. So does the deep relative-depth $\cosh((c-1)m)$ moment. By the [Poisson difference identity](deep-retained-excess.md) and the nonzero smoothing symbol on this single frequency, the entire real trace at $a$ agrees, in addition to the pointwise marginal and full finite Euler functional. Positivity holds eventually: $h_{.99}\to4.0713\ldots$, $h_0\to-5.0713\ldots$, and $\|U(v-1)\|_\infty<10^{-7}$ eventually.

The deep layers alone have nonzero $C_c$ moment $S\to-1.1635\ldots$. With the pair density half the total, the two $X$'s differ by $-.04(\lambda/R)S\widehat{(F+2\alpha k_A)}(D-2)$. On the real axis the two-half expansion of $B$ in the band proof replaces $a(1/2\pm ix)$ by $(1/2\pm ix)^{-1}$ at $O(e^{-D/4})$ relative numerator error. In the transform at $D-2$ only the positive carrier square survives as $D\to\infty$, by Riemann-Lebesgue. Its limit is $\int g_\epsilon(x)e^{2ix}/(1/2+ix)^2\,dx$, tending as $\epsilon\downarrow0$ to $4\pi/e$ by the Fourier transform of $v e^{-v/2}\mathbf1_{v>0}$. The price transform vanishes. Since $\lambda/R\to1/(6\pi)$ the gap has iterated limit $.011414\ldots$, positive for small fixed smoothing. This does not straddle a failure threshold or model a failing character.

**Exact versus stable data.** Even a single exact real trace determines a bounded-depth, locally finite *atomic* reflected array of logarithmic unit counts, in the sense of meromorphic continuation. Each kernel continued in $y$ has residues $\pm1/(2i)$ at $x\pm i(a-b)$; distant terms converge normally off the poles. Push the signed pole measure (residues multiplied by $2i$) forward by $(x,v)\mapsto(x,a-v)$. It is $\nu=\mu-\tau_{2a}\mu$ by reflection of the depth measure $\mu$, where $\tau_s$ translates depth by $s$. Hence $\sum_{j=0}^{n-1}\tau_{2aj}\nu$ restricted to the critical strip recovers $\mu$ for $2an\ge1$, including after pole cancellations. This is not a stable real-axis estimate. Neither the continuous witness nor such exact identification decides the size of (2) for zeta.
