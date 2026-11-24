# A one-sided price from one interior value trace

Use the [uncut test](uncut-trace-normal.md) at its prescribed height: $R=(9/5)\log q$, $t=2q^{3/5}$, $D=\log(R^2)$, $a=1/D$, $A=1/2+a$, $\alpha=2(\cosh 1-1)$, and $S=2\sinh 1$. For a right member put $b=\beta-1/2$, $x=\gamma-t$, $c=bD$. Write $k_h(x)=h/(h^2+x^2)$, $P_h=k_h/\pi$ for $h>0$, and set

$$ p_b=k_{A-b}+k_{A+b},\qquad \delta_b=k_{A-b}+k_{A+b-2a}. $$

All sums below count each $b>a$ once with multiplicity, over all ordinates; $b=a$ is not included. The positive measured defect is $\Delta(y)=\sum_{b>a}\delta_b(y-x)=W_A(y)-(P_{A-a}*W_{a+})(y)$ by the [Poisson difference identity](deep-retained-excess.md), with a right limit of the smoothed expression at a supporting depth. Put $d=\Delta(0)/R$. Uniformly $p_b=(1+O(a))\delta_b$: Only the second width changes, by $2a$, and its logarithmic derivative in the width is bounded by the reciprocal width. Thus $d\le(1+O(a))W_A(0)/R$. This uses one exterior budget, not one per band.

Let $F=g_\epsilon B^2$ be the original complex smoothed test, $K=e^{A|\partial|}F$ (Fourier multiplier), and $m_D=\int F/(2\pi)$. Measure the signed contrast

$$ Y=\frac{1}{2\pi R}\int_{\mathbb R}K(y)[\Delta(0)-\Delta(y)]\,dy. $$

**Price.** For fixed sufficiently small $\epsilon>0$, uniformly in the zero locations as $D\to\infty$,

$$ X\le Y-[m_D+\alpha-S-o_\epsilon(1)]d. \tag{1} $$

Here $X=R^{-1}\sum_{b>a}[-\Re F(x-ib)-\alpha p_b(x)]$. The coefficient before the error tends in the iterated limit ($D\to\infty$ first, then $\epsilon\downarrow0$) to $2/e$, not to zero. Thus a large failure requires the *single-defect contrast* $Y$ to exceed the uncut threshold $47/81-\cosh(1)/3-O(\epsilon)-o(1)$ **plus** this positive price times $d$. Centering matters: The coefficient for the uncentered pairing has the other sign. No bound on $Y$ at such heights is assumed.

## The signed remainder

Use $u=|\xi|$ and $\widehat F(\xi)=\int e^{-ix\xi}F(x)\,dx$. Define $q_b=[\sinh(a|\partial|)e^{-(b-a)|\partial|}F]$. The pair multiplier of $\delta_b$ is $2\pi e^{-(A-a)u}\cosh((b-a)u)$. Splitting $\cosh(bu)=e^{au}\cosh((b-a)u)-\sinh(au)e^{-(b-a)u}$ gives exactly

$$ X=-\frac{\int K\Delta}{2\pi R}+\frac1R\sum_{b>a}[q_b(x)-\alpha p_b(x)]. \tag{2} $$

The pole price was kept exact and separate. If using $F+2\alpha k_A$ in the multiplier split, add $\alpha(\delta_b-p_b)$ to $q_b$ and subtract $\alpha\delta_b$ instead: The result is identical. For fixed parameters $F$ is entire (the endpoint quotients below have removable poles), even, and real on the real axis. On strips slightly wider than $A$ it and its derivatives rapidly decrease for small $\epsilon$. Contour shifts for $F,xF,x^2F$ and two Fourier integrations by parts on the half-axes, retaining the derivative jump at zero, give $K=O_{D,\epsilon}((1+y^2)^{-1})$ and $\int K=2\pi m_D$. The sum of convolutions against $|K|$ converges: Convolving the inverse-square majorant with either positive Poisson kernel gives inverse-square decay at $x$ (widths bounded above). The logarithmic unit-interval zero count suffices. No uniform inverse-smoothing norm for $K$ is claimed.

In fact, put $g_\epsilon(x)=\exp(1-\cosh(\epsilon x))$ and $\phi=Dx-2\arctan(2x)$. For all $a<b\le1/2$ and all real $x$ one has the signed formula

$$ q_b(x)=\delta_b(x)\,[S e^{1-c}g_\epsilon(x)\cos\phi+o_\epsilon(1)]. \tag{3} $$

Here is an elementary uniform-error proof. Write $T_v=e^{-v|\partial|}$, so $q_b=(T_{b-2a}-T_b)F/2$. Take $b_0=\sqrt a$. On the real axis expand the exact two halves

$$ B(z)=\sum_{s=\pm1}\frac{e^{siDz/2}-e^{-D/4}}{1/2+si z}. $$

Squaring gives $F=2w+e^{iDx}H+e^{-iDx}\bar H+E$, where $w=g_\epsilon/(1/4+x^2)$, $H=g_\epsilon/(1/2+ix)^2$, and $|E|\ll e^{-D/4}/(1+x^2)$. The same expansion on $|\Im z|\le a$ uses the analytic extensions of the envelopes (including the reflected envelope for $\bar H$); the bound on $E$ still holds since $e^{aD}=e$. On this strip the envelopes and their first derivatives are $O_\epsilon((1+x^2)^{-1})$.

For $0<v\le b_0$, applying $T_v$ to a carrier $e^{i\omega x}h(x)$ with any of these envelopes gives

$$ e^{-v|\omega|}e^{i\omega x}h(x)+O_\epsilon\!\left(\frac{v\log(2/v)}{1+x^2}\right). $$

Indeed, freeze $h$ at $x$ in the Poisson integral. For $|y|\le1$ the envelope difference is $O_\epsilon(|y|/(1+x^2))$; for $|y|>1$ use $P_v(y)\ll v/(1+y^2)$ and the convolution bound for two inverse squares. This proof also works at $\omega=0$, and $T_0$ is the identity. The remainder $T_v E$ keeps its original bound up to a constant by Poisson convolution. For $-a\le v<0$, use $T_{-s}F=2\Re F(x+is)-T_sF$ with $s=-v$; this follows by contour shift. In the real part, freezing the shifted envelopes costs $O_\epsilon(a/(1+x^2))$ since $sD\le1$. The conjugate carrier pair gains $\cosh(sD)$ in that real part, hence gains $2\cosh(sD)-e^{-sD}=e^{sD}$ in $T_{-s}F$.

Consequently for $a<b\le b_0$, the low term cancels in the half-difference, and the carrier pair $2w\cos\phi$ gains $(e^{-(b-2a)D}-e^{-bD})/2=\sinh(1)e^{1-c}$. The additive error is $O_\epsilon(b_0\log(2/b_0)/(1+x^2))$. Both widths of $\delta_b$ are $1/2+O(b_0)$ here, so $\delta_b=(1+O(b_0))/(1/4+x^2)$ uniformly. This proves (3) through $b_0$. At $b=b_0$ the carrier itself is exponentially small in $\sqrt D$. For $b>b_0$ use $q_b=T_{b-b_0}q_{b_0}$, a **positive** Poisson propagation. It sends $k_{1/2}$ to $k_{1/2+b-b_0}\ll k_{A+b-2a}\le\delta_b$, since the two compared widths stay bounded above and away from zero. Both sides of (3) divided by $\delta_b$ are now $o_\epsilon(1)$. This avoids propagating a small absolute error through the growing relative-depth cosine.

## What must be measured

By (2) and (3) the loss in (1), up to $o_\epsilon(1)d$, is exactly the nonnegative quantity

$$ \frac S R\sum_{b>a}\delta_b(x)\,[1-e^{1-c}g_\epsilon(x)\cos\phi]. $$

This proves (1), since $0<g_\epsilon\le1$ on the real axis. Also $m_D\to\int w/\pi$ by the real-axis expansion and Riemann-Lebesgue, and $\int w/\pi\to2$ by dominated convergence. Thus $m_D+\alpha-S\to2+2(\cosh1-1)-2\sinh1=2/e$ in the stated order. The factor $S$ in the pointwise upper price $q_b/\delta_b\le S+o_\epsilon(1)$ is sharp for unrestricted single pairs: Take $x=0$ and $c\downarrow1$ from above. This is not a zeta sharpness claim.

If using the **uncentered** measurement in (2), only the region

$$ 1<c<1+\log(S/\alpha)=1.77193\ldots,\qquad g_\epsilon(x)\cos\phi>\alpha e^{c-1}/S $$

can add positive charge to it at leading order. This follows by pricing $q_b-\alpha p_b$ *together*, not by dropping a phase sign from the original test. All other pairs have already paid the remainder; the total uniform approximation error is $o_\epsilon(1)d$. In (1) even the worst such pairs have been paid by the constant part of the measurement. Neither version replaces the signed integral of $K\Delta$ by a norm bound.

## Precision of the sufficient test

The sufficient observable $Z=Y-(m_D+\alpha-S)d$ is linear in the one value defect. It can be evaluated without a numerical inverse Fourier transform: $K=2\Re F(\cdot+iA)-P_A*F$. If a surrogate defect has uniform absolute error $\eta$ (unnormalized trace units), the resulting error in $Z$ is at most

$$ \eta\left[\frac{\|K\|_1}{2\pi R}+\frac{S-\alpha}{R}\right]. $$

The bracket tends to $2e/\pi=1.7305\ldots$ in the same iterated limit. Indeed, put $z=x+iA$. In the two endpoint halves of $B(z)$ retain just $e^{-izD/2}/(1/2-iz)$. Its absolute value is $O(\sqrt R/(1+|x|))$; the error is $O(De^{-D/4}/(1+|x|))$, since $|1/2+iz|=|-a+ix|$. Thus in $L^1(dx)$,

$$ K/R=2e\Re\left(e^{-iDx}\frac{g_\epsilon(x+i/2)}{(1-ix)^2}\right)+o_\epsilon(1). $$

Here $e^{AD}=eR$, the Poisson convolution has bounded $L^1$ norm, and replacing $A$ by $1/2$ *in the envelope only* uses dominated convergence. Averaging the absolute real part of the carrier gives $2/\pi$ times the envelope modulus in the integral: Approximate the complex $L^1$ envelope by step functions on bounded intervals and average the ordinary absolute cosine on each interval. Finally $|g_\epsilon(x+i/2)|\to1$ and is bounded by $e$ for small smoothing, so its integral against $(1+x^2)^{-1}$ tends to $\pi$. This gives the stated constant. Uniform absolute accuracy is sufficient, not necessary: The error is tested against a signed carrier. The leading $L^1$ approximation alone is **not** accurate to $o(1)$ when integrated against a trace of size $O(R)$.

Only the window $|y|\le J=(2/\epsilon)\log D$ of the *smoothed defect* is needed up to $o_\epsilon(1)$ in $Z$ (this is not a cut on zero ordinates). Indeed $P_A*|F|(y)\ll(1+y^2)^{-1}$ and $|F(y+iA)|\ll R\exp(1-D^2/4)/(1+y^2)$ on the tail by the shifted endpoint bounds above. Also $\Delta(y)\le(1+O(a))W_A(y)\ll R+D^2+\log(2+|y|)$: Use the [completed exterior identity](opposite-phase-bands.md#spend-one-poisson-budget-not-two) at $t+y$, absolute Euler bound $O(D^2)$, bounded-width Stirling bound $O(\log(2+|t+y|))$, and the pole term $O(D)$ even near ordinate zero. Thus omitting the tail in $\int K\Delta/(2\pi R)$ costs $O_\epsilon(1/J)+o(1)$. The precision estimate applies also to errors bounded just on this window, with this additional truncation cost. It does not permit truncating $W_{a+}$ before the Poisson convolution at the same $J$.

**Decision.** A sufficient arithmetic target is $Y-(m_D+\alpha-S)d\le0.0658$ uniformly at the prescribed heights for all sufficiently small fixed smoothing and sufficiently large conductors, since the limiting failure threshold is $0.0658867\ldots$. Test the *priced inequality*, not separate smallness of the contrast and the scalar defect. Undoing the Poisson attenuation near frequency $D$ still magnifies trace errors by order $R$. The pointwise price is unconditional; the required exceptional-height estimate of this real-value trace functional is not proved.

**After-Work calibration.** The [depth discount and trace precision calculation](uncut-depth-discount.md) evaluates both this price and its slack on the existing finite Euler models. It gives a stronger sufficient test using one additional scalar and a better-conditioned interior pairing for $Z$ given exact exterior data; neither supplies the missing exceptional-height estimate.
