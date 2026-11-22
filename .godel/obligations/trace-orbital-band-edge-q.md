# A bandwidth threshold for null lifts in the rational circle test

**Question:** In the half-twisted ring-transition model, does the cutoff composition depend on how one lifts an orbital circle mode? The [existing circle comparison](trace-orbital-q.md#half-weight-untwisting-and-the-iterated-limit-on-a-section) takes specified lifts. The test here varies one mode by a genuine representative of zero, without changing the quotient mode. It distinguishes a stable range of band-to-position ratios from a range in which even ambient-norm convergence of the lifts is insufficient. This is a paper calculation for a project replacement, not a theorem about the Haar-indented shell.

In the trivial isotype over $\mathbb Q$, fix $L=\log p$, $0<\alpha<1/2$, $r\ge1$, and the Hilbert norm with weight $w(x)=e^{2\alpha|x|}(1+x^2)^r$ against $dx$. Let $v_b(x)=e^{x/2}\sum_{n\ne0} b(ne^x)$ for even Schwartz $b$ with both $b(0)=\widehat b(0)=0$. Let $Q_Y$ project onto the closed theta level $W_Y$ of additive Fourier band $Y$, and $P$ onto the full geometric closure. Let $A_f z=f*z$ for nonzero $f\in C_c^\infty(\mathbb R)$ and $a=\inf\operatorname{supp} f$. The test concerns exactly

$$C_{R,Y}z=\Pi M_{\rho_R} P A_f Q_Y z,\qquad \Pi z([x])=\sum_{k\in\mathbb Z}e^{-(x+kL)/2}z(x+kL).$$

Here $Q_Y$ acts first. On $W_Y$ it fixes the input, and $P$ fixes the convolution output by invariance of the full geometric range. Untwisted circle Haar is $dx/L$. We do not extend the uncut $\Pi$ to the ambient Hilbert space. It is defined on each lower-bounded support space: The finitely long left part has a finite fibre bound, and the right tail has the bound below. The log cutoff is supported on $[-R,R]$, $R=\log\Lambda$, with $0\le\rho_R\le1$. Use the symmetric cutoff conditions in Definition 9.3.3.1, p. 427, with $\varepsilon\Lambda=o(1)$ as in (11.3.2.4–5), pp. 495–496 (text extraction). It equals one on $[-R+\delta_R,R-\delta_R]$, where $\delta_R=-\log(1-\varepsilon/\Lambda)=o(e^{-2R})$: Reflect the upper half of the norm plateau $[1,\Lambda-\varepsilon]$. This improved *log* transition width matters at equality.

## Stable up to and including the support edge

For every $Y\le e^a\Lambda$ and $z\in W_Y$ with $\Pi z=0$,

$$\|C_{R,Y} z\|_{L^2(\mathbb R/L\mathbb Z)}\le C_{f,L,\alpha,r}\,e^{-(1/2+\alpha)R}(1+R)^{-r}\|z\|_H$$

for sufficiently large $R$. The [Poisson support edge](trace-level-transport-q.md#the-poisson-edge-separates-the-cutoff-traces) gives $z=0$ below $-\log Y$, also for the closed level. Thus $u=A_fz$ vanishes below $a-\log Y\ge-R$. Its full periodization is zero: Untwisting conjugates convolution to convolution by $e^{-t/2}f(t)$, which periodizes to circle convolution against $\Pi z$. Unfolding is legitimate by weighted Cauchy–Schwarz on lower-bounded support (in particular $e^{-x/2}z\in L^1$). Hence only $(1-\rho_R)u$ needs a bound.

On $[-R,-R+\delta_R]$ compact-local Cauchy–Schwarz for convolution gives $|e^{-x/2}u(x)|\le C e^{(1/2-\alpha)R}(1+R)^{-r}\|z\|_H$, since the input lies within fixed distance of $-R$. The interval has length less than $L$, so periodization has no overlap, giving the additional factor $\sqrt{\delta_R/L}=o(e^{-R})$. On the right, every $h$ supported in $[T,\infty)$ for $T\ge1$ satisfies

$$\|\Pi h\|_2\le C e^{-(1/2+\alpha)T}(1+T)^{-r}\|h\|_H.$$

Apply Cauchy–Schwarz on each fibre: The squared multiplier bound is the sum of $e^{-y}/w(y)$ over fibre points $y\ge T$, bounded by a geometric series times $e^{-(1+2\alpha)T}(1+T)^{-2r}$. Integrate the weighted square sum over the period. Take $T=R-\delta_R$ and use boundedness of $A_f$ on $H$ by compact translation bounds. This proves the estimate, hence uniform stability on bounded null inputs. It also bounds relative traces for changes of section into this null subspace with bounded **trace norm**, by the trace ideal inequality; bounded operator norm alone makes no such trace assertion in growing dimension.

## Every larger fixed ratio admits vanishing-norm witnesses

Fix $\kappa>e^a$ and $Y=\kappa\Lambda$. Choose real even $\widehat b\in C_c^\infty([-1,1])$ vanishing near zero and nonzero arbitrarily close to $1$ from the left. Arrange zero integral by subtracting an interior even bump away from zero and the edge. Then $v=v_b$ has support infimum zero: Just above $x=0$ only the pair $\pm1$ contributes to the Poisson sum, and below zero no term contributes. The right tail decays faster than any exponential by the original Schwartz sum. The left support infimum of $f*v$ is therefore $a$ by the Titchmarsh convolution theorem; one can truncate $v$ smoothly to the right before applying the compact-support theorem near $a$. In particular this works for signed tests. Put $F(y)=e^{-y/2}(f*v)(y)$. Choose

$$a-L<c<\min(a,\log\kappa-L),\qquad \int_c^{c+L}F(y)\,dy\ne0.$$

Such a $c$ exists since the primitive from $a$ cannot vanish throughout any right neighborhood of $a$. With $S_du(x)=u(x+d)$, put

$$z=(1-p^{-1/2}S_L)v,\qquad d=R+c,\qquad w_R=e^{-d/2}S_d z.$$

The vector $z$ is the theta profile of $b-b(p\,\cdot)$, and $w_R$ the profile of that test dilated by $e^d$. Both moments remain zero, and its band is at most $p e^d<Y$, with slack even for strictly interior levels. Untwisting $z$ gives an ordinary translation difference, hence $\Pi w_R=0$ by telescoping. Translation bounds give $\|w_R\|_H=O(e^{-(1/2-\alpha)R}(1+R)^r)\to0$. Since both projections act as above, the constant coefficient of the cutoff output is exactly

$$\int C_{R,Y} w_R\,\frac{dx}{L}=\frac1L\int_{\mathbb R}\rho_R(y-d)\big(F(y)-F(y+L)\big)\,dy\longrightarrow\frac1L\int_c^{c+L}F(y)\,dy\ne0,$$

where the left integral is over one period. The translated cutoff tends a.e. to the indicator of $(c,\infty)$ and $F$ is integrable. In particular, for each sufficiently large **fixed** $R$ this is a genuine fixed null input with nonzero output for every sufficiently large band. This is not failure merely of the cutoff multiplier or of a projector on unrelated ambient inputs. For a fixed ratio the stable and unstable alternatives above meet at $e^a$; no rate boundary for ratios approaching $e^a$ from above is asserted.

**Scalar interpretation:** Change a lifted constant mode by $w_R$ and keep all other modes fixed. If $\ell_0$ extracts the normalized constant Fourier coefficient, the change of section is $w_R\otimes\ell_0$. The induced operator difference is rank one, with relative trace $\ell_0(C_{R,Y}w_R)$. No trace-class hypothesis on a base operator is needed for this relative trace; it is a difference of ordinary traces only when those are defined. Thus exhaustion-dependent genuine lifts constrained only by quotient value and ambient closeness do not specify a limiting scalar above the threshold. For a **fixed** genuine finite-band null input the stable estimate applies eventually. This result neither contradicts a limit on a prescribed section nor proves that such perturbations preserve any manuscript indentation. It concerns a circle output, not the ambient global trace or the joint real-place local trace. The missing step is still to identify a shell-preserving lift of the same Haar diagonal, not to choose its Fourier lifts after seeing the cutoff.
