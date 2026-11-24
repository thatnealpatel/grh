# A fixed ambiguity inside an arbitrarily narrow trace-mesh cell

For the exact two-band $E_1$, shrinking the gap between sampled interior verticals need not shrink the uncertainty in the [positive continuous model](interior-trace-depth-transfer.md). Fix **any open interval** $I\subset(1,2)$ in scaled depth. There are two assignments with the same ordinate marginal, the same spatial mean at each depth, the same analytic functional with the Euler coefficients through $2V$, and the same entire translated real Poisson traces on every vertical outside the cell (and its reflection, at verticals not supporting a layer). Yet their $E_1$ differ by more than $.03$ at all sufficiently large prescribed samples. Typically the smaller value is below $.0519$ and the larger above $.0658$. The width of $I$ does not enter these margins. The construction and the onset of the asymptotic **do** depend on $I$. No straddling at a failing conductor or assertion about the true zeta trace is made.

## Four layers that preserve the measured functions

Use $t=2q^{3/5}$, $R=(9/5)\log q$, $D=2\log R$, $\lambda=\log(t/(2\pi))/(2\pi)$, and $\phi=Dx-2\arctan(2x)$. Layer densities below are in units of $\lambda$ and include both reflected sides, so the pair density is half the displayed total. Take four distinct depths $c_j=c_1+(j-1)h$ in $I$, in increasing order, with physical distances $c_j/D$ from the critical line. Write $S$ for the convolution of symbol $s(h\xi/D)$, where

$$ s(v)=(1+2\cosh v)^{-1}=\sinh(v/2)/\sinh(3v/2). $$

This is positivity preserving and has mass $1/3$: It is the strip Poisson map with lower boundary zero, upper boundary the input, width $3h/(2D)$, evaluated $h/(2D)$ from the lower side (solve the Fourier mode ODE). Equivalently its kernel for strip width $d=3h/(2D)$ is $\sin(\pi/3)/[2d(\cosh(\pi x/d)+\cos(\pi/3))]$. Its first absolute moment is $O(h/D)$.

Let $b_+,b_-$ be nonnegative trigonometric polynomials of circular mean one, to be chosen, and abbreviate $b_\pm(\phi(x))$ to $B_\pm$. Take $m=.04$. In A use the ordered densities

$$ (d_1,d_2,d_3,d_4)=m(S B_-, B_+, B_-, S B_+); $$

in B interchange $+$ and $-$. The common total mean is $8m/3$; even the *individual* means agree. Indeed $e^{ik\phi(x)}$ for $k\ne0$ has spatial mean zero (its slow factor tends to a constant at each end), and convolution multiplies the mean by its mass. These statements do not prescribe the local mass of each depth on each ordinate interval.

With $g=B_+-B_-$ the difference vector is $m(-Sg,g,-g,Sg)$. Its sum vanishes pointwise. For $X=e^{\pm h\xi/D}$ it annihilates the geometric progression in the depth index, by

$$ -s+X-X^2+sX^3=s(X-1)(X^2-2\cosh(h\xi/D)X+1)=0,\qquad s=s(h\xi/D). $$

For an interior vertical at physical displacement $a\ge0$ from the line, the pair Poisson multiplier per unit total density, divided by $\pi$, is $e^{-a|\xi|}\cosh(c_j\xi/D)$ if $a>c_j/D$, and $-\sinh(a|\xi|)e^{-c_j|\xi|/D}$ if $a<c_j/D$. Thus for $a$ below all four layers or above them the entire trace difference is zero. The negative verticals follow by reflection. This is an identity of convolutions with integrable kernels (their Fourier transforms agree), so does not require treating the bounded densities as integrable. It includes the constant mode, without moving any mean mass between depths. It also kills $\cosh(c_j\xi/D)$ in the analytic functional, where one moves the shifts onto the analytic test, not onto the density.

## Common exterior completion

Write $L=40$, $C_j(\xi)=\cosh(c_j\xi/D)$, $C_L(\xi)=\cosh(L\xi/D)$ (the latter subscript denotes depth, not a layer index). Use the [finite Euler model](shared-ordinate-weil-model.md) target

$$ v(x)=1-\frac{1}{\pi\lambda}\sum_{n\le 2R^2}\frac{\Lambda(n)}{\sqrt n}\cos((x+t)\log n). $$

Put $l=\alpha F_{16}(\phi)$ on the line, with $F_N(\theta)=|\sum_{k=0}^{N-1}e^{ik\theta}|^2/N$ and $.5\le\alpha\le.75$. The remaining layer at $L$ has density

$$ d_L=C_L^{-1}(v-l)-\sum_{j=1}^4 (C_j/C_L)d_j . $$

Only the *ratios* act on densities as multipliers. The cubic identity shows $d_L$ is identical in both assignments. By the symmetric shifts of a strip-holomorphic decaying test $f$, as in the finite Euler model, the full pairing is exactly $\lambda\int vf$. Specifically, convolving the shifted $L$ test by $C_j/C_L$ returns the shifted $c_j$ test, and by $1/C_L$ returns $f$. All depths are eventually in the critical strip.

Uniformly in $x$ at large $q$, $d_L$ differs from $1-\alpha-8m/3$ by less than $10^{-5}$. For the Euler part of $C_L^{-1}(v-1)$ the [previous split at $n=R$](interior-trace-depth-transfer.md) costs less than $10^{-7}$ eventually. For the rest, each multiplier has a rescaled Schwartz kernel with first absolute moment $O_{I,L}(1/D)$, so on each mode $e^{ik\phi}$ it acts by its value at $kD$ with uniform $o(1)$ error, by freezing the Lipschitz slow factor. This also applies to the compositions with $S$. The polynomials are fixed before $q$ grows. At $k\ne0$ the ratios $C_j/C_L$ are at most $2e^{-38|k|}$, $s\le1/3$, and the Fourier coefficients of any of the nonnegative mean-one polynomials have modulus at most one. For instance, the limsup of the nonconstant polynomial contribution is at most $4\alpha/(e^{40}-1)+16m/(e^{38}-1)$, even if the degrees chosen for a narrow cell are very large: Each frozen coefficient is bounded by the multiplier at that mode, and the uniform freezing errors vanish for each fixed polynomial. In particular $0<d_L<1$ eventually. Positivity at the four other layers is exact.

## The jump the trace misses

Use $w=g_\epsilon(x)/(1/4+x^2)$, $A=(6\pi)^{-1}\int w$, $T=(\cosh 1-1)/3$, and $K=\cosh(.28)$. Fix smoothing sufficiently small that $.33<A\le1/3$. Write $\langle\cdot\rangle$ for normalized circular integration. For fixed $c\in I$ the limiting $E_1$ per phase profile $b(\phi)$ is $\langle b R_c\rangle$, with

$$ R_c(\theta)=-[A(1+\cosh c\cos\theta)+T]\,\mathbf1_{|\cos\theta|>K/\cosh c}. $$

Indeed the charge per pair before normalization tends in envelope-adjusted carrier form to $-2w(1+\cosh c\cos\phi)$ on compacts, and the price to $-2(\cosh1-1)/(1/4+x^2)$. The pair normalization is $\lambda/(2R)\to1/(12\pi)$. In the [exact phase](weil-phase-bands.md) the phase error is $o(1)$ on compacts. Bound the **absolute** mask error by a neighborhood of the finitely many cut points times the sup norm of the fixed profile and weight. Circular averaging against either weight follows by Riemann-Lebesgue on the nonzero carrier modes; the boundary neighborhoods then shrink to zero mass. The central hole and outer tails cost $o(1)$ by the fixed-depth integrable envelopes. Thus this prices both exact bands, not a one-sided phase surrogate. The bound is not uniform in the sup norm of the profile as $I$ shrinks. For $SB_\pm$ the limiting profile is $S_h b_\pm$, where $S_h$ acts on circular mode $k$ by $s(hk)$, by the same freezing estimate.

Consequently $E_{1,A}-E_{1,B}$ tends at **every** sequence of samples to

$$ m\langle (b_+-b_-)H\rangle,\qquad H=-S_hR_{c_1}+R_{c_2}-R_{c_3}+S_hR_{c_4}. $$

All the common layers cancel, including the Euler layer. The two $S_h$ terms are continuous since their circular multipliers decay exponentially for fixed $h>0$. At $\tau=\arccos(K/\cosh c_2)$, $R_{c_3}$ is continuous, whereas $R_{c_2}$ jumps from $-[A(1+K)+T]$ to zero as the angle increases. Thus the upward jump of $H$ is $A(1+K)+T>.84$. Choose two centers just to the right and left of $\tau$ so that they are continuity points of $H$ with right value minus left value $>.82$. Take $b_+,b_-$ to be the same Fejér kernel $F_N$ centered at the respective points. By approximate identity convergence at those points, some finite $N$ gives $\langle(b_+-b_-)H\rangle>.8$. This proves a limiting gap exceeding $.032$, independently of $|I|$. It is the jump in the **opposite band's cost**, not a large favorable-only charge.

## Calibrating the two targets

At density-one samples in the convergence-in-density sense of the [moving-cutoff calculation](shared-ordinate-weil-model.md#evaluating-the-full-and-line-charges), start from the full off-line charge less its full price. Its common benchmark is

$$ B(\alpha)=A[-1+(31/16)\alpha]-(1-\alpha)T. $$

This subtracts the line's full charge and its share of the Poisson budget only once: The full charge is $-A+o(1)$ in density, the line charge $-(31/16)\alpha A+o(1)$ at all samples, and the total and line Poisson sums are $\pi\lambda+o(R)$ and $\alpha\pi\lambda+o(R)$ respectively by the finite functional and averaging. All off-line depths here exceed one. To obtain $E_1$, add the *gray recovery*, that is, the negative of the uncut charge less price on the omitted gray set. At the four layers, its limiting value $G_i$ in assignment $i$ is the integral of its four nonnegative circular profiles times $[A(1+\cosh c_j\cos\theta)+T]$ on the corresponding gray sets, summed over $j$. Hence $G_i$ does not depend on $\alpha$, and

$$ 0\le G_i\le(8m/3)[A(1+K)+T]<.094, $$

since even $T-A(K-1)>0$. At $L$ the absolute gray recovery is less than $10^{-6}$ eventually (or in limsup): Use $d_L<1$, the actual gray bound $|\Re Z^2|\le2(1+K)|P|^2$, and the carrier gray fraction $2\arcsin(K/\cosh L)/\pi$ as in the [constant transfer](interior-trace-depth-transfer.md). The cuts at the ends of the annulus again cost $o(1)$.

Here the uncut first harmonic of the $L$ layer is **not** an error: It is already included through the exact full analytic pairing in $B(\alpha)$. Only its gray correction is estimated by the gray fraction. The midpoint $B(\alpha)+(G_A+G_B)/2$ excluding that small correction is affine increasing. At $\alpha=.5$ it is below $.05$ even using the upper bound $.094$, and at $.75$ it exceeds $.09$ even with zero recovery. Set it equal to $(.0519+.0658)/2$. Because the common benchmark and common $L$ layer cancel, $G_A-G_B$ is the limiting gap already proved. Thus the typical values have $E_{1,B}<.0519$ and $E_{1,A}>.0658$, with slack even after the $L$-layer error. This is for separately constructed models at each sample. At a hypothetical high-endpoint failure the [finite prime-side calculation](shared-ordinate-weil-model.md#cutting-to-the-exact-bands) supplies the same extra $\Re S_V(t)+O(\epsilon)+o(1)$ to each, with $\Re S_V(t)\ge47/81-o(1)$ at that failure's own cutoff. The smaller calibrated benchmark is at least $(.0519+.0658)/2-.094/2>.011$, since both $G_i$ are in $[0,.094]$. With sufficiently small fixed smoothing the gap survives but neither assignment is a low-excess model at such a failure.

**Decision.** For the hard band observable, neither the mesh size alone nor removing the constant-depth ambiguity gives an error tending to zero on general positive assignments. Even exact mean masses and exact translated traces off one narrow cell miss a fixed charge there. A refinement argument for actual zeros needs more, for example quantitative control of mass at the *moving phase boundaries*, or an inequality not requiring hard-cut reconstruction. There is no obstruction here for a dense continuum of verticals, uniformly bounded carrier profiles as the mesh shrinks, or a test with a continuous angular weight.
