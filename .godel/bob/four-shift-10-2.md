# Four translates at 3t by joint refitting

Four order-two translates at $3t$ suffice in the [(10,2) lattice comparison](sparse-10-2.md) at $c=39/20$. This replaces the [five-term upper bound](joint-refit-10-2.md). The [rational table](four-shift-10-2.txt) gives $l,10^{10}b_{t,l},10^{10}b_{3t,l},10^{10}h_l$ for $H_y(x)=\sum_l b_{y,l}e^{ilx/25}$ and $h(x)=\sum_l h_le^{ilx/25}$. The only nonzero $h_l$ are:

| $l$ | $-7$ | $6$ | $19$ | $33$ |
|---|---:|---:|---:|---:|
| $10^{10}h_l$ | $-4091085$ | $-5978233$ | $-3407238$ | $-3150199$ |

Use the [finite measurements](sparse-10-2.md#the-two-finite-higher-order-measurements) with the new masks. At $3t$ take $Q_3=P_{2,3t}(-(C_1/C_2)h)$, where $C_j=\cosh(jc)/3$. Thus the measured spline coefficient is $-(C_1/C_2)h_l e^{-l/50}$ at shift $l/25$, not $h_l$ itself. At $t$ take $Q_t$ defined by the spatial sine-kernel deconvolution with $L=8192$ and $N_t=2L$. All sites of $H_t$ satisfy $|l|\le192<L$ and $|l|+L-1<N_t$, so the deconvolution recovers $H_t$ exactly at every phase. The higher measurements at $t$ do not add to the shift count at $3t$.

## Ball verification

Run Sage's Python from the repository root with assertions enabled (Sage 10.9 path on the checking host):

```sh
/opt/sage-10.9/bin/python .godel/bob/check-four-shift-10-2.py
/opt/sage-10.9/bin/python .godel/bob/check-four-shift-10-2.py --L=2048 --margin=.00000023
```

The same table pays at both finite lengths. The following are rounded displays of the certified lower prime price $P_0$, finite $t$ price $T_L$, and upper $3t$ price $U_{\rm up}$; the checker tests the strict margin against the unrounded balls.

| $L$ | $P_0$ | $T_L$ | $U_{\rm up}$ | $P_0-T_L-U_{\rm up}$ |
|---:|---:|---:|---:|---:|
| 8192 | 0.164068618153612427 | 0.160759272231331606 | 0.003308864619233256 | $>4.8\cdot10^{-7}$ |
| 2048 | 0.164068618153612427 | 0.160759515506921613 | 0.003308864619233256 | $>2.3\cdot10^{-7}$ |

The [checker](check-four-shift-10-2.py) uses 128-bit balls and the same full-domain prices as the five-term construction:

- **Prime floor.** At each radial node, bound the minimum of $f_t(z)A(u)+f_{3t}(z)B(u)-z_+u$ on $[0,1]$, with the same $u$ at both heights, $A=2u^2-1$, $B=4A^3-3A$, and $f_y(z)=\sum_l b_{y,l}e^{-l/50}(z+l/25)_+$. A dyadic chord check uses $|\partial_u^2|\le4|f_t|+420|f_{3t}|$. The radial mesh includes every exact ramp knot and 0. The minimum is concave on each affine cell, so the integral of the endpoint chord with weight $e^{-z}$ bounds it from below. Below the first knot the integrand vanishes; beyond $z=18$ integrate the affine floor given by the endpoint minimum and minimum slope, separately. Add $8/9$.
- **Finite $t$ cost.** Use the deconvolved mask coefficients $b_{t,l}/d_{|l|}$ and the trace weights $d_{|l|}e^{-|l|/50}$ in the actual $2L$-point sum, evaluated by a ball FFT. The ideal $t$ norm is not substituted.
- **$3t$ cost.** Fold the entire trace to $\varphi=x/25\in[0,\pi]$ and use the exact CDF masses of its Poisson density on 32768 cells. At each endpoint the same dyadic chord method bounds $\max_\theta\Re(H_{3t}e^{i\theta}+he^{2i\theta})$, with angular curvature $|H_{3t}|+4|h|$. On a spatial cell of width $\Delta$ apply the chord bound at every fixed $\theta$ before taking the maximum. The spatial error is bounded by $\Delta^2\sum_l l^2(|b_{3t,l}|+|h_l|)/8$; the density-skew correction to integrating the endpoint chord is $\Delta(\rho_{\rm left}-\rho_{\rm right})|S_{\rm right}-S_{\rm left}|/8$, where $S_{\rm left},S_{\rm right}$ are the endpoint upper bounds. Neither maximization assumes the maximizing phase varies smoothly. In the dyadic check a cell is discarded only when its chord upper bound plus interpolation error lies below the best sample lower bound plus tolerance; otherwise it is bisected. There is no sample-only acceptance test.

## Search provenance

The search started at $(-9,5,19,33)$ on base `d22e48e0`, checking the cached four fits' lattice sites and sampling prices again. Refit both first columns and the second coefficients with the [fixed-support cone](search-two-shift-10-2.py), using 209 first sites through $\pm192$ (dense through $\pm50$, then even through $\pm125$, then multiples of four). An $L=4096$ local screen nominated $(-8,5,19,33)$ and $(-8,6,20,34)$ for searches with a finer mesh and $L=8192$. The winning support $(-7,6,19,33)$ used the first of these fits to seed active angular cuts, adaptive radial refinement and phase-aligned grouping of the finite $t$ rows. The final fit used base spacings `dz=.011`, `dx=.09`, `tgroup=.07`, second-order Gauss rules, radial cutoff 16 plus the separate affine-tail sample, and seven cut rounds at tolerance `2e-10`. Its floating reprice used `dz=.0015`, `dx=.026`, stationary angular roots and the full finite $t$ sum, before rounding each table entry to a multiple of $10^{-10}$.

| Support (lattice indices) | $L$ | Floating repriced margin in $10^{-6}$, chord / barycenter |
|---|---:|---:|
| $(-9,5,19,33)$ | 4096 | $-0.699$ / $-0.593$ |
| $(-8,5,19,33)$ | 8192 | $-0.626$ / $-0.375$ |
| $(-8,6,20,34)$ | 8192 | $-0.606$ / $-0.231$ |
| $(-7,6,20,34)$ | 8192 | $+0.107$ / $+0.390$ |
| $(-7,6,19,33)$ | 8192 | $+0.354$ / $+0.595$ |

The finite surcharge over the ideal $t$ cost in the winning floating reprice was about $0.0163\cdot10^{-6}$: much smaller than the change from shifting the support and refitting. The cone, cached fits and quadrature are nomination tools only; replaying the checked margin needs just the rational table and Sage, not those inputs or an optimizer.

## Scope

The signed inequality in the fixed shallow comparison is $Q_t+Q_3<-4.8\cdot10^{-7}$ at $L=8192$. At sufficiently large actual failures it is conditional on the two windows being shallow and on taking the iterated errors small for these fixed masks, as in the six-term construction. For instance, a measured sum $\ge-4\cdot10^{-7}$ contradicts joint shallowness once the total error is less than $8\cdot10^{-8}$. No such arithmetic lower bound follows from this certificate. Nor does the search exclude three terms.

## Repricing the signed premise on a shallow model

On the [shared-prime long-layer construction](endpoint-convolution-lift.md) from the 152-slab first law, the limiting $Q_t$ is zero and $-.000891398<Q_3<-.000891397$ on the four new terms. Thus the sufficient lower bound $-4\cdot10^{-7}$ is not a consequence of the failure mean in that relaxation. In fact, **changing the conditional second law alone cannot recover the lower bound**, even if one drops all higher constraints at $3t$. This conclusion fixes the first prime law, all its first translates, the common trace marginal, and the zero-answer completion at $t$.

To see this, use $m=-G_B/C_1$, $v=1-|m|^2$, and the kernels $S(s)=\int e^{isx}m^2\,d\mu$, $R(s)=\int e^{isx}v\,d\mu$ of the [three-shift library calculation](three-shift-library.md). Since the measured multiplier is $-(C_1/C_2)h$, the measured response is **plus** $C_1\Re\int h m_2\,d\mu$, with $m_2=m^2+v g$, $|g|\le1$. Its center is $Q_{3,0}=C_1\sum_l h_l S(l/25)$, realized by the Poisson second law in the long-layer construction. By Cauchy–Schwarz with measure $v\,d\mu$ every disk completion satisfies

$$|Q_3-Q_{3,0}|\le C_1\int |h|v\,d\mu\le C_1\sqrt{R(0)\sum_{k,l}h_k h_l R((k-l)/25)}.$$

The [ball checker](check-three-shift-library.py) certifies $Q_3<-.00008175$ uniformly on this disk, and $Q_3<-.00007548$ for the [five-term mask](joint-refit-10-2.md) by the same argument. The radius bound need not be attained, nor need every disk choice have a shared-prime long-layer realization. Only the Poisson center is used for that example. None is an assertion about arithmetic phases or zeta divisors.
