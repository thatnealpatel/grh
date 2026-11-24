# Six translates in the paired (10,2) separator

Keep the [paired comparison and first masks](paired-10-2.md) at $c=39/20$. There is a sufficient order-two mask at $3t$ with **six distinct translates**, down from the 511 available shifts in the previous construction. It uses the same first masks, and no orders beyond ten at $t$ or two at $3t$. With the finite measurements defined below, the shallow comparison puts their signed higher-order sum below $-1.88\cdot10^{-6}$. Consequently a measured sum $\ge-10^{-6}$ rules out both windows being shallow at a sufficiently large failure. This is a sufficient upper bound on the number of shifts, not a minimum or a prediction of the measured sign.

## The balance to be paid

For $y=t,3t$ let $H_y(x)=\sum_l b_{y,l}e^{ilx/25}$ with the **unchanged** real coefficients from [the paired table](paired-10-2.txt). Write $C_j=\cosh(jc)/3$, $d\mu=dx/[2\pi(1/4+x^2)]$, and $s=2\cos(\pi/12)$. If $H=\sum_l a_l e^{ilx/25}$ is a measured multiplier for order $j$, write $P_{j,y}(H)$ for the [smoothed prime measurement](long-cutoff-moments.md#the-arithmetic-observable) at height $y$ with $B_j$ replaced **before** smoothing by $\sum_l a_l e^{-l/50}B_j(\cdot-l/25)$. Do not use $a_l$ as the spline coefficient. Under the shallow hypothesis the limiting measurement is $-C_j$ times the integral of $\Re(H m_{y,j})$ against $\mu$, with $m_{y,j}$ the conditional moment of $\cosh(jd)e^{ij\theta}/\cosh(jc)$. The trace is the common fixed-ordinate marginal, not an independence assumption about $x$ and $\theta$. The paired failure constraint, using the shared prime phase at $t$ and $3t$, gives

$$P_{1,t}(H_t)+P_{1,3t}(H_{3t})\ \ge\ P_0\ >\ .16405490$$

in the limiting comparison. Here $P_0$ is the [checked lower bound](check-paired-10-2.py) on

$$\frac89+\int e^{-z}\min_{0\le u\le1}\{f_t(z)A(u)+f_{3t}(z)B(u)-z_+u\}\,dz,$$

where $z=D-\log p$, $u=|\cos((t/2)\log p)|$, $f_y(z)=\sum_l b_{y,l}e^{-l/50}(z+l/25)_+$, $A=2u^2-1$ and $B=4A^3-3A$. The minimum uses one shared $u$ for both heights, before taking the phase-free prime limit. The checker retains the angular, radial and tail bounds of the paired proof.

At $t$ write $T_\infty=(C_1/s)\int |H_t|\,d\mu$ for the [limiting price](two-shift-dual-search.md#exact-limiting-price-used-by-the-search) and let $T_L$ be its finite replacement below. At $3t$, for a candidate support coefficient $h(x)$ define

$$S(H,h)=\max_\theta\Re(He^{i\theta}+he^{2i\theta}),\qquad U(h)=C_1\int S(H_{3t},h)\,d\mu.$$

The ideal price $U_\star=(C_1/\sqrt2)\int |H_{3t}|\,d\mu$ need not come from a finite mask. In fact, after rotating $H$ to $r=|H|$, the average over $\theta=\pm\pi/4$ is $r/\sqrt2$ for **every** second coefficient. The choice $h_\star=-H^2/(2\sqrt2|H|)$ (zero at $H=0$) makes the maximum equal to that average, by completing the square in $\cos\theta$.

The quantity to keep positive is

$$P_0-T_L-U(h)=(P_0-T_\infty-U_\star)-(T_L-T_\infty)-(U(h)-U_\star).$$

On these first masks the checker certifies ideal slack $>52.039\cdot10^{-6}$ and bounds the two finite overheads by $1.476\cdot10^{-6}$ and $49.426\cdot10^{-6}$, respectively. At $3t$ the candidate must fit a tight budget, even though the ideal slack is positive. To nominate a sparse candidate, approximate $h_\star$ on the $1/25$ lattice, pricing the transverse (imaginary) error after rotating $H$ to the positive real axis as well as the error in the real quadratic. For example with $k=-\Re(h e^{-2i\arg H})\ge r/4$ the real-quadratic maximum is $k+r^2/(8k)$, so the aligned loss is quadratic near $k=r/(2\sqrt2)$. The final candidate came from pruning and refitting on this support objective; neither the search quadrature nor nonlattice intermediate fits are used below.

## The two finite higher-order measurements

At $3t$ take $h=10^{-8}\sum_l v_l e^{ilx/25}$ with

| $l$ | $-23$ | $-9$ | $5$ | $19$ | $33$ | $55$ |
|---|---:|---:|---:|---:|---:|---:|
| $v_l$ | $-18844$ | $-25047$ | $-57437$ | $-33872$ | $-43702$ | $7938$ |

Measure $Q_3=P_{2,3t}(-(C_1/C_2)h)$. Thus the actual coefficients on translated splines are $-(\cosh c/\cosh(2c))10^{-8}v_l e^{-l/50}$. They are real, nonzero, and at distinct shifts $l/25$; there are no further order-two terms at $3t$ to merge or cancel. The sign follows from the boundary inequality

$$ S(H,h)+\Re(He^{i\theta}-he^{2i\theta})\ge0,$$

obtained by changing $\theta$ to $\theta+\pi$ in the maximum. Apply harmonic extension with identical data on $d=\pm c$ at each fixed $x$. The constant term $S(H_{3t}(x),h(x))$ is bounded and continuous, so the fixed trace marginal applies to it as well as to polynomial constants. This bounds $P_{1,3t}(H_{3t})+Q_3$ from above by $U(h)$ in the comparison.

At $t$ take $L=1024$, $N=2L$ and $\alpha=\pi/(L+1)$. Define the nonnegative spatial kernel

$$K_L(\varphi)=\left|\sum_{a=0}^{L-1}\sqrt{2/(L+1)}\sin((a+1)\alpha)e^{ia\varphi}\right|^2=\sum_{|l|<L} d_{|l|}e^{il\varphi},$$
$$d_l=\frac{(L-l)\cos(l\alpha)+\sin((l+1)\alpha)/\sin\alpha}{L+1}\quad(0\le l<L).$$

For $0\le p<N$, put $\varphi_p=2\pi p/N$, $D_p(x)=K_L(x/25-\varphi_p)/N$, and $V_p=\sum_l (b_{t,l}/d_{|l|})e^{il\varphi_p}$. Orthogonality modulo $N$ gives $\sum_p D_p V_p=H_t$ **exactly**: A mode from the first mask has $|l|\le40$ and cannot differ by $N$ from a kernel mode with $|l|<L$. In particular the deconvolution does not change the accepted first price.

Let $w_a=\sqrt{2/12}\sin((a+1)\pi/12)$ for $0\le a\le10$ and $s_j=2\sum_{a=0}^{10-j}w_aw_{a+j}$ for $1\le j\le10$, so $s_1=s$. Put

$$G_j(x)=\frac{s_j}{s}\sum_{p:\,V_p\ne0} D_p(x)|V_p|(V_p/|V_p|)^j,
\qquad A_t(x)=\frac1s\sum_p D_p(x)|V_p|.$$

Each $G_j$ has finite real Fourier coefficients: $V_{N-p}=\overline{V_p}$ and the translated spatial kernels pair by conjugating their Fourier coefficients. The fixed points $p=0,N/2$ have real $V_p$ and real kernel coefficients. Now $G_1=H_t$, and $A_t+\Re\sum_{j=1}^{10}G_j e^{ij\theta}$ is a positive combination of rotated angular sine squares, hence nonnegative on the circle. Harmonic extension bounds $P_{1,t}(H_t)+Q_t$ by $T_L=C_1\int A_t\,d\mu$, where

$$Q_t=\sum_{j=2}^{10}P_{j,t}((C_1/C_j)G_j),\qquad
T_L=\frac{C_1}{sN}\sum_{p=0}^{N-1}|V_p|\left[1+2\sum_{l=1}^{L-1}d_l e^{-l/50}\cos(l\varphi_p)\right].$$

The formula for $T_L$ uses the exact trace Fourier weights $e^{-|l|/50}$. No limit in $L$, $N$, or the number of translates is needed. All higher masks at $t$ are fixed and have at most 2047 shifts per order, among $l/25$ for $|l|<1024$; their size does not add to the count at $3t$.

## Verification and scope

Run `sage .godel/bob/check-sparse-10-2.py` at the root with assertions enabled. It replays the paired first-price floor, encloses $T_L<.16072313$ and $U(h)<.00332990$, and checks $P_0-T_L-U(h)>1.88\cdot10^{-6}$ directly using the unrounded bounds (tighter than separately pricing the overheads).

Here is the quadrature bound behind the replay. All three masks have real coefficients on the same lattice, so the trace integrands are even and $2\pi$-periodic in $\varphi=x/25$. Periodizing $\mu$ sums its Fourier coefficients $e^{-|l|/50}$ and folding to $[0,\pi]$ gives density $\rho(\varphi)=\sinh(1/50)/[\pi(\cosh(1/50)-\cos\varphi)]$. This includes the full real-line tail. The checker uses $8192$ equal cells with exact masses from the CDF $(2/\pi)\arctan[\tan(\varphi/2)/\tanh(1/100)]$. At each spatial node it bounds $S$ above by the maximum of the $1024$ angular evaluations plus $(|H|+4|h|)\pi^2/(2\cdot1024^2)$, since the angular derivative at a maximizer vanishes. On each spatial cell of width $\Delta$, interpolate the *endpoint upper bounds* and add $\Delta^2\sum_l l^2(|b_{3t,l}|+10^{-8}|v_l|)/8$. This follows by applying the scalar chord error to each fixed angular evaluation **before** maximizing; no smoothness of the maximizing phase is assumed. When the endpoint bounds are $a,b$ and the mass is $m$, the integrated chord is at most $m(a+b)/2+\delta|b-a|$, with $\delta=\Delta(\rho_{\rm left}-\rho_{\rm right})/8$ by pairing the two halves of the cell under the decreasing density. The norm prices use the same chord estimate with $h=0$. For a lower norm bound on a cell, take the modulus of the integrated complex chord, bounded below by $m|(H_{\rm left}+H_{\rm right})/2|-\delta|H_{\rm right}-H_{\rm left}|$, then subtract the integrated complex interpolation error. All evaluations and error sums use ball arithmetic. There is no angular or spatial sample-only test and no dropped Fourier tail of the ideal $h_\star$ to estimate: The checker prices the stated rational polynomial directly.

Adding the two strip inequalities gives the signed upper price $Q_t+Q_3\le T_L+U(h)-P_0$ in the fixed comparison. At an actual real high-endpoint failure use $t=2q^{3/5}$ and $D=\log((9\log q/5)^2)$. If neither window $|\gamma-y|\le (2/\epsilon)\log D$, $y=t,3t$, contains a right zeta zero with $D(\beta-1/2)>39/20$, the fixed finite masks have the same comparison up to the [iterated smoothing and trace errors](masked-cutoff.md#what-the-shallow-hypothesis-buys). Fix $\epsilon$ sufficiently small for these particular masks, then take $q$ sufficiently large that the total signed-price error is less than $8\cdot10^{-7}$, before comparing with $-10^{-6}$. The windows include their centers. This supplies a shorter conditional screen, not a bound on $Q_t+Q_3$ from the failure hypothesis alone. The remaining arithmetic question is whether the signed lower bound holds at failures; improving the number six further is a separate optimization problem.
