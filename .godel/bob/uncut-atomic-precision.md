# Precision needed to recover the uncut charge from atomic traces

Use the two four-depth assignments for the [uncut charge $X$](uncut-trace-normal.md), with the same $q,t,R,D,\lambda$, Euler coefficients through $2V$, and sufficiently small fixed $\epsilon$. Write $V=R^2$, $D=\log V$. There are local reflected **atomic** arrays on the whole ordinate axis with exactly the same counting marginal, for which, at every sufficiently large sample:

* Each entire translated value trace at $a=1/D$ differs from the **common continuous trace** by $O(R e^{-\kappa R/D})$ in absolute supremum norm.
* For $1<\sigma\le2$, each exterior Poisson trace differs from the corresponding **finite Euler trace** by $O(R e^{-\kappa R/D})$, uniformly in $\sigma$ and translation.
* The two uncut $X$'s differ by more than $.011$. These include the price and the original complex smoothing, not just a carrier harmonic.

Here $\kappa>0$ is fixed, not an optimal exponent. The arrays can even be chosen simple, with identical critical-line atoms of spatial mean density $.52\lambda$, as described below. They depend on the sample. The earlier [constant-layer lattice](interior-trace-depth-transfer.md) gives exponential closeness for a *cut* charge; moving that layer does not change the uncut integral.

## Quantize a coupling, not the two marginals

Write $u_i^\pm$ for the positive total densities in units of $\lambda$ in the uncut construction: Scaled depths $c_i=0,.99,1.01,40$, baseline $(.32,.24,.21,.23+U(v-1))$, and perturbation $\pm.04 h_i\cos((D-2)x)$ there. Their common sum $H=1+U(v-1)$ is pointwise the same. Use the sixteen pair intensities

$$ d_{ij}(x)=\frac{\lambda}{2}\frac{u_i^+(x)u_j^-(x)}{H(x)},\qquad M_{ij}(x)=\int_0^x d_{ij}(w)\,dw. $$

At each $M_{ij}^{-1}(n+1/2)$, $n\in\mathbb Z$, put a reflected pair at $c_i/D$ in the plus array and at $c_j/D$ in the minus array (two coincident line atoms when the respective depth is zero). Both arrays thus have the same counting measure on ordinates. The row and column sums are precisely the desired continuous **pair** intensities. The construction gives $O(R)$ atoms per unit interval and bounded discrepancy per cell relative to its own intensity on any interval.

For some $\delta\in(0,.005)$ independent of $q$, on the closed strip $|\Im z|\le s=\delta/D$ every $d=d_{ij}$ is holomorphic with $\Re d\ge c_0 R$ and $|d|\le C R$, for fixed $c_0,C>0$. Indeed all four $u_i^\pm(x)$ are between $.07$ and $1$ eventually on the real axis, by the [limiting coefficients](uncut-trace-normal.md#why-the-normal-term-is-not-redundant-in-the-continuous-test). In $U(v-1)$ the **sum of absolute coefficients** before the cosines is $<10^{-7}$ eventually, by the [split at $R$](interior-trace-depth-transfer.md#transfer-with-no-change-in-the-data). All frequencies are at most $D+\log 2\le2D$. Thus each density and $H$ change by $O(e^{2\delta}-1)$ from their values at $\Re z$, uniformly: For each cosine use $|\cos(\omega z+\theta)-\cos(\omega\Re z+\theta)|\le e^{|\omega\Im z|}-1$. Choose $\delta$ small in the quotient, using $H$ bounded away from zero and $\lambda\asymp R$. Real-axis positivity alone without analytic control would not justify the shift.

## One error bound for the measured kernels and the target

For $M'=d$ as above and $K$ holomorphic on a neighborhood of the closed strip with uniform decay $O((1+|\Re z|)^{-1-\eta})$, set $L_s(K)=\sup_{|y|\le s}\int |K(x+iy)|\,dx$. The periodization $\sum_{n\in\mathbb Z}K(M^{-1}(n+\theta))$ is continuous in $\theta$, by decay and $M'\asymp R$ on the axis. Its $k$th Fourier coefficient is

$$ \int K(x)d(x)e^{-2\pi i k M(x)}\,dx . $$

The constant coefficient is the wanted continuous integral. For $k\ne0$ move the contour to $\Im z=-s\,\mathrm{sgn}(k)$. Since $\Im M(x+iy)=\int_0^y\Re d(x+iv)\,dv$, the exponential decays there by at least $e^{-2\pi |k|c_0 R s}$ and does not grow on the connecting segments. Summing the absolute Fourier coefficients recovers the periodization, including at $\theta=1/2$, and gives

$$ \left|\sum_n K(M^{-1}(n+1/2))-\int Kd\right|
 \le 2CR\,L_s(K)\,\frac{e^{-2\pi c_0 R s}}{1-e^{-2\pi c_0 R s}}. \tag{1} $$

For comparison, on these *same nodes*, integrating the second derivative of $K\circ M^{-1}$ in the mass variable gives a composite midpoint error $\ll (\|K''\|_1+D\|K'\|_1)/R$ (use $d\asymp R$, $|d'|\ll RD$). For the interior kernels this is $O(D^2/R)$. It already proves vanishing absolute error; (1) uses the available strip of analyticity to give a different precision scale.

For the translated interior trace the pair test is the sum of two translated $k_w(z)=w/(w^2+z^2)$, $w=(1\pm c_i)/D$. Each $|w|\ge .01/D>2s$, even on the shallow side. Hence $|k_w(x+iy)|\le (4/3)|w|/(x^2+w^2)$ for $|y|\le s$, also for a negative numerator. Translation does not change the $L^1$ bound. For the exterior trace take $w=\sigma-1/2\pm c_i/D$; these widths are eventually $>1/4$. The continuous traces are respectively common and the finite Euler values by the uncut construction. Explicitly the exterior target at $y$ is $\pi\lambda-\sum_{n\le2V}\Lambda(n)n^{-\sigma}\cos((t+y)\log n)$, not the completed zeta trace. No sharp truncation in the ordinate variable is made in (1). More generally, the error from the finite Euler functional $\lambda\int vf$ is $O(R e^{-\kappa R/D}L_{(40+\delta)/D}(f))$ for strip tests with the stated decay and holomorphy there: Apply (1) to the sum of the two imaginary shifts. This is an estimate in a specified test norm, **not** exact analytic equality after rounding.

For $X$ only the deep rows (or columns) count, once each; take $K(z)=(f(z+ib)+f(z-ib))/2$ for $b=c_i/D$, with $f=-(g_\epsilon B^2+2\alpha k_A)/R$ as in the uncut test. Then $L_s(K)=O_\epsilon(1/R)$ uniformly as $D\to\infty$. In fact on $|\Im z|\le(40+\delta)/D$, the two endpoint exponentials in $B$ have moduli bounded by $e^{(40+\delta)/2}$; the [two-half formula](weil-phase-bands.md#an-exact-phase-that-separates-the-two-halves) bounds each remaining factor by $O(1/(1+|\Re z|))$ since its denominator has real part $>1/4$ eventually. The complex smoothing is bounded there, and the price poles at $\pm iA$ are separated. Thus (1) changes either $X$ by $O_\epsilon(e^{-\kappa R/D})$. The continuous gap has iterated limit $.011414\ldots$ (large $D$ first, then small $\epsilon$), which proves the stated strict gap.

## Keeping the critical-line atoms simple and fixed

In the first coupling the line in a model can get two atoms at one ordinate. If line simplicity is imposed, exact ordinate multiplicities could reveal such a change of allocation. To remove that issue, keep density $.52\lambda$ on the line in both models and make the four varying layers **all off-line**, at $c=.1,.99,1.01,40$. Use respective baselines $.22,.18,.05,.03+U(v-1)$ in units of $\lambda$. Write $m=(D-2)/D$, $C_c=\cosh(mc)$, and keep the original deep coefficients $h_{1.01}=1$, $h_{40}=-\kappa_0$ with $\kappa_0=\cosh(.01m)/\cosh(39m)$ and $S=C_{1.01}-\kappa_0 C_{40}$. Use the same perturbation $\pm.04 h_c\cos((D-2)x)$, but solve the two shallow equations with

$$ h_{.99}=\frac{(1-\kappa_0)C_{.1}-S}{C_{.99}-C_{.1}},\qquad h_{.1}=-1+\kappa_0-h_{.99}. $$

The coefficient sum, full $C_c$ moment, and deep relative $\cosh((c-1)m)$ moment still vanish. The baselines still give $\lambda\int vf$ (constant layers shift freely); the three cancellations give the common marginal, exterior pairing, and signed interior trace as before. At $m=1$ the shallow coefficients are respectively $4.120$ and $-5.120$ to three decimals, so all four densities are eventually $>.009$. Only the two deep layers enter $X$, with precisely the same **difference** as before. The common interior trace for the simple variant is its own continuous trace, not the original baseline's trace. No absolute value of $X$ has been carried over.

Couple only the four off-line layers in (1), with their common sum $H=.48+U(v-1)$ in the denominator. Quantize the common line density as a single lattice of spacing $1/(.52\lambda)$; (1) applies to its constant intensity too. Choose the offsets $\theta$ of the sixteen pair quantizers in succession: Only countably many offsets meet an ordinate of any earlier cell or of the common line lattice. The estimate is uniform in the offsets. Each array is now simple; the two atoms at each off-line ordinate have distinct real parts. The line proportion by spatial mean is $.52$ since the cosine terms of the total intensity have zero mean and cumulative rounding costs $O(1)$ per cell. This is a property of local models continued on the ordinate axis, not an asymptotic assertion about zeta.

**Decision for the failure test.** If the marginal is exact but the value and exterior Poisson data have absolute error allowances of order $CR e^{-\kappa R/D}$ with sufficiently large $C$, the common continuous data are admissible observations for both arrays. Any one estimate on these data errs by more than $.0055$ on at least one array; any valid upper bound for both has slack $>.011$ on the smaller one. Exact meromorphic identification is consistent with this. The gap is not a threshold crossing, does not rule out all useful upper bounds, and supplies no zeta estimate. Test the one-sided relative-depth remainder with the actual signed weight and a single budget at failures, not generic stable inversion of the value trace.
