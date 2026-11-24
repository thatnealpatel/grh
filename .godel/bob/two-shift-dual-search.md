# Two-shift signed-dual probe at $(10,2)$ and $c=39/20$

**Decision:** No strict separator was found. The best sampled relaxed objective was about $-3.41\cdot10^{-5}$ at shifts $(.16,1.16)$, and repricing its coefficients without trace cell fusion gives about $-4.3\cdot10^{-5}$. This searches the signed dual, not the common-law primal. It does not exclude arbitrary first supports, all pairs of second shifts, or even the sampled optima rigorously. The accepted [one-shift obstruction](single-shift-10-2.md) and [many-shift separator](paired-10-2.md) remain the endpoints.

## Exact limiting price used by the search

Use the normalization, fixed-spline limit, and signs in [the many-shift separator](paired-10-2.md) and [the translated comparison](translated-cutoff-budget.md). Set $C_j=\cosh(jc)/3$, $s_{10,1}=2\cos(\pi/12)$, and $d\mu=dx/(2\pi(1/4+x^2))$. Choose independent real finite first multiplier coefficients $a_{y,k}$ at each height $y=t,3t$, with matching first splines

$$H_y(x)=\sum_k a_{y,k}e^{ikx},\qquad f_y(z)=\sum_k a_{y,k}e^{-k/2}(z+k)_+.$$

Choose a real two-coefficient mask $h(x)=h_1e^{isx}+h_2e^{irx}$ at $3t$. Converting back to the original signed order-two measurement, its Fourier multiplier is $-(C_1/C_2)h$, whose shift-$s$ spline coefficient is $-(C_1/C_2)h_1 e^{-s/2}$, and similarly at $r$. In particular, *negative* coefficients in the search are positive measured coefficients. Indeed, a measurement contributes $-C_j\Re(H_j e^{ij\phi})$ at the boundary; changing the variable to $\theta=\phi+\pi$ gives positive sign at order one and negative sign at order two.

On the zero-higher-answer path the normalized prime floor is

$$P=\frac89+\int e^{-z}\min_{0\le u\le1}\bigl(f_t(z)A(u)+f_{3t}(z)B(u)-z_+u\bigr)\,dz,\qquad A=2u^2-1,\quad B=4A^3-3A.$$

The failure-mean multiplier is normalized to one. A positive multiplier can be scaled to one because all trace prices are positively homogeneous. A zero multiplier cannot separate: the pointwise choice $u=1/\sqrt2$ gives $A=B=0$, and the trace support price is nonnegative by angle averaging. The strict discriminator in this normalization is

$$M=P-\frac{C_1}{s_{10,1}}\int |H_t|\,d\mu-C_1\int \max_{\theta\in\mathbb R}\Re\bigl(H_{3t}e^{i\theta}+h e^{2i\theta}\bigr)\,d\mu>0.$$

The second integral is the pointwise support price for the actual finite masks at $3t$. For each $x$ the angular polynomial with the strip factors $\cosh(jd)/\cosh(jc)$ is harmonic in $(d,\theta)$, so its upper bound for $|d|\le c$ is exactly the circle maximum at $d=\pm c$. There is no tail truncation or extra second translate in this exact expression.

The first integral is the **infimum** over all finite degree-two-through-ten multipliers at $t$ for the given first mask. The accepted tilted twelve-point angle grid has first moment of modulus $1/s_{10,1}$ and zero moments at orders two through ten. At each $x$ orient it to attain $|H_t(x)|/s_{10,1}$ at first order; this lower bounds the circle maximum regardless of the higher multipliers. For the matching upper limit, use the accepted sine-polynomial construction and its kernel $D_L$ as follows. This also works for nonlattice finite first supports:

* For each real first shift $k_i$ introduce a torus coordinate $\xi_i=k_i x$, and take the product of the nonnegative sine kernels $D_L(\xi_i-\theta_{p_i})$ on the equally spaced angle grids. Normalize the product by the number of grid points, taking the one-coordinate grid size $N>2L$. The weights sum to one; the weighted mean of $e^{i\theta_{p_i}}$ is $d_1e^{i\xi_i}$, where $d_1=\cos(\pi/(L+1))$.
* At each grid point use $V=\sum_i(a_{t,k_i}/d_1)e^{i\theta_{p_i}}$. If $Q$ is the [degree-ten sine square](finite-cutoff-budget.md) of constant term one and first cosine coefficient $s_{10,1}$, then $|V|[1-Q(\theta+\arg V+\pi)]/s_{10,1}$ has first term $\Re(Ve^{i\theta})$ and is at most $|V|/s_{10,1}$. Use zero when $V=0$. Weighted averaging yields $H_t$ identically at degree one. The higher coefficients are finite sums of frequencies $\sum_i n_i k_i$; conjugation of all grid coordinates pairs the values and gives real multiplier coefficients. The reproduced first mask and the second mask at $3t$ have not changed.
* The cost excess over $(C_1/s_{10,1})\int|H_t|d\mu$ is at most
  $$(C_1/s_{10,1})\sum_i |a_{t,k_i}|\left(d_1^{-1}-1+\sqrt{2(1-d_1)}\right).$$
  Indeed the kernel expectation of $|e^{i\theta_{p_i}}-e^{i\xi_i}|^2$ is $2(1-d_1)$, so the triangle inequality and Cauchy–Schwarz give this bound uniformly in $x$. The excess tends to zero with $L$. For lattice data a single kernel, deconvolving each shift by its own $d_{|k_i|/.04}$ as in the accepted proof, is more economical. In either construction $L$ is fixed before the conductor limit.

Thus one must not choose extra second translates at $3t$ merely to realize the ideal price at $t$. A rigorously positive $M$ with fixed finite first supports and a two-term $h$ would suffice, after budgeting the finite $t$ construction error and the existing limiting errors. These identities do not supply such a margin.

## Numerical method and scope

For each previously selected pair $(s,r)$, [the search](search-two-shift-10-2.py) solves a convex conic problem over the first coefficients and the two unrestricted signed coefficients of $h$. The outer choice of $(s,r)$ is nonconvex and sampled separately. The shift unit in the script is $.04$. First supports are finite subsets of that lattice, either both optimized or with the accepted first multiplier at $t$ fixed.

* The radial grid includes all first knots and zero. The terms being minimized are affine in $z$ on each knot-free cell, including the right tail after $z=10$, so the minimum is concave there. Replacing a cell by its exact $e^{-z}$ barycenter would give an **upper** bound on $P$; the exact weighted chord would give a lower bound on a finite cell. On the tail one can lower bound the minimum at $z$ by the minimum at $10$ plus $(z-10)$ times the minimum slope. The optimization uses the barycenter and includes the tail mass $e^{-10}$ at $z=11$. Its exponents and angular cuts are floating point.
* For lattice shifts the trace integrands are even and periodic, so the search folds the entire Cauchy measure onto $[0,\pi/.04]$, with density $(.04/\pi)\sinh(.02)/(\cosh(.02)-\cos(.04x))$. Taking exact cell means of the Fourier columns before evaluating the convex trace price would **lower** that price by Jensen. The implementation uses unenclosed 12-point Gauss cell integration. In both integrals angular cuts start with a finite grid, then add numerically located extrema. A finite list of angular constraints relaxes the discretized problem. Supporting those directions with enclosed integrals and a checked conic bound would require a separate checker.
* `--check` leaves the coefficients fixed, computes the prime and trace extrema via real roots of the stationary polynomials rather than angular cut exchange, and integrates the trace at the actual Gauss nodes in finer cells. It reports prime chord and barycenter estimates with target spacings `dz=.005`, `dx=.0125` (the latter is increased on the far trace cells). It is independent floating repricing, not a ball enclosure.

`Cut objective` below is $8/9$ minus Clarabel's reported minimization objective, with the fixed first-price constant subtracted where applicable. It approximates an optimistic value **only for that specified support and those cells**. Restricting shifts removes admissible choices and goes in the other direction. Neither these estimates nor solver residuals are a rigorous upper bound on the problem in the heading.

| First support per height (real shifts) | Completed pairs | Best pair | Best cell reprice | Cut objective |
|---|---:|---:|---:|---:|
| $t$ fixed; $3t$ in $[-1.6,1.6]$ by $.04$ | 150 | $(0,1)$ | $-.00005989234$ | $-.00005978394$ |
| Both free, $[-2.2,2.2]$ by $.04$ | 8 | $(.20,1.20)$ | $-.00004039284$ | $-.00004039182$ |
| Both free, $[-3.6,3.6]$ by $.04$ | 6 of 7 (timeout) | $(0,1)$ | $-.00004237777$ | $-.00004237667$ |
| Both free, 143 tapered shifts through $\pm3.68$ | 9 | $(.12,1.12)$ | $-.00003653938$ | $-.00003653833$ |
| Both free, 209 tapered shifts through $\pm7.68$ | 3 | $(.16,1.16)$ | $-.00003413921$ | $-.00003408867$ |

Every completed cut objective was negative. All completed solves in the table reported `Solved`, except $(.08,1.04)$ in the 143-shift run, which reported `AlmostSolved` with cut objective $-3.98900\cdot10^{-5}$.

The fixed-$t$ outer scan used pairs from $[-1,2.6]$ by $.20$ and gaps in $[.20,2.40]$. The final three pairs were $(.12,1.08),(.16,1.16),(.20,1.20)$; their cut objectives were $-3.63339,-3.40887,-3.54742$ in units of $10^{-5}$. On the best pair `dx=.13`, `dz=.017`, tolerance $3\cdot10^{-10}$, and nine cut rounds gave `Solved` with reported primal and dual residuals $2.94\cdot10^{-10}$ and $2.26\cdot10^{-14}$. The coefficients of $h$, in order, were about $-.001018011621,-.0005809242445$. Repricing with the finer original integrands gave:

| $P$ chord | $P$ barycenter | $t$ cost | $3t$ cost | Chord margin | Barycenter margin |
|---:|---:|---:|---:|---:|---:|
| .1640096107805 | .1640142324439 | .1606695057398 | .0033856035106 | $-4.54985\cdot10^{-5}$ | $-4.08768\cdot10^{-5}$ |

**Controls:** Four coincident pairs (one effective translate), shifts $0,.20,.40,.80$, gave negative fixed-$t$ objectives, consistent with the accepted all-real one-shift result. Allowing the unconstrained optimal *ideal* second mask at $3t$ for the accepted paired first weights gives a floating margin $+5.59775\cdot10^{-5}$ (using $C_1/\sqrt{2}$ times the norm at $3t$), consistent with the separately certified positive many-shift margin. Neither control is a substitute for that accepted evidence.

### Replay

From base `0354c85bef9a9ecc79ecb59095ba01eaf3514596` with this script present, use Python 3 with NumPy, SciPy, Clarabel (`faer` backend); the runs used Python 3.14.7, NumPy 2.5.5, SciPy 1.18.1, Clarabel 0.11.1. Save files are generated by the commands and are not checker inputs external to the replay. The outer scan is slower than the three-pair run.

```sh
export OPENBLAS_NUM_THREADS=1
s=.godel/bob/search-two-shift-10-2.py
python "$s" --fixed-t --stride=1 --range=40 --dx=.18 --dz=.03 --iter=5 \
  --min-shift=-25 --max-shift=65 --shift-step=5 --min-gap=5 --max-gap=60
python "$s" --stride=1 --range=55 --dx=.10 --dz=.02 --iter=10 --tol=2e-10 \
  --pairs='0,30;-5,25;0,25;5,35;5,30;0,35;10,40;25,55'
# The following 181-shift run completed all but the last pair within its time limit.
python "$s" --stride=1 --range=90 --dx=.11 --dz=.018 --iter=10 --tol=2e-10 \
  --pairs='0,30;5,35;10,40;-5,25;0,25;25,55;0,20'
python "$s" --stride=1 --range=92 --taper --dx=.11 --dz=.018 --iter=10 --tol=2e-10 \
  --pairs='3,28;5,30;2,26;0,23;3,25;-1,25;-5,20;4,27;0,30'
python "$s" --stride=1 --range=192 --taper --dx=.13 --dz=.017 --iter=9 --tol=3e-10 \
  --pairs='3,27;4,29;5,30' --save /tmp/two-shift-best.npz
python "$s" --check /tmp/two-shift-best.npz
python "$s" --control
python "$s" --fixed-t --stride=1 --pairs='20,20;5,5;0,0;10,10'
```

**Next discriminator:** Seek an all-first-support bound for the promising positive-measured-coefficient region around $(.16,1.16)$, or a positive strictly repriced candidate there with nonlattice first supports. The exact $t$ price above eliminates optimizing the order-two-through-ten masks independently. An exclusion for a finite selected lattice, even if rigorously replayed, would not settle the arbitrary-pair question. No arithmetic signed-measurement premise for actual failures has been proved here.
