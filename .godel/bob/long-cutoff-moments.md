# A doubled cutoff tests shallow phase alignment at one height

Use the [real high-endpoint failure](sampled-principal-peaks.md#if-the-first-harmonic-barely-passes-price-the-third), with $R=(9/5)\log q$, $V=R^2$, $D=\log V$, and $t=2q^{3/5}$. The [two-height disjunction](common-filter-pair.md) changes the height while keeping the cutoff. Here **keep $t$** and change the cutoff from $V$ to $V^2$. This doubles the *zero* phase, not the prime phase. It gives a prime measurement which can decide whether to ask for a substantially deeper zero census at the same height.

Write $d=D(\beta-1/2)$, $x=\gamma-t$, and $J=(2/\epsilon)\log D$. Let $P_2$ be the real smoothed sum below, with normalization $R^{-3}$, not $V^{-2}$. At every sufficiently large failure, for each row at least one alternative holds:

| A right zeta zero with $d>c$ and $|x|\le J$ | Or the prime measurement must satisfy |
|---|---|
| $c=1.50$ | $-3.36<P_2<-.31$ |
| $c=1.54$ | $-3.64<P_2<-.066$ |

The center **is included**. Fix sufficiently small $\epsilon>0$ before taking $q$ large. In particular a nonnegative $P_2$ forces depth $>1.54$ in the same window. The assertion is not an unconditional increase in the guaranteed single-height depth. It does not require that $3t$ be free of zeros or that the two prime sums be independent.

## The arithmetic observable

Use the [signed smoothing kernel](opposite-phase-bands.md#use-the-unused-half-of-the-log-axis) $k_\epsilon$ with bilateral transform $g(w)=\exp(1-\cos(\epsilon w))$, mass one, and $|k_\epsilon(y)|\ll \epsilon^{-1}\exp(-|y|/\epsilon)$. Put $h_2(r)=r_+^2/2-r_+$. For $P_2$ convolve the following **whole weight** in $y$ with $k_\epsilon$:

$$ B_2(y)=h_2(2D-y)-3h_2(D-y)+3h_2(-y)-h_2(-D-y),\qquad
P_2=\frac{1}{R^3}\sum_n\Lambda(n)\cos(t\log n)(k_\epsilon*B_2)(\log n). $$

One may restrict this smoothed sum to primes $p\le V^{5/2}$ at cost $o_\epsilon(1)$ (proof below). Do **not** replace the convolution by its unsmoothed value at positive $y$: The total absolute prime scale at the long endpoint is of order $R$, not $1$.

For the proof and the extension, use each fixed integer $j\ge1$. Let $h_j(r)$ be zero for $r<0$ and otherwise

$$ h_j(r)=\sum_{l=0}^{j-1}(-1)^l {j-1\choose l}\frac{r^{j-l}}{(j-l)!} .$$

Define $B_j(y)=\sum_{k=0}^{j+1}(-1)^k{j+1\choose k}h_j((j-k)D-y)$ and $P_j$ as above with $R^{j+1}$ in the denominator. These subscripts index **radial cutoffs**, not the heights of the two-height test. $B_1$ is the original even tent. At a failure $P_1\ge p-O(\epsilon)-o(1)$, $p=47/81$, by the linked smoothing estimate and the original mean $\ge8/9-o(1)$. The other $P_j$ are not supplied by that mean.

The $(j+1)$st difference kills the degree-$j$ polynomial below $-D$, so $B_j$ is supported on $[-D,jD]$ and $\|B_j\|_\infty\ll_j 1+D^j$. For $n>V^{j+1/2}$ the convolution is $\ll_{j}(1+D^j)(V^j/n)^{1/\epsilon}$. Chebyshev and partial summation bound the normalized tail by $O_{j,\epsilon}((1+D^j)R^{j-1/\epsilon})=o(1)$ for $1/\epsilon>j$. In the truncated sum the powers of exponent at least two cost $O_j((1+D)^{j+2}R^{-1/2})$ by the same supremum bound and Chebyshev at the square root of the cutoff. Thus the measurements only require finite prime sums to the precision claimed.

## One common phase on the divisor

With $w=\beta+ix$, the Mellin multiplier of the whole smoothed, normalized weight is

$$ K_j(w)=\frac{g(w)}{R^{j+1}} e^{jDw}(1-e^{-Dw})^{j+1}\frac{(1-w)^{j-1}}{w^{j+1}} . $$

Indeed integrate each truncated power first on $\Re w>0$. The apparent pole at zero is removable. Apply the contour of the [even tent identity](opposite-phase-bands.md#use-the-unused-half-of-the-log-axis), from $2$ to $-1/4$, to get $P_j=-\Re\sum_\rho K_j(w)+o_\epsilon(1)$. On the new vertical the exponential polynomial costs $O_j(V^{1/4})$, the rational factor is $O_j((1+x^2)^{-1})$ (with $x$ the integration ordinate there), and the integrated logarithmic-derivative bound is $O(\log t)$. Division by $R^{j+1}$ therefore suffices, even for $j=1$. The pole term at $1-it$ vanishes in the limit by double exponential decay of $g$; the same separated horizontals as for the even tent work at each fixed $q$. For $|x|>J$ the whole residue sum is $o_\epsilon(1)$: The exponential polynomial costs at most $O_j(V^j)$, while $|g|\le\exp(1-D^2/4)$ and $\sum_\rho(1+x^2)^{-1}=O(R)$.

Argue under the alternative that there is **no** right zero with $d>c$ inside $J$, with $c$ fixed. Reflection gives $|d|\le c$ on the whole window. Define

$$ k(x)=(1/4+x^2)^{-1},\qquad \phi(x)=Dx-2\arg(1/2+ix),\qquad M=R^{-1}\sum_{|x|\le J} k(x). $$

Then $M=1/3+o_\epsilon(1)$. In the completed Hadamard trace at $\sigma=1+1/D$ the full Poisson sum is $(\log t)/2+O(D^2+1)$ by the absolutely convergent Euler series and Stirling. The $|x|>J$ part is $o_\epsilon(R)$ by the unit counts $O(\log(2+|t+x|))$. Inside, the width $\sigma-\beta=1/2+O_c(1/D)$ gives $(1+O_c(1/D))k(x)/2$. Finally $\log t/R\to1/3$. This uses neither an asymptotic local zero count at scale $1/D$ nor a global zero-free strip.

Let $\mathbb E_0$ count all zeros in the window, with probability proportional to $k(x)$ and with multiplicities. For fixed $j,c$ we obtain the simultaneous comparison

$$ P_j=-M\,\mathbb E_0[\cosh(jd)\cos(j\phi)]+e_j,\qquad
\lim_{\epsilon\downarrow0}\limsup_{q\to\infty}|e_j|=0 \tag{1} $$

along the no-deep cases (equivalently the errors are uniformly arbitrarily small in this order). In fact $(1-e^{-Dw})^{j+1}=1+O_{c,j}(1/R)$ there. At $w_0=1/2+ix$, $1-w_0=\bar w_0$, so the rational factor is **exactly** $k(x)e^{-2ij\arg w_0}$. Moving it from $w$ to $w_0$ costs $O_{j,c}(k(x)/D)$ by differentiation, with $\Re w\ge1/4$ eventually. Removing $g$ costs arbitrarily little in (1): On $|x|\le B$ it tends uniformly to one as $\epsilon\downarrow0$, and on the complement the cost is $O_{c,j}(1/B)+o(1)$ by unit counts, $|g|\le e$, and $e^{jd}\le e^{jc}$. The normalization leaves $e^{jd}/R$ times the carrier. Averaging with the mirror replaces $e^{jd}$ by $\cosh(jd)$ with the same phase, also valid on the line. The common $k$ for *all* orders is the reason for the numerator $(1-w)^{j-1}$.

## Price the second measurement before asking for a deeper census

Normalize the moments $m_j=\mathbb E_0[\cosh(jd)\cos(j\phi)]/\cosh(jc)$. Any nonnegative even trigonometric polynomial $b_0+\sum b_j\cos(j\theta)$ satisfies $b_0+\sum b_j m_j\ge0$. Its harmonic extension to the periodic strip $|u|\le c$ with identical data on both boundaries is obtained by replacing $\cos(j\theta)$ by $\cosh(ju)\cos(j\theta)/\cosh(jc)$. Apply the minimum principle on the cylinder and then evaluate at $(d,\phi)$. Thus positivity applies **before** summing over the depth distribution.

In particular $|m_2|\le1$ and $m_2\ge2m_1^2-1$: Use $(\cos\theta-m_1)^2$ in the extension. At failure $m_1\le-3p/\cosh c$ up to errors vanishing in the stated order. By (1) the resulting limiting lower and upper prices on $P_2$ are

$$ -\cosh(2c)/3,\qquad -\frac{\cosh(2c)}{3}\left[2\left(\frac{3p}{\cosh c}\right)^2-1\right]. $$

The latter is $-.3193015\ldots$ and $-.0667239\ldots$ in the respective rows. The price is sharp at the level of these angular moments: At $|d|=c$ choose $\cos\phi=-3p/\cosh c$ for the upper price; a mixture of $\cos\phi=\pm1$ with that same mean gives the lower price. This does not realize the prime or zero data. In particular a longer test of nearly zero is *not* the shallow baseline at a failure in either row.

**What the shorter prime tests leave free.** Even fixing all prime phases through $2V$ costs only $O(D^2/R)$ in $P_2$. In an abstract prime phase assignment, set the real parts at all remaining primes to zero except on $0.9\le 2D-\log p\le1.1$. On this slab $(k_\epsilon*B_2)(\log p)$ is bounded above by a fixed negative constant for sufficiently small fixed $\epsilon$ and large $D$: The unshifted $h_2$ there is below $-.49$, its convolution tends uniformly to it on this compact as $\epsilon\downarrow0$, and the three more distant endpoints have exponentially small convolved tails. By PNT the slab has log-prime mass $\asymp V^2$. Choosing a common real part in $[-1,1]$ on it therefore allows either sign and any fixed target for $P_2$ up to $o(1)$, with prime powers negligible as above. This restores just the new prime measurement to the phase-law comparison. It does not treat phases at an actual $t$ as freely adjustable.

## More lengths if the second measurement does not decide

For example at $c=1.75$, use $|1+2z+2z^2+2z^3+z^4|^2$ on $|z|=1$. Its constant is 14 and its cosine coefficients are $(24,16,8,2)$. Under failure and no deep zero, positivity and (1) imply

$$ \frac{16P_2}{\cosh(2c)}+\frac{8P_3}{\cosh(3c)}+\frac{2P_4}{\cosh(4c)}<-.031 . $$

Indeed the limiting upper price is $14/3-24p/\cosh c<-.03139$. Compare the **signed combination**, not three independent bounds. More generally for fixed $c$ with $\cosh c<6p$ one can choose a finite degree such that the longer measurements cannot all be near zero at a shallow failure. Use $|1+z+\cdots+z^n|^2/(n+1)$, whose first cosine coefficient is $2n/(n+1)$. For large fixed $n$ its first term alone spends more than $1/3$ in the price inequality; the other terms must compensate. Conversely if $\cosh c\ge6p$, the boundary law at depth $c$ with density $(1-2(3p/\cosh c)\cos\theta)/(2\pi)$ has precisely the first required moment and *all* higher moments zero. The limit $\operatorname{arcosh}(94/27)=1.91931\ldots$ is for this moment-only, vanishing-long-measurements comparison, not a depth forced from the original angular datum.

**Decision.** At a candidate first measure the doubled-cutoff sum at its original height. A value outside the appropriate interval asks for the corresponding deeper census, not for a second height; a value inside does not. The four-length inequality is another signed screen if those sums are available. If none discriminates, retain the original [single-height net-charge](common-filter-depth.md) or [two-height signed test](common-filter-pair.md). Nothing here bounds $P_2$ pointwise at exceptional samples, proves a zero-free window, or changes the uniform $Z$ bound. [Replay the scalar and spline checks](check-long-cutoff-moments.py) with SageMath Python without `-O`.

**Before extending past the measured prefix:** The [finite cutoff budget](finite-cutoff-budget.md) gives the full finite moment test for signed data and the least maximum order on the near-zero path. For example, at $c=1.90$ use the order-15 signed price rather than the order-54 equal-coefficient construction. The sharp cutoffs are for this model; they do not predict the measurements.
