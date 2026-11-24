# Two signed first masks at the original and third heights

Let $R=(9/5)\log q$, $V=R^2$, $D=\log V$, and $t=2q^{3/5}$. Suppose a real primitive character of conductor $q$ fails the endpoint test at its own cutoff $V$ and modulation $q^{3/5}$. More generally, use the [same failure datum](fixed-strip-endpoints.md#signed-pairs-versus-the-gram-bound) for a real twist of conductor $q|d_0|$ at its own cutoff $(\tfrac95\log(q|d_0|))^2$, with $|d_0|\le V^\theta$ for fixed $\theta$ and modulation still $q^{3/5}$. At least one of the two windows

$$ |\gamma-t|\le (2/\epsilon)\log D,\qquad |\gamma-3t|\le (2/\epsilon)\log D $$

contains a zeta zero with **$D(\beta-1/2)>1.23684$**. Both centers are included. Fix any sufficiently small $\epsilon>0$ and then take $q$ sufficiently large. This uses neither a long-measurement premise nor an external zero-free strip. Unlike the older [common-filter rows](common-filter-pair.md), it asserts existence, not a signed charge on an annulus. In particular, the first-height hole of those rows is not part of this result. The [depth-$1.95$ five-translate result](joint-refit-10-2.md) compares with a signed *higher*-measurement premise and does not give this unconditional disjunction.

## The common prime floor

For each $y=t,3t$ fix real coefficients $b_{y,l}$ on a finite lattice of shifts $lh$. The [new table](symmetric-first-depth.txt) uses $h=1/100$ and records $l,10^{10}b_{t,l},10^{10}b_{3t,l}$; the [repriced table](paired-10-2.txt) uses $h=1/25$ and denominator $10^7$. Unlisted coefficients are zero. Both signs are carried by the coefficients. Put

$$ H_y(x)=\sum_l b_{y,l}e^{ilhx},\qquad f_y(z)=\sum_l b_{y,l}e^{-lh/2}(z+lh)_+. $$

Let $z=D-\log p$, $d\nu_q=V^{-1}\sum_p(\log p)\delta_z$ and $u=|\cos((t/2)\log p)|$. With $A(u)=2u^2-1$, $B(u)=4A(u)^3-3A(u)$, the cosines at $t$ and $3t$ are exactly $A(u)$ and $B(u)$ for the **same** $u$. Define the unsmoothed signed prices $P_y=\int f_y(z)\cos(y\log p)\,d\nu_q$. The original endpoint test at $q^{3/5}$ gives its normalized real-character prime mean $\ge 8/9-o(1)$, since the conductor plus Gamma term is $(1+3/5+o(1))\log q$ and the mean has coefficient $9/5$ on dividing by $\log q$. For a twist the total variation change when moving the failure weight from its own cutoff to $V$ is $o(1)$ uniformly by the linked bound. Bounding the real character values by one gives $\int z_+u\,d\nu_q\ge 8/9-o(1)$. This is the only failure-specific input. In particular we do not translate this datum when translating the test ramps.

Subtract $z_+u$ before integrating, and take the pointwise minimum over $0\le v\le 1$. It follows that

$$ P_t+P_{3t}\ge \mathcal P-o(1),\qquad
\mathcal P=\frac89+\int_{\mathbb R} e^{-z}\min_{0\le v\le1}\{f_t(z)A(v)+f_{3t}(z)B(v)-z_+v\}\,dz. $$

Only the minimum, which is continuous, vanishes below a fixed left endpoint, and has at most linear growth on the right, is tested against PNT. On compact $z$ intervals the normalized log-prime measure tends to $e^{-z}dz$ by PNT and step approximation. Beyond $z=L$ the absolute tail costs $O((1+L)e^{-L})$ uniformly by Chebyshev and partial summation. The multiplier of the angular datum is one in both the integral and the $8/9$ term.

## The full first-mask prices when both windows are shallow

Write $x=\gamma-y$, $d=D(\beta-1/2)$, $w=\beta+ix$, $w_0=1/2+ix$ and $k(x)=|w_0|^{-2}$. Suppose at one of the two heights there is no right zero with $d>c$ in its closed window. Reflection at the same ordinate makes $|d|\le c$ throughout that window, with no exclusion at $x=0$.

Use only the first **whole even tent** and the signed smoothing in the [Mellin identity](long-cutoff-moments.md#one-common-phase-on-the-divisor). At shift $s=lh$ translate the tent in the log-prime variable by $s$ before smoothing and scale by $b_{y,l}e^{-s/2}$. The moment with cosine at $y$ then has Mellin multiplier

$$ \frac{g(w)}{R^2}\frac{e^{Dw}(1-e^{-Dw})^2}{w^2}L_y(w),\qquad L_y(w)=\sum_l b_{y,l}e^{lh(w-1/2)},\quad g(w)=\exp(1-\cos(\epsilon w)). $$

Thus $P_y$ is minus the real sum of this multiplier over the zeta zeros, up to $O(\epsilon)+o_\epsilon(1)$. Indeed the fixed translated tents give the ramps at nonnegative log prime arguments except on a fixed compact set costing $o(1)$; their first-order smoothing costs $O(\epsilon)$ by the [Lipschitz and tail bound](masked-cutoff.md#five-shifts-and-their-first-price). Prime powers are negligible. The new multiplier $L_y$ is uniformly bounded on the contour strip, and $\log(3t)/R\to1/3$ just as $\log(t)/R\to1/3$. The contour, pole, and discarded outer-residue estimates therefore apply unchanged up to fixed constants at both heights. In particular $|x|>(2/\epsilon)\log D$ makes the smoothing bound at most $\exp(1-D^2/4)$; the whole-tent factors and the inverse-square zero count then give $o_\epsilon(1)$ outside the window, without restricting depths there.

On retained shallow zeros $L_y(w)=H_y(x)+O_c(D^{-1})$, $w^{-2}=w_0^{-2}+O_c(k(x)/D)$, and $(1-e^{-Dw})^2=1+O_c(R^{-1})$. Bounds are uniform in $x$ for fixed coefficients. Also $|g(w)|\le G_\epsilon=\exp(1-\cos\epsilon)$ for $0\le\beta\le1$ and sufficiently small $\epsilon$. The sum of the line-replacement errors is $o_\epsilon(1)$ by the unit zero counts. Take absolute values only **after** summing the shifts in $L_y$, so the remaining weight is $k(x)|H_y(x)|$, not the sum of the absolute individual shift prices. The depth factor from $R^{-2}e^{Dw}$ is $e^d/R$. Pair at each $x$ before bounding the resulting positive majorant: The two values $e^{\pm d}$ average to $\cosh d\le\cosh c$, and a line zero has factor one. Consequently

$$ P_y\le\frac{G_\epsilon\cosh c}{R}\sum_{|\gamma-y|\le (2/\epsilon)\log D} k(x)|H_y(x)|+O(\epsilon)+o_\epsilon(1). $$

For the trace limit put $d\mu=dx/[2\pi(1/4+x^2)]$. In this shallow case the [local Poisson trace](masked-cutoff.md#what-the-shallow-hypothesis-buys) applies also to the continuous test $k|H_y|$. Explicitly, normalize the local zero count by $\log y$. For each fixed $a>1/2$ and $v\in\mathbb R$, the exterior Hadamard identity at $1/2+a+i(y+v)$ gives a limiting Poisson sum $1/2$; Euler and gamma give $(\log y)/2+O_{a,v}(1)$ before normalization. Unit counts let us discard outside the window and replace the local width $1/2+a-\beta$ by $a$ at cost $o(1)$ after normalization. The same counts give vague compactness and a uniform inverse-square tail. Each subsequential limit has the Poisson integral $1/2$ at every $(a,v)$ above; analyticity in $a$ extends this to all real $a>0$, and the normalized Poisson approximate identity identifies the measure as $dx/(2\pi)$. This justifies testing against $k|H_y|$ by its inverse-square decay. In particular

$$ R^{-1}\sum_{|\gamma-y|\le (2/\epsilon)\log D} k(x)|H_y(x)|\longrightarrow\frac13\int |H_y|\,d\mu. $$

Under shallowness of **both** windows, add the two upper prices. Since $G_\epsilon\to1$, the limiting upper price in the given order of limits is the bound needed here, $\frac{\cosh c}{3}\int (|H_t|+|H_{3t}|)\,d\mu$. Equivalently, one can first remove $g$ on each fixed compact ordinate set as $\epsilon\downarrow0$ and bound both tails by $O(1/B)$ beyond $|x|=B$, then use the signed first-rotation identity with carrier $\exp(iDx-2i\arg w_0)$ before taking absolute values. In both derivations reflection is at the *same* ordinate, so it does not conjugate $H_y$ or reverse its shift. This step only uses the pointwise cap, not any higher-order angular constraint or a finite spatial deconvolution. If $\mathcal P$ strictly exceeds that number, take $\epsilon$ small enough and then $q$ large enough so that the total errors are smaller than the gap. The shared lower bound at failure contradicts simultaneous shallowness. This proves the strict depth conclusion and requires no information about phases at individual zeros or their correlation between heights.

## Numerical certificate

From the repository root, with SageMath 10.9 and assertions enabled:

```sh
sage .godel/bob/check-symmetric-first-depth.py
```

The [checker](check-symmetric-first-depth.py) uses the fixed integer inputs, exact shift and coefficient rationals, and 128-bit real and complex balls. It tests the shared lower floor, both full-norm upper bounds, and their priced difference. All columns below round in the sufficient direction; the price and difference use the internal ball bounds before decimal rounding.

| First masks | $c$ | $\mathcal P>$ | $\int |H_t|\,d\mu<$ | $\int |H_{3t}|\,d\mu<$ | Price $<$ | Gap $>$ |
|---|---:|---:|---:|---:|---:|---:|
| [Repriced](paired-10-2.txt), first columns only | 1.23627 | .16405890 | .25979062 | .00388180 | .164057572 | $1.3\cdot10^{-6}$ |
| [New](symmetric-first-depth.txt) | 1.23684 | .16546278 | .26142997 | .004371324 | .165461796 | $9.0\cdot10^{-7}$ |

Both rows passed as written with SageMath 10.9 in the candidate workspace based at `0648ae053814bd2c07dd78ff74446225e795e8ae` (42 seconds). The new row's ball lower bound on the signed difference is $9.932214480951384\cdot10^{-7}$ to the shown precision. The transfer from first masks to shallow zeros was also independently checked using the complex-carrier form of the residue identity, followed by the exterior Poisson trace and an inverse-square tail bound.

The first row reuses masks originally fit for a higher-order test, but no higher coefficients or prices enter either row. The new masks were nominated by a sampled cone fit with two modulus epigraphs and angular minimum cuts, using cap $\cosh(1.237)/3$ and failure multiplier one. Exploratory lattices of width $.04$, $.02$, and $.01$ gave improving prices; on the $.01$ lattice the frozen pair was rounded to $10^{-10}$ and entries of magnitude below $10^{-8}$ after rounding were set to zero. The fit and its numerical crossing near $1.236854$ are not needed for replication, and neither is an optimality certificate.

* **Prime side.** At each radial node sample $v=j/M$ with $M=1536$ on the full interval including endpoints, and subtract $(4|f_t|+420|f_{3t}|)/(8M^2)$. At an interior angular minimizer the derivative is zero, and the absolute second derivative is bounded by $4|f_t|+420|f_{3t}|$ on $[0,1]$. On each radial cell all knots and zero are treated as boundaries, in addition to the $1/250$ mesh through the right endpoint (9 for both tables). For each $v$ the polynomial being minimized is affine in $z$. Its minimum is concave on each cell and is bounded below by the chord of the lower bounds at its endpoints. Integrate that chord with the exact exponential mass and first moment. On the right tail use the endpoint lower bound plus distance from the endpoint times the independent lower bound on the minimum slope. On the left tail all ramps, including $z_+$, vanish.
* **Zero side.** With $\vartheta=hx$, $\eta=h/2$, the Cauchy probability folds, using evenness of $|H_y|$ and periodicity, onto $[0,\pi]$ with density $\rho(\vartheta)=\sinh\eta/[\pi(\cosh\eta-\cos\vartheta)]$. This follows, for example, from the Cauchy's Fourier coefficients $e^{-|l|\eta}$ and summation of the geometric series; it includes the whole real-line tail. The cumulative mass at an interior point is $(2/\pi)\arctan(\tan(\vartheta/2)/\tanh(\eta/2))$. In each of the $32768$ equal cells of width $\delta$, linearly interpolate the **complex** polynomial between endpoints, with error bounded by $\delta^2\sum_l l^2|b_{y,l}|/8$. The triangle inequality bounds its modulus by the chord of the two moduli plus this error, also where the polynomial vanishes. The exact cell mass times the average endpoint modulus gives the symmetric part of the chord integral. The difference from that part is bounded by $\delta(\rho_{\rm left}-\rho_{\rm right})/8$ times the absolute endpoint difference: Subtract any constant density between its endpoint values and integrate the positive and negative halves of the centered linear weight. This uses monotonicity of the folded density. All cell masses and interpolations are enclosed, not merely sampled ordinates.

The [$(9,9)$ witness](two-height-translated-radial.md) gives an abstract ceiling for the first-mask comparison: The same admissible phase law pays at most $.62275\int (|H_t|+|H_{3t}|)d\mu$ for **every** pair of first masks, by its Plancherel representation and Fourier cap. Hence the common prime floor cannot exceed that upper bound, and no such comparison can certify $c\ge\operatorname{arcosh}(3\cdot .62275)\simeq1.237312$. This is an obstruction in the relaxation, not a bound on zeros or a claim of optimality of the table. For the first-only comparison a circle law with the prescribed first moment exists when its modulus is at most one; higher moments are then free, not necessarily zero. The separate convolution lift (accepted at `daee96a913971252a4db7f06bcdbc73214431a9e`, `.godel/bob/endpoint-convolution-lift.md`) matches unconstrained long answers on the same first-layer prime law, by modifying the long layers. No long-layer construction is used in the lower certificate.
