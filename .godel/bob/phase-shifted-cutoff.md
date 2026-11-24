# One raw order versus a phase-shifted prefix

At a sufficiently large real high-endpoint failure use the [original height, order-$j$ spline $B_j$, and smoothing](long-cutoff-moments.md). Two decisions differ: Can the unchanged $P_2$ force a deeper census, and how far must a new translated prefix run? For the raw decision a zero answer separates at $c=1.577$ but is feasible at $1.5797$, **even given all first-order translates** in the limiting comparison. For the prefix decision, a linear rotation of the zero phase reduces the sufficient maximum order at $c=1.95$ from thirteen to twelve. The latter does not improve the guarantee from $P_2$ alone.

## The two measurements

Set $h=1/10$, $r_l=(N-|l|)/N^2$ for $|l|<N$, and $H_N(x)=|N^{-1}\sum_{l=0}^{N-1}e^{ilhx}|^2=\sum_l r_l e^{ilhx}$. Given a fixed real $b$, define $T_j(N,b)$ using shifts $s=lh+jb$ and coefficients $A_s=r_l e^{-s/2}$: Replace $B_j(y)$ in $P_j$ by $\sum_s A_s B_j(y-s)$ **before** smoothing. The first price is the [masked-cutoff floor](masked-cutoff.md) $P=2(8/9)^2/\mathcal L-\sum_s A_s e^s$, where $f(z)=\sum_s A_s(z+s)_+$ at $j=1$ and $\mathcal L=\int_0^\infty z^2e^{-z}/f(z)\,dz$. Both filters below have positive coefficients and $f(0)>0$. No longer measurements are inferred by translating the first sum.

In that note's shallow comparison, the line multiplier at order $j$ is now $e^{ijbx}H_N(x)$. The order-dependent translation is essential: This replaces the common phase $\phi$ by $\phi+bx$ at *every* order, leaving the mass and the depth factors untouched. More explicitly the conditional summand for $-T_j/(M\cosh(jc))$ is, up to vanishing total errors,

$$H_N(x)\frac{\cosh(jd)}{\cosh(jc)}\cos(j(\phi+bx)).$$

The contour bounds, line replacement, reflection, and trace marginal in the masked proof apply since there are only finitely many fixed shifts for each of finitely many fixed orders. Reflection changes depth sign at fixed $x$. The harmonic extension of a nonnegative cosine polynomial is nonnegative at $(d,\phi+bx)$ pointwise, without an independence assumption. Let $I=\sum_l r_l e^{-|l|h/2}$ and $K=\sum_{l,m} r_lr_m e^{-|l+m|h/2}$. These are the first two mask moments for $d\mu=dx/[2\pi(1/4+x^2)]$.

* **Raw $P_2$.** Use $(N,b)=(5,0)$ only at the first cutoff. The unmasked limiting upper price from the masked proof is $\cosh(2c)(1-2(3P/\cosh c)^2/K)/3$. At $c=1.577$ it is below $-.00154$.
* **New second measurement.** Use $(N,b)=(6,1/25)$ throughout. The upper price for $T_2$ is $I\cosh(2c)(1-2(3P/(I\cosh c))^2)/3<-.00124$ at $c=1.61$. In particular the order-two filter is centered at shift $2/25$, not $1/25$.
* **Order twelve.** With the same $(6,1/25)$ and $n=12$, take $v_k=\sqrt{2/14}\sin((k+1)\pi/14)$, $0\le k\le12$, and $s_j=2\sum_{k=0}^{12-j}v_kv_{k+j}$. The [sine-vector inequality](finite-cutoff-budget.md) at the rotated phase gives a limiting upper price on $\sum_{j=2}^{12}s_j T_j/\cosh(jc)$ of $I/3-2\cos(\pi/14)P/\cosh c<-.000146$ at $c=1.95$.

Thus measured lower bounds of $-.0015$, $-.0012$, and $-.00014$, respectively, force a right zero with $D(\beta-1/2)>c$ in the corresponding row. The height is $t=2q^{3/5}$, $D=\log((9\log q/5)^2)$, and $|\gamma-t|\le(2/\epsilon)\log D$ includes the center. The strict margins absorb errors by fixing sufficiently small $\epsilon>0$ before taking $q$ sufficiently large. Run [the price checker](check-masked-cutoff.py) with SageMath Python without `-O`.

## Why the raw decision cannot just inherit the rotated depth

Keep the [joint translated-ramp comparison](translated-cutoff-budget.md), but require only the **raw** order-two value to be zero. Write $z=D-\log p$, $w=1/2+ix$. For a step prime-phase assignment $a(z)=\cos(t\log p)$ in the relaxation, zero below its first knot and constant after its last, let $z_l$ denote knots and $u_l=e^{-z_l/2}\Delta a_l$. Matching every first price is achieved at depths $\pm c$ by a conditional circle first moment

$$m(x)=-3G(x)/\cosh c,\qquad G(x)=\sum_l u_l e^{iz_l x}/w.$$

Indeed $\widehat{e^{-z/2}a}(x)=\sum_l u_l e^{-iz_l x}/w$, and multiplication of its conjugate by $\bar w/w$ gives the signed first-price representer from the linked proof.

There is an exact further test once $m$ is fixed and $|m|\le1$. The **unmasked** second cosine moment can be zero if and only if

$$\int(\Re m)^2\,d\mu\le1/2,\qquad \int(\Im m)^2\,d\mu\le1/2.$$

In fact at each $x$ put the circle law on the endpoints of the vertical chord through $m(x)$, with mean $m(x)$. Then the real second moment is $2(\Re m)^2-1$. On the horizontal chord it is $1-2(\Im m)^2$. These are extrema by the nonnegativity of each coordinate variance; at a degenerate chord use a point mass. A constant mixture of the two conditional laws reaches every value between their **integrated** extrema. It need not kill the second moment conditionally on $x$. For a raw measurement it is incorrect to impose the stronger pointwise requirement $|m(x)|\le1/\sqrt{2}$.

For $c=1.5797$ the [witness checker](check-raw-cutoff-law.py) uses the following levels divided by $100000$, starting at knots $j/10$, $-4\le j\le8$:

```
-88932, -100000, -100000, -100000, -58442, 34040, 66435,
71453, 67715, 64682, 62872, 61717, 57755
```

Integration on the nonnegative slabs gives $\int z_+ e^{-z}\sqrt{(1+a)/2}\,dz>8/9$. The jump polynomial's modulus is even and $20\pi$-periodic, so verifying $|G|<\cosh c/3$ by ball subdivisions through $10\pi$ suffices. To check the two energies, integrate each exponential term of $|G|^2$ and $G^2$ against $\mu$. The kernels for the difference $v=z_l-z_k$ and sum $v=z_l+z_k$ of knots, respectively, are

$$L(v)=(2+|v|)e^{-|v|/2},\qquad S(v)=(1+v_++v_+^2/2)e^{-|v|/2}.$$

Indeed the respective Fourier integrands apart from $e^{ivx}dx/(2\pi)$ are $w^{-2}\bar w^{-2}$ and $w^{-3}\bar w^{-1}$. Invert by convolving the positive and negative half-line exponentials with the corresponding polynomial powers. In the second case this is $\int_{\max(0,-v)}^\infty (v+y)^2 e^{-(v+2y)/2}\,dy/2$; the first is the same integral with polynomial $(v+y)y$. Half the sum and half the difference of the resulting two quadratic forms in the jumps are the real and imaginary energies of $G$. The checker gives $.3554931$ and $.0137400$ as strict upper bounds, both below $\cosh^2(c)/18$. It checks the entire spectrum and the integrals, not just a frequency grid.

The same prime assignment gives limiting $P_2=0$: Its nonzero real parts are confined to primes below $e^{.4}V$, whose smoothed weight costs $O_\epsilon((1+D^2)/R)$ after normalization, with prime powers negligible as in the long-cutoff identity. Thus both sides of the limiting model match **the same data**, including all first ramps. This is not a zero divisor or an exceptional conductor. Use the raw test if only that measurement is known; between $1.577$ and $1.5797$ this comparison does not identify its exact limiting threshold. Beyond the obstruction use an additional observable, not another first weight followed by the same zero answer.
