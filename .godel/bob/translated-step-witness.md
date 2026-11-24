# Twelve radial orders at depth 1.95

At scaled depth $c=39/20$, the **least maximum order is twelve** on the zero-answer path in the [fixed-translate limiting comparison](translated-cutoff-budget.md). A new step law obstructs order eleven simultaneously for all translates. The [phase-shifted order-twelve separator](phase-shifted-cutoff.md#the-two-measurements) already suffices. This is not a claim about the least number of measurements, about nonzero responses, or about actual exceptional conductors or zeta zeros.

## A fixed witness and its certificate

The [replay](check-translated-step.py) defines $a(z)$ by rational pairs $(1024z_j,10^{12}a_j)$: Use level $a_j$ from knot $z_j$ to the next knot, zero before $-12$, and the last level from $16$ onwards. With $J=e^{-z/2}a(z)$ and $\widehat{J}(x)=\int_{\mathbb R}J(z)e^{-ixz}\,dz$, it checks

$$|a|\le 1,\qquad \int_0^\infty z e^{-z}\sqrt{(1+a(z))/2}\,dz>8/9,\qquad \sup_{x\in\mathbb R}|\widehat J(x)|\le C=0.61505322.$$

The angular weight integrates to one. Its exact mass on each slab is the difference of $(1+z)e^{-z}$ at the endpoints. If $b_j=e^{-z_j/2}(a_j-a_{j-1})$ with $a_{-1}=0$, integrating $J$ on the slabs and telescoping gives

$$\widehat J(x)=\frac{e^{2ix}}{1/2+ix}N(x),\qquad N(x)=\sum_j b_j e^{-ix(z_j+2)}.$$

The replay also compares this jump formula to the uncombined slab integral at three rational frequencies. For $|x|\ge64$, it checks $\sum_j|b_j|/64<C$. On $[0,64]$, let $Q(x)=|N(x)|^2-C^2(1/4+x^2)$. With $B_k=\sum_j|b_j||z_j+2|^k$, the product rule bounds $|Q^{(4)}|$ by $\sum_{k=0}^4{4\choose k}B_kB_{4-k}$. On each dyadically subdivided interval the replay adds the first three derivative bounds at the midpoint and this fourth-order Taylor remainder to the midpoint value, and checks a strict negative upper bound. Real $a$ supplies evenness of $|\widehat J|$. This is a whole-frequency bound, not an estimate from peaks on a grid.

Run `sage .godel/bob/check-translated-step.py` at the repository root. It needs SageMath with Arb real and complex balls (tested with SageMath 10.9, 128-bit precision) and assertions enabled. Rational inputs are exact and comparisons use outward enclosures. The output was:

```text
angular mean minus 8/9: [8.323590532923062168517177541e-8 +/- 1.95e-36]
jump tail bound at 64 : [0.60322348450006397995847381231833832 +/- 3.02e-36]
all-frequency cap: [0.61505322000000000000000000000000000000 +/- 4.86e-39] ; finite boxes: 3603
order-11 slack: [0.0004111950207585306998087314560184485 +/- 6.01e-38]
zero-frequency excess over order-12 cutoff: [0.00210514941437339979995767660470560 +/- 4.70e-36]
```

The knots were set on nonuniform meshes. Finite-grid cone optimization with exchange of sampled local peaks chose the levels, after which both knots and rounded levels were frozen. The best floating-point sampled maximum before rounding was about $.61505318$; neither the search nor its solver is needed to replay the certificate or establishes optimality of the cap.

## Apply the same law to every translate

Use $R,V,D,t$ and the splines $B_j$ from the [long-cutoff comparison](long-cutoff-moments.md). On the prime side take the abstract real phase assignment $a(D-\log p)$, giving absolute half-angle cosine $\sqrt{(1+a)/2}$. For fixed first-order shifts $s$ and real coefficients $A_s$, define

$$f(z)=\sum_s A_s(z+s)_+,\qquad w_0=1/2+ix,\qquad H(x)=\sum_s A_s e^{s w_0},\qquad d\mu(x)=\frac{dx}{2\pi|w_0|^2}.$$

The limiting first price is $\int f(z)a(z)e^{-z}\,dz$. Since $\widehat{e^{-z/2}f}=H/w_0^2$, Plancherel writes this price as $\int \Re(HG)\,d\mu$ with $G=(\bar w_0/w_0)\overline{\widehat J}$. On the shallow side keep the same marginal $\mu$, depths $\pm c$ equally, and first conditional complex circle moment $m_1(x)=-3G(x)/\cosh c$.

The certified cap is below $C_{11}=\cosh(c)/(6\cos(\pi/13))$. Thus at each $x$ the grid $\theta_l=(2l+1)\pi/13$, $0\le l<13$, with masses $(1-2|m_1(x)|\cos\theta_l)/13$ is nonnegative. Its first moment is $-|m_1(x)|$ and moments two through eleven vanish by the roots-of-unity sum. Rotate the grid by $\arg(-m_1(x))$ when $m_1(x)\ne0$; this keeps the zeros and matches the prescribed complex first moment. The first residue price is therefore $-\cosh(c)\int\Re(Hm_1)\,d\mu/3=\int\Re(HG)\,d\mu$. The vanishing higher moments are conditional on $x$, so no fixed translated multiplier can change the higher zero answers, even with different shifts at each order.

These zero answers agree with the same prime assignment. Nonzero prime real parts are confined to $p\le e^{12}V$ and the whole smoothed, translated spline is $O_{j,\epsilon,H}(1+D^j)$ in supremum norm. Chebyshev, after the $R^{-(j+1)}$ normalization, gives $O_{j,\epsilon,H}((1+D^j)R^{1-j})=o(1)$ for each fixed $j\ge2$. Prime powers are negligible by the [long-cutoff truncation](long-cutoff-moments.md#the-arithmetic-observable) with sufficiently small fixed $\epsilon$. These are the fixed-test limits, first large $q$ then small $\epsilon$, not bounds uniform in growing shifts or order.

## Decision

The upper side is the phase-shifted test accepted at `9e976c723f57337aa2d4da05259a47cc1336a6f5`: At order $j$, use shifts $l/10+j/25$ for $|l|<6$ with the coefficients specified there. All are permitted fixed translates. The replay of its `check-masked-cutoff.py` gave the limiting upper price $-0.00014656108484547\ldots$ on its signed order-twelve combination under shallowness, so all longer answers through twelve being zero are incompatible. Together with the common witness through eleven, this pins the least maximum order to twelve.

The earlier price also rules out the order-twelve Fourier target $C_{12}=\cosh(c)/(6\cos(\pi/14))=.612948024\ldots$, not merely for this witness. For that test's first mask $H=H_6 e^{ix/25}$ with $H_6\ge0$ and $I=\int H_6\,d\mu$, its established floor and the first-price identity imply $P\le\int\Re(HG)\,d\mu\le I\|\widehat J\|_\infty$ for any admissible step law. The negative order-twelve price is precisely $P/I>C_{12}$. This does not identify the optimum Fourier cap.

Use the signed test for available data; do not treat a feasible prefix as proof of shallowness or a small rounded measurement as an exact zero. To improve the decision on the zero-answer path below order twelve requires information beyond this fixed-translate relaxation, not another choice of eleven-order mask.

One such datum now has a [certified joint price](short-third-price.md): Compare the order-eleven screen with the short third harmonic before extending the radial cutoff. The threshold that excludes this one step law does not by itself exclude every shallow law.
