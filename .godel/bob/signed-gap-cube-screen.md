# Testing cancellation across, and inside, integer gaps

On one retained shift, two genuine shell heights have almost equal sums of absolute gap contributions, but their signed sums have opposite signs. Asymptotically, cancellation **inside** the dense gap groups suffices to clear whole height intervals of length $X^k$, where $k\sim\log_2\log X$. This gives a signed cap test with $O(1+t/X^k)$ statistic evaluations per retained shift. It does not say that a specified ordinate clears. There is a phase ambiguity even given *all* the complex group magnitudes as functions of height.

Use the [retained-shell notation and cap equivalence](retained-shell-overshoot.md): $t=2q^{3/5}$, $X=(3\log(t/2))^2$, $D=\log X$, $L=X/D$, $n=2\lceil(2+\gamma)\log t/D\rceil$, $0<\gamma<1/2$, $a=1/16$. Freeze $d\le5D$ positive, $p,p+d$ prime in $[e^{-8}X,X]$, $w_p=X^{-1}\log(X/p)\log p\log(p+d)$, and $\lambda_p=\log(1+d/p)$. Set $w_p=0$ at absent starts. For a far gap $g>nD^2$ put

$$P_g(u)=2\sum_{p} w_p w_{p+g}e^{iu(\lambda_p-\lambda_{p+g})},\qquad Q_d(u)=\sum_g\Re P_g(u),$$

summing only over present pairs. Call a group dense if it has more than $M=X/(nD^4)$ such pairs. Write $Q_*$ for the dense real sum. Retention means that the ordered mass of starts at distance $\le D^2$, times $n^2$, is at most fixed $K$. Only in transferring the result back to the cap will we need this assumption.

## The finite test

At $q=2^{127}-1$, $\gamma=1/4$, and $d=18$, one has $0<M<1$: **All** 11141 nonempty far groups are dense. The maximum group count is 184. As a diagnostic, not a deletion at cap precision, also sum just the groups with at least ten pairs. The [Sage interval checker](check-retained-crest.py) gives these strict bounds, with $v=9t/8+1296287232$, $\ell=L/\sqrt n$:

| Height | $\lvert Z_d\rvert$ | $Q_*=Q_d$ | $\sum_{\#\ge10}\Re P_g$ | $\sum_{\#\ge10}\lvert\Re P_g\rvert$ |
|:--|--:|--:|--:|--:|
| $v$ | $(.429,.431)$ | $(.097,.098)$ | $(.098,.099)$ | $(.515,.516)$ |
| $t+2\ell$ | $(.028,.029)$ | $(-.006,-.005)$ | $(-.006,-.005)$ | $(.515,.516)$ |

Thus at the grid node, taking absolute values *after summing within each group* already costs more than half a unit in this diagnostic, whereas the signed dense sum is negative. Nearly equal absolute totals coexist with very different signed totals. Neither row tests the asymptotic screen below. The first row is the exact crest center, not asserted to be a grid node.

## A slow test on the genuine shell

Take, eventually,

$$k=\left\lfloor\log_2\frac{D}{(\log D)^4}\right\rfloor,\quad H=\lfloor\exp(D/(\log D)^2)\rfloor,\quad V=X^k,\quad \delta=(a^2/(800D^4))^{2^k}.$$

We construct an explicit real test (the real part of $S$ below) such that

$$\sum_{g\ {\rm dense}} |P_g(u)|\ge a^2/2\quad\Longrightarrow\quad \Re S(u)\ge 3\delta/4,\qquad V\sup|S'|=o(\delta). \tag{1}$$

In particular this is a sufficient screen for the **signed** target, not an equivalence with an absolute gap bound. We use exact rational logarithms throughout; the derivative bound controls cell width, not phase rounding at the center.

**Differencing the original sum.** Average $g$ uniformly from $1$ to $G=\lfloor X\rfloor$ and $p$ uniformly on the cyclic group of order $N=2G+1$. For representatives $0\le p<N$ set

$$f_g(p)=1_{g\ {\rm dense}}\,w_p w_{p+g}(8D^2/X)^{-2} e^{iu(\lambda_p-\lambda_{p+g})},$$

with missing terms zero and $p+g$ interpreted as an integer in the weight. Then $|f|\le1$. Multiply by one unit scalar per $g$ to make its $p$-average nonnegative. The mean of this rotated $f$ is $\sum_{\rm dense}|P_g|/[2NG(8D^2/X)^2]$. The denominator is at most $400D^4$. These auxiliary rotations are only for the inequality; the statistic is independent of them.

Take independent differences $h_i=b_i-b'_i$ of independent uniform integers in $[1,H]$. Starting from $f$, apply $F(p)\mapsto F(p+h_i)\overline{F(p)}$ successively on the cyclic group. Let $A_j$ be the mean after $j$ steps over all variables. Then $|A_j|^2\le A_{j+1}$: Insert an independent uniform translation $b\in[1,H]$ under the $p$-average, take Cauchy outside the $b$-average, expand its squared modulus, and translate $p$ by the second draw. The inner $p$-average before Cauchy is shift invariant. After the first step the gap rotations cancel exactly. Thus on the left of (1), $A_k\ge\delta$.

Each nonzero resulting term has $R=4\cdot 2^k$ prime vertices

$$p+\sum_{i\in I}h_i+eg+bd,\qquad I\subseteq[1,k],\quad e,b\in\{0,1\},$$

counted for now with multiplicity. There is no wrap in these formulas: The zero corner $p$ is in the band, and $kH=o(e^{-8}X)$. Delete every label with a repeated vertex and call the remaining mean $S$. For fixed $g$ in the sum the offsets $0,d,g,g+d$ are distinct. A collision involving different subsets fixes one of the $h_i$ given all the others, costing probability at most $1/H$. Consequently $|A_k-S|\le R^2/H=o(\delta)$, since $\log(1/\delta)=O(D/(\log D)^3)$. This deletion is made **after** iterating Cauchy, not inside each differencing step.

The frequency of a surviving term is the $k$-fold difference of $\lambda(p)-\lambda(p+g)$. Integrate the $k$th derivative over the box with directed sides $h_i$. Throughout the box both arguments lie between their corner extrema. From $\lambda(x)=\int_0^d(x+y)^{-1}dy$ its absolute frequency is at most $2H^k d\,k!(e^8/X)^{k+1}$. The total coefficient mass is at most one. Multiplication by $V$ leaves $\exp(-D+o(D))=o(\delta)$, proving (1).

## Why the slow test rarely flags

For $m=k$ one has, on $U=[t,5t/4]$,

$$ |\{u\in U: |S(u)|\ge\delta/4\}|\ \le\ tX^{-(2-o(1))m}. \tag{2}$$

Here the multiplicities and the cost of the growing moment matter. For each surviving label its signed prime-valuation vector has precisely $R$ nonzero entries, half $+1$ and half $-1$. Unique factorization identifies equal rational characters with equal vectors. Given the support, the label $(p,g,h_1,\ldots,h_k)$ is determined by choosing $p,p+g,p+h_1,\ldots,p+h_k$ from it, so there are at most $R^{k+2}$ compatible labels. Each carries weight at most $(NGH^k)^{-1}$, using the triangular law on differences. The coefficients $c_v$ after coalescing are nonnegative, have sum at most one, and satisfy $\sum_v c_v^2\le R^{k+2}/(NGH^k)$.

For independent unit circle phases at the primes let $F(z)=\sum_v c_v z^v$. In one variable $z$, for complex $a_0,b,c$, set $w=bz+c\bar z$. The distribution is symmetric under $w\mapsto-w$. The sign average of $|a_0\pm w|^{2m}$ is largest for aligned arguments with the same moduli (expand in even powers of $2\Re(a_0\bar w)$). Hence it is bounded by $\sum_j\binom{2m}{2j}|a_0|^{2m-2j}|w|^{2j}$. Use $|w|^2\le2(|b|^2+|c|^2)$ and $\binom{2m}{2j}/\binom mj\le(2m-1)^j$ by pairing factors. This gives

$$\|a_0+bz+c\bar z\|_{2m}^2\le |a_0|^2+(4m-2)(|b|^2+|c|^2).$$

With the coefficients functions of the remaining phases, take the $L^m$ norm and use the triangle inequality on the right. Iteration charges $4m-2$ only on nonzero-coordinate branches. Thus $\mathbb E |F|^{2m}\le [(4m-2)^R\sum_v c_v^2]^m$.

In the shell expansion of $|S|^{2m}$ all frequencies are $\log(A/B)$ with integers $A,B\le X^{mR}$. A nonzero one has modulus at least $X^{-mR}$. Majorize $1_U$ by a constant times $\operatorname{sinc}^2((u-9t/8)/(2t))$, $\operatorname{sinc}(x)=\sin(x)/x$. Its transform in angular frequency vanishes outside $[-1/t,1/t]$ and its mass is $O(t)$. Since $mR D=O(D^2/(\log D)^3)=o(\log t)$, only the zero frequencies contribute, with coefficient exactly $\mathbb E|F|^{2m}$. This is an integral bound on the continuous shell, not orthogonality on a mesh. Markov's inequality proves (2): Inside the $m$th power, $(4/\delta)^2(4m-2)^R R^{k+2}=\exp(o(D))$, while $NG\asymp X^2$ even before the $H^k$ saving.

**Use and cost.** Partition $[t+\ell,5t/4-\ell]$ into cells of length $V$ with a possible shorter last cell. At each midpoint estimate $\Re S$ to absolute error $\delta/16$; clear the cell if the estimate is at most $\delta/2$. By (1) every cleared cell has $|Q_*|<a^2/2$ throughout. On every flagged cell $|S|\ge\delta/4$ throughout. By (2) their total length is at most $tX^{-(2-o(1))k}$. Subdivide flagged cells at step at most $\ell$ using $\lceil v/\ell\rceil$ equal subintervals for length $v$, including both endpoints. Their node count is $O(1+tX^{-(2-o(1))k}(1/V+1/\ell))$. Including coarse midpoints this takes $O(1+t/X^k)$ evaluations. At the fine nodes test **signed** $Q_*$ with $O(1/n)$ absolute error. Retention, sparse deletion, and the second derivative interpolation bound from the linked cap note give equivalence to the original cap with bounded change of its additive exponent constant. This counts possibly expensive statistics: The explicit coarse sum enumerates up to $NG(2H)^k$ labels before pruning, not one original prime-pair sum. Even this label count is $X^{2+o(1)}$. No bit-time bound is asserted.

## A phase ambiguity shared by all the shifts

Even enforcing one common phase per prime vertex, and giving the complete within-gap magnitude profiles for **all shifts at once**, does not identify the signed decision at a specified ordinate. This can be tested with a single quadratic vertex twist. Let $v$ be an interior ordinate. Multiply the phase at vertex $p$ by $p^{-iv}$ in the first control and by $p^{-iv}e^{i\beta p^2}$ in the second. Take the quotient of endpoint phases on an edge, in the order $(p+d)/p$. Relative to the first control the extra edge factor and the extra factor in the gap sum are, respectively,

$$ e^{i\beta(2dp+d^2)},\qquad e^{-2i\beta dg}. $$

Hence $|P_{d,g}(u)|$ agrees **everywhere** in the two controls for every $d,g$, and their complex within-gap cube statistics agree after the first difference in $p$. No separate twist choices on intersecting chains are needed.

In the first control all $Z_d(v)=A_d=\sum w_p$. By the linked cap note, for sufficiently large fixed $K$ there are $\gg D$ retained shifts with $A_d>1/4$. In the second control, average over uniform $\beta\bmod 2\pi$. For each $d>0$ the distinct start frequencies $2dp+d^2$ in this variable give $\mathbb E_\beta |Z_d(v)|^2=\sum w_p^2\le K/n^2$ for retained $d$. Summing over all retained shifts up to $5D$ gives **one** $\beta$ for which $\max_d |Z_d(v)|\le\sqrt{5DK}/n=o(1)$ on that family. The strip and sparse-group errors use only absolute masses, so the two controls give opposite dense signed cap decisions at $v$ on all the selected large-mass shifts. In fact these decisions persist on one common interval of length $cL$ about $v$, for a sufficiently small fixed $c>0$: Retention gives $A_d=O_K(1)$ by the cell bound in the cap note, so $L|Z'_d|\le 5e^8 A_d$ for either control. These are controls with compatible vertex twists, not untwisted prime examples. They do not preserve $|\Re P_{d,g}|$ or all the complex phases.

**Restoring signed data on a residue class.** There is also a finite test that preserves every $|\Re P_{d,g}|$, not just $|P_{d,g}|$. Apply the extra vertex twist with $\beta=\pi/8$ directly to the *untwisted* fixture. All vertices are odd, so $d,g$ are even; the gap factors are real signs $(-1)^{(d/2)(g/2)}$. Every complex group with $4\mid d$ or $4\mid g$ is unchanged at all heights. At $d=18$ and the genuine node $t+44\ell$, the checker gives

| Data | $\lvert Z_d\rvert$ | $Q_*$ |
|:--|--:|--:|
| Untwisted | $(.178,.179)$ | $(.016,.017)$ |
| Quadratic twist | $(.052,.053)$ | $(-.003,-.002)$ |

The common signed contribution from the groups $4\mid g$ lies in $(.007,.008)$, already greater than $a^2$. The complementary class $g\equiv 2\pmod 4$ changes sign. Thus even restoring the exact complex profiles on the invariant class while keeping the absolute real profiles on *every* group does not determine which side of $a^2$ the signed sum is on here. The contrast is between two phase assignments on the same prime support at the same genuine node, only one of them untwisted; the threshold comparison is finite, not a decision on an eventual cap with unspecified constant.

**Decision.** Use within-gap differencing to shorten the search, not to infer the signed cap at the remaining nodes. For a phase-sensitive next test on a flagged ordinate $u$, keep $P_{d,g}(u)$ complex and form the explicit trigonometric polynomial

$$ B_d(\beta)=\sum_{g\ {\rm dense}}\Re(e^{-2i\beta dg}P_{d,g}(u)). $$

The genuine value is $B_d(0)$, not a random evaluation. One can first test whether the violating angles for the candidate shifts overlap at all: If the superlevel sets on the *same* $\beta$ cannot meet with the required multiplicity, that excludes simultaneous overshoots at zero. If they do overlap, locate them relative to zero, rather than merely pricing their measure. The control shows the limit of any translation-invariant answer to this angular test. The screen and finite signed test give neither a uniform arithmetic exclusion nor the weighted budget for smaller excursions.
