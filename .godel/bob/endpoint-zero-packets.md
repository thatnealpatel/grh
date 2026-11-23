# What a failing endpoint would cost in off-line zeros

For two failures of distinct twists of the same real base, the Gamma terms pay for **all near-critical-line zero residues** of their product character, even at power heights. The remaining residues must carry a positive fixed amount. At the [nonresonant test pair](resonant-endpoint-heights.md#what-remains) there is also such a requirement on zeta alone. Neither requirement asserts the existence of an actual failing endpoint.

Use the [own-cutoff endpoint identity and signed-pair inequality](fixed-strip-endpoints.md#signed-pairs-versus-the-gram-bound), with $1<A<2$, fixed $\theta>0$, $X=(A\log q)^2$, $D=\log X$, and $b_p=X^{-1}\log p\log(X/p)$ for $p<X$. Use the same $7/8$ strip as [in the resonance proof](resonant-endpoint-heights.md), for the primitive real nonprincipal product inducer or for zeta, respectively. Put $H=X^{3/8}D$. For one of these $L$-functions write, counting nontrivial zeros with multiplicity,

$$ B_L(t;c)=\sum_{\substack{\rho=\beta+i\gamma:\ |\gamma-t|\le H\\ \beta>1/2+c/D}}\frac1{1+(\gamma-t)^2}. $$

* **Any two failures.** If twists $i\ne j$ fail at $y_i,y_j$ respectively, let $L=L(s,\psi^*)$ for the primitive inducer of $\chi_{d_i}\chi_{d_j}$. For every fixed $c>0$ with $(A-1)\cosh c<1$, and all sufficiently large $q$, at least one of $t=y_i+y_j$ and $t=y_i-y_j$ has $B_L(t;c)\gg_{A,c} X^{1/8}$. The conductor of $L$ divides $M=[|d_i|,|d_j|]\le X^{2\theta}$. In particular, if the product inducers all satisfy GRH, there is at most one failing twist over **all** endpoint heights, without assuming GRH for the high-conductor base twists. Local packet bounds at the two witness combinations would suffice in place of product GRH.
* **One high witness.** At $A=9/5$, failure of any single real twist at $y=q^{3/5}$ forces $B_\zeta(2y;c)\gg_c X^{1/8}$ for each fixed $0<c<\operatorname{arcosh}(47/27)$. No second twist or product-character hypothesis is needed for this implication. It is a weighted count, not a claim of distinct ordinates or of a positive fraction of the zeros.

## Price the part near the critical line

Write $f$ for the conductor ($1$ for zeta) and $S_L(t)=\sum_{p<X} b_p\psi(p)p^{-it}$, with $\psi$ the possibly imprimitive product or identically one for zeta. The sign of $t$ centers the residues at $+t$; the real prime mean is unchanged. Uniformly for $\log(f(2+|t|))=O(\sqrt X)$, we claim

$$ |S_L(t)-P(t)|\le\cosh(c)\frac{\log(f(2+|t|))}{\sqrt X}+C X^{-1/8}B_L(t;c)+o(1), \tag{1} $$

where $P(t)=0$ for the nonprincipal character, and $P(t)=X^{-it}/(1-it)^2$ for zeta. The leading coefficient, not a big-$O$ estimate on the first term, is needed. All little-$o$ terms are for fixed $c,\theta$ and fixed height-growth constant.

The [strip contour](strip-edge-height.md#a-uniform-residue-bound-on-the-original-weight) and its [zeta version](resonant-endpoint-heights.md#odd-coefficients-an-exclusion-independent-of-the-base-conductor-in-the-prime-estimate) give $S_L-P$ as $-\sum_\rho X^{\rho-it-1}/(\rho-it)^2+o(1)$. Indeed the vertical at $1/16$ costs $O(X^{-15/16}\log(2f(2+|t|)))$, higher powers cost $O(X^{-1/2}D^3)$, and missing Euler factors at primes dividing $M$ cost $O(D\log M/X)$. The reflected strip puts $1/8\le\beta\le7/8$. With $u=\gamma-t$, a unit-interval zero count $O(\log(2f(2+|\gamma|)))$ gives

$$ \sum_{|u|>H}\frac{1}{1+u^2}\ll \frac{\log(2f(2+|t|))+\log(2+H)}{H}. $$

This follows by summing $j^{-2}(\log(2f(2+|t|))+\log(2+j))$ outside the window. Even charging every tail zero $O(X^{-1/8}/(1+u^2))$ costs $O(1/D)$.

To price zeros inside the window, put $\sigma=1+1/D$ and $K_0(u)=(1/4+u^2)^{-1}$. For the entire completion $\mathcal L$ (including $s(s-1)$ for zeta) we have

$$ \sum_\rho\frac{\sigma-\beta}{(\sigma-\beta)^2+u^2}=\Re\frac{\mathcal L'}{\mathcal L}(\sigma+it)\le\tfrac12\log(f(2+|t|))+O(D^2+1). \tag{2} $$

For the identity, subtract Hadamard log derivatives at $\sigma+it$ and $1-\sigma+it$. The functional equation and conjugation double the real part on the right. Reflection $\beta+i\gamma\leftrightarrow1-\beta+i\gamma$ makes the two convergent sums of real kernels equal on the left. For the bound use the conductor and Gamma factors (half the displayed logarithm, up to $O(1)$ by Stirling or bounded height), and $|L'/L|\le\sum_{n\ge2}(\log n)n^{-\sigma}\ll D^2$. For zeta the two rational terms cost at most $O(D+1)$, even near $t=0$. The same identity at $\sigma=2$ gives the unit count above. Every summand in (2) is positive.

On the good local set $|u|\le H$, $|\beta-1/2|\le c/D$, the kernel in (2) is $(1+O_c(1/D))K_0(u)/2$, **uniformly in $u$**. Likewise $(\beta^2+u^2)^{-1}=(1+O_c(1/D))K_0(u)$. The numerators of the absolute residues of a reflected pair sum to $2X^{-1/2}\cosh((\beta-1/2)D)$; a zero on the line contributes $X^{-1/2}$ per copy. Thus the entire good set costs at most

$$ \frac{\cosh c}{\sqrt X}(1+O_c(1/D))\sum_{\rm good} K_0(u)\le \cosh(c)\frac{\log(f(2+|t|))}{\sqrt X}+o(1) $$

by (2), dropping the positive Poisson terms from outside the set. No asymptotic local zero count and no cancellation of phases is needed. Pair the other local zeros by reflection: Each right member counted by $B_L$ and its left partner together cost at most $C X^{-1/8}/(1+u^2)$ by the full strip. This proves (1).

## Spend the Gamma margin

Write $s_l=\log(2+|y_l|)/\log q$. Since $h_l\le1+o(1)$, failure at its own cutoff forces $s_l\le A-1+o(1)$ uniformly; $\log(q|d_l|)=\log q+O_\theta(D)$. The signed-pair lower bound on the average real product mean is $(2-A+s_i+s_j)/A-o(1)$. At $t=y_i\pm y_j$ we have $\log(f(2+|t|))/\sqrt X\le\max(s_i,s_j)/A+o(1)$, including coincident or opposite heights. The difference between the required average and the first term of (1) is therefore at least

$$ \frac{2-A+\min(s_i,s_j)-(\cosh c-1)\max(s_i,s_j)}{A}-o(1)\ \ge\ \frac{1-(A-1)\cosh c}{A}-o(1). $$

A positive fixed gap forces the claimed mass at one of the two ordinates. No division by an individual $s_l$ is involved. For $A=9/5$, $y_i=q^{1/5}$, $y_j=q^{3/5}$, keeping the smaller Gamma term gives the sharper pair-specific range $\cosh c<5/3$: The threshold is $5/9$ and the good cost is $\cosh(c)/3+o(1)$.

For the principal test at $y=q^{3/5}$, reality and Cauchy–Schwarz give $h_j(y)^2\le(\sum b_p)\sum b_p\cos^2(y\log p)$. Failure requires $h_j(y)\ge8/9-o(1)$, hence $\Re S_\zeta(2y)\ge47/81-o(1)$. The pole is $o(1)$ there, and $\log(2+2y)/\sqrt X=1/3+o(1)$. Subtract $\cosh(c)/3$ to obtain the second claim. The principal and product packets need not belong to the same function or to the same ordinate.

**Remaining test.** At the named nonresonant pair it would now suffice to show $B_\zeta(2q^{3/5};1)=o(X^{1/8})$ (indeed $\cosh 1<47/27$); alternatively bound the *signed* contribution left by the off-line pairs in (1). A global density estimate averaged over $t$ is not a uniform packet bound at this moving center. Neither the $7/8$ strip nor (2) excludes the required packets. No counterexample to RH, unconditional all-height list of size one, or floor for unrestricted Weil inputs follows.
