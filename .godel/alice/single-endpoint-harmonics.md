# A single real endpoint tests finitely many zeta ordinates

In the [real-base endpoint setup](../bob/fixed-strip-endpoints.md), fix $1<A<\pi/2$ and $c>0$ with $(2/\pi)\cosh c<1$. A failure of **one** twist at $|y|\ge Y$ forces

$$
\max_{1\le j\le J} B_\zeta(2jy;c)\ \ge\ \delta X^{1/8}
$$

for all sufficiently large $q$, with fixed $Y,J,\delta>0$ independent of the twist and its height. Here $X=(A\log q)^2$, $D=\log X$, and $B_\zeta(t;c)$ is the [zeta packet](../bob/endpoint-zero-packets.md) in $|\gamma-t|\le X^{3/8}D$, $\beta>1/2+c/D$, counting zeros with multiplicity and weight $1/(1+(\gamma-t)^2)$. The implication uses the zeta $7/8$ strip in the cited estimate, not GRH for any twist. For example $A=3/2$, $c=1/2$ admits $J=50$, $Y=5$. The conclusion is a disjunction over frequencies, not a packet at $2y$ in particular.

**Angular bound.** Let $b_p=X^{-1}\log p\log(X/p)$ for $p<X$, of total mass $1+o(1)$. The nonnegative weights and reality of the base and twists give $h_d(y)\le\sum b_p|\cos(y\log p)|$, including at primes where the character vanishes. Write $K=2/\pi$. Integrating against $\cos(2ju)$ on $[-\pi/2,\pi/2]$ gives the absolutely convergent expansion

$$ |\cos u|=K+\sum_{j\ge1}a_j\cos(2ju),\qquad a_j=\frac{4(-1)^{j-1}}{\pi(4j^2-1)}. $$

Partial fractions give $\sum_{j>J}|a_j|=K/(2J+1)=:e_J$, in particular $\sum_{j\ge1}|a_j|=K$. The ordinary single double-angle test only requires $\Re S_\zeta(2y)\ge 2/A^2-1-o(1)$ when $s:=\log(2+|y|)/\log q=o(1)$. At $A\ge\sqrt2$ this gives no positive fixed deficit against zero. This is a limitation of that test, not evidence for failing twists. Uniform angular measure has mean $|\cos|$ exactly $K$, so an error-free mean-value comparison to $1/A$ by this envelope alone has no fixed margin at $A=\pi/2$.

**Spend the height term once.** At a failure, $h_d(y)\ge(1+s)/A-o(1)$ uniformly: First use $h_d\le1+o(1)$ in the own-cutoff identity to get $s=O(1)$, then replace $\log(q|d|)$ by $\log q$ in the height ratio since $|d|\le X^\theta$ for fixed $\theta$. Thus every fixed $j\le J$ is in the domain $\log(2+|2jy|)=O(\sqrt X)$ of the packet estimate (1). For the principal mean $S_\zeta(t)=\sum b_pp^{-it}$, that estimate gives

$$
|\Re S_\zeta(2jy)|\le\frac1{1+4y^2}+\frac{\cosh(c)}{A}s+C X^{-1/8}B_\zeta(2jy;c)+o(1).
$$

Indeed the principal pole has modulus $(1+4j^2 y^2)^{-1}$ and $\log(2+|2jy|)=\log(2+|y|)+O_J(1)$. These errors are uniform at fixed $J$. Use the absolute coefficient sum, **not** one full height cost per mode. Truncation of the envelope now yields

$$
 KC X^{-1/8}\max_{j\le J} B_\zeta(2jy;c)\ \ge\ (1/A-K)+(1-K\cosh c)s/A-e_J-K/(1+4y^2)-o(1),
$$

where the maximum runs from $1$ to $J$. Choose $J,Y$ so $e_J$ and $K/(1+4Y^2)$ are each less than $(1/A-K)/4$. The right side has a uniform positive margin for $|y|\ge Y$, proving the implication. In the example both error budgets are $K/101<(2/3-K)/4$ and $K\cosh(1/2)<1$.

**Consequences and limits.** Even without zeta RH there is *no* failing twist on $Y\le|y|\le\exp(\lambda X^{1/8})$ for sufficiently small fixed $\lambda>0$ in this setup. Use the [principal strip estimate (3)](../bob/resonant-endpoint-heights.md) on the same fixed modes: Each absolute real mean is at most $(1+4Y^2)^{-1}+O(\lambda)+o(1)$. Multiplying by the absolute coefficient mass and taking $\lambda$ small leaves $h_d<1/A$ by a fixed margin. This does not control the pole for $y$ near zero.

Under zeta RH the packets vanish identically, so there is no failure at $|y|\ge Y$ at any height. The existing bounded-band theorem, using the nonprincipal quadratic strip, allows at most one distinct failing twist on $[-Y,Y]$. Together this gives an all-height list of size at most one for $1<A<\pi/2$ without assuming GRH for the product inducers. Away from the strip-controlled band the packet implication alone does not exclude even one failure. These are endpoint-profile statements, not positivity for arbitrary Weil inputs, Alice's $A=2.1$ window, or a proof of any RH.
