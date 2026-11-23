# One-sided prime means at power-sized twist radius

Fix $1<A<2$, put $b=2/A-1>0$, and let $X=(A\log q)^2$ for a large prime $q$. There is a constant $\theta=\theta(A)>0$ such that among fundamental discriminants $|d|\le X^\theta$ at most one twist $(\cdot/q)\chi_d$ has nonpositive Weil quotient on its **unmodulated endpoint** at its own cutoff. If the base endpoint fails, each nontrivial twist here has quotient at least $((2-A)/2-o_A(1))\log q$ on that profile. This closes the [one-sided test](local-quadratic-twists.md) without an absolute prime-sum bound.

## The arithmetic input

For distinct $d_1,d_2$ in the family, let $m=\operatorname{lcm}(|d_1|,|d_2|)\le X^{2\theta}$ and $\psi=\chi_{d_1}\chi_{d_2}$ on the units modulo $m$, extended by zero. This real character is nonprincipal: If the primitive inputs agreed on the units modulo $m$, they would have the same primitive inducing character. Use $m$ itself, not just the conductor of $\psi$. Write

$$S_\psi(v)=\sum_{p\le v}\psi(p)\log p,\qquad M_\psi(X)=\frac1X\sum_{p<X}\psi(p)\log p\,\log(X/p)=\frac1X\int_1^X S_\psi(v)\,\frac{dv}{v}.$$

[Thorner and Zaman, *Refinements to the prime number theorem for arithmetic progressions*, Corollary 1.4 and Remark 1.5](https://arxiv.org/abs/2108.10878v2) give, for $v\ge m^{12}$, a prime-log sum in each reduced class $a$ of $\lambda_a v/\varphi(m)$ with relative error $O(E_m(v))$, where for an absolute $c>0$

$$E_m(v)=\exp(-c\log v/\log m)+\exp\big(-c(\log v)^{3/5}/(\log\log v)^{1/5}\big).$$

Here $\lambda_a=1$ in the absence of the exceptional zero for this modulus; otherwise $\lambda_a=1-\chi_1(a)v^{\beta_1-1}/\beta_1$, in the notation of the corollary. These factors are nonnegative and average to one over the units. Multiply by $\psi(a)$ and sum. The ordinary main term vanishes; by orthogonality the secondary main term is either zero or **negative**:

$$S_\psi(v)=-\mathbf1_{\psi=\chi_1}\,v^{\beta_1}/\beta_1+O(v E_m(v)),$$

with the first term omitted when there is no exceptional character. The relative errors need not have the same sign: Their absolute sum is $O(vE_m(v))$ by the mean of $\lambda_a$. Working with reduced classes already accounts for primes dividing $m$.

Choose $0<\theta\le1/48$. Then $m^{12}\le\sqrt X$. Below $\sqrt X$ use $|S_\psi(v)|\ll v$, giving $O(X^{-1/2})$ in the integral. Above it $\log v/\log m\ge1/(4\theta)$, and the second exponential tends to zero uniformly. Thus for an absolute $C$ we get $M_\psi(X)\le C\exp(-c/(4\theta))+o(1)$, with the same bound for $|M_\psi(X)|$ **if the secondary term vanishes**. Shrink $\theta(A)$ until the constant term is at most $b/4$. For large $q$ we have $M_\psi(X)\le b/2$ uniformly. The estimate needs a fixed margin, not an $o(1)$ error at fixed $\theta$.

## Transfer to the actual profiles

Put $b_p=\log p\,\log(X/p)/X$ on $p<X$, and $h_i=\sum b_p\xi(p)\chi_{d_i}(p)$, where $\xi$ is the Legendre character modulo $q$. In the [endpoint formula](endpoint-arithmetic-test.md) the signed mean at $X_i=(A\log(q|d_i|))^2$ equals $h_i+o(1)$ at height zero, uniformly: $X_i/X=1+O_A(\log X/\log q)$, prime powers cost $O(X_i^{-1/2}\log^3 X_i)$, and changing the cutoff costs $O(|\log(X_i/X)|)$ by $\sum_{p\le v}\log p\ll v$ and partial summation. In particular the unit quotient is $(1-Ah_i+o(1))\log(q|d_i|)$.

For either common sign $e=\pm1$, $|e\chi_{d_1}(p)+e\chi_{d_2}(p)|\le1+\psi(p)$, including zeros. Since $\sum b_p=1+o(1)$, we get $e(h_1+h_2)\le1+b/2+o(1)$. Two nonpositive unmodulated quotients would require $h_1+h_2\ge2/A-o(1)=1+b-o(1)$. If $d_1=1$ fails, then $1-Ah_2\ge2-A-Ab/2-o(1)=(2-A)/2-o(1)$ as claimed. No argument singles out the base as good.

**Remaining sign issue.** Even a height tending to zero can reverse the sign. For any $Y(q)=o(1)$ and $|y|\le Y(q)$ the same twist's real endpoint mean is $h_i\cos(y\log X)+o(1)$ uniformly. Indeed $|p^{iy}-X^{iy}|\le |y|\log(X/p)$, and $\sum b_p\log(X/p)=O(1)$ by integrating the Chebyshev bound twice. The cutoff and prime-power errors above are unchanged in absolute value. Thus $y=\pi/\log X$ reverses the mean up to $o(1)$, with bounded Gamma energy. A nonpositive quotient somewhere in $|y|\le Y(q)$ requires $|h_i|\ge1/A-o(1)$. At most **two** discriminants can do this: Three would have two $h_i$ of the same sign, already excluded. For a remaining opposite-sign pair the same pointwise inequality with opposite choices of signs gives $|h_1|+|h_2|\le1-M_\psi(X)+o(1)$. Hence such a pair requires the product to be the exceptional character modulo $m$ and $M_\psi(X)\le-b+o(1)$. This is a necessary condition, not an example. To recover at-most-one for these modulations, address that opposite-sign case, not the one-sided unmodulated estimate. This does not control arbitrary heights or the full Weil floor.
