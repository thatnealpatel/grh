# A Weil floor in short quadratic twist families about every base

Fix $0<\varepsilon\le 1/4$. There is $c_\varepsilon>0$ with the following property. Start from **any** primitive Dirichlet character $\xi$ of conductor $q$ (including $q=1$). Use fundamental discriminants $1\le |d|\le R$ coprime to $q$, and put $c=q|d|$, $\chi=\xi\chi_d$, where $\chi_d=(d/\cdot)$. These twists are primitive of conductor $c$. Write

$$ U=\log(qR),\qquad L=\log U,\qquad F=U/\log R. $$

Take $R\to\infty$ and $1\le A$ with $AF\le c_\varepsilon L$. Apart from $O_\varepsilon(R^{1/2+\varepsilon})$ discriminants, the compact Weil floor for $\chi$ on the window $D_c=2\log(A\log c)$ is $(1+O(1/L))\log c$. Its lower bound holds on **all** Pick blocks of distinct real nodes $n\ge (\log\log c)^3$, $\sum 1/n\le D_c/2$, relative to $C_{ij}=1/(n_i+n_j)$. Low-energy unit tests, with Gamma energy $G=o(\log c)$ excluding the conductor, have absolute signed prime cost $o(\log c)$. The exceptional set can depend on the base character, $A$, and $R$, but not on the test or the block. The count is uniform in the base; it is not a simultaneous set of good $d$ for all bases.

In particular, for every large prime $q$, even an exception to the [prime quadratic theorem](quadratic-product-window.md), take $\xi=(\cdot/q)$, fix $A>1$, and take $R=\exp(C_{A,\varepsilon}\log q/\log\log q)$ for a sufficiently large constant. Then almost every quadratic twist up to this **subpower** radius has the conductor floor. An exceptional count in the ambient family of conductors near $qR$ would not imply this: It could discard the entire twist family. At the other extreme, $q=1$ gives the same exceptional count in the family of fundamental discriminants up to $R$, not just prime conductors, including $A=c_\varepsilon\log\log R$. Neither application certifies an individual exceptional character.

## A weighted product count in place of distinct conductors

Discard $|d|\le\sqrt R$ at cost $O(\sqrt R)$, so $U/2\le\log c\le U$. Set $X=(AU)^2\exp(L^{-1/2})$, $D=\log X=2L+O(\log L)$, $u_p=(\log p)/\sqrt p$, and $S=\sum_{p\le X}u_p\sim 2AU$. Write $P_\chi(t)=\sum_{p\le X}u_p\chi(p)p^{it}$. We first count discriminants with a witness $|P_{\xi\chi_d}(t_d)|>V$ at $|t_d|\le R^a$. Use $1\le a\le 20AF$, $0<\eta=V/S<1$, and the least even integer $m\ge 8a/\varepsilon$. Below we use only thresholds with

$$ m\log(1/\eta)\le \rho L,\qquad \rho=\varepsilon/16. \tag{1} $$

Let $B$ be the witness count. Rotate each witness by a scalar $z_d$ of modulus one to make its sum positive real. With prime expectation of weights $u_p/S$ and $H(p)=\sum_d z_d\chi_d(p)p^{it_d}$, we have $B\eta\le |\mathbb E_p\,\xi(p)H(p)|\le(\mathbb E_p |H(p)|^m)^{1/m}$. In particular **the base need not be quadratic**. Expand $H^{m/2}\overline H^{m/2}$. At least $(B\eta)^m/2$ ordered tuples have a product-character sum of modulus at least $S\eta^m/2$ at some $|t|\le mR^a$: Each term in the normalized expansion has modulus at most one, and the smaller terms cost at most $(B\eta)^m/2$ in total. Repeated indices are allowed. There is no claim of $\gg(B\eta)^m/m!$ distinct product conductors.

Represent $d$ uniquely by its signed squarefree radicand $v$, with $d=v$ for $v\equiv1\bmod4$ and $d=4v$ otherwise. For a tuple put $n=|\prod_i v_i|$, and let $s$ be the signed squarefree part of $\prod_i v_i$, so $n=|s|h^2$. The product discriminant is $\prod_i d_i=d(s)u^2$ for some integer $u\ge1$: The powers of four from the inputs leave a square after dividing by $d(s)/s$, since if all inputs are $1\bmod4$ then $s\equiv1\bmod4$. (Here an odd square is $1\bmod4$.) Consequently the product character at $p$ equals $\chi_{d(s)}(p)\mathbf1_{p\nmid u}$, including at $2$, and agrees away from primes dividing $2n$ with the primitive character for $s$ (possibly trivial). Replacing it by this character changes the sum by at most $2\sum_{p\mid 2n}u_p\ll\sqrt{\log(2n)+1}$. Indeed split at $\max(2,\log(2n))$, use $\sum_{p\le y}u_p\ll\sqrt y$, and bound the sum of distinct prime logs by $\log(2n)$. Since $m\log R\ll_\varepsilon AU$ and $A\ll L$, this error is $o(S\eta^m)$ by (1). Thus each counted tuple has $|P_{\chi_{d(s)}}(t)|\ge W=S\eta^m/4$ for large $R$.

For each fixed $s$ the number of ordered tuples producing it is at most

$$ 2^m \left\lfloor R^{m/2}/\sqrt{|s|}\right\rfloor\max_{n\le R^m}\tau_m(n)
 \ \le\ R^{m/2+o(m)}/\sqrt{|s|}. \tag{2} $$

Here $\tau_m$ counts ordered positive factorizations into $m$ factors. The first bound chooses the square root $h$, the factors, and their signs. For uniformity in $m\ll_\varepsilon L$, split primes at $U^{1/2}$. Small prime powers $p^v\Vert n$ have $\tau_m(p^v)\le(v+1)^m$, and $\log(v+1)=O_\varepsilon(L)$; their total log cost is $O_\varepsilon(m L\sqrt U)$. Large primes have $\tau_m(p^v)\le m^v$, and their total exponent is at most $2m\log R/L$. Both log costs are $o(m\log R)$ since $\log R\gg_\varepsilon U/L$. The decay in $|s|$ in (2) is essential: The principal product alone can have many preimages.

## Pay for collisions at their reduced conductor

For each dyadic $K\le R^m$ count the possible $s$ with $K\le |s|<2K$. Their primitive characters are distinct and have conductors $\le8K$. At a single time, set $k=\lfloor\log(8K)/D\rfloor$, $N=\lfloor X^k\rfloor\le8K$. For $k\ge1$, apply [Heath-Brown, Corollary 2](https://doi.org/10.4064/aa-72-3-235-275) to the coefficients of the $k$th power. As in the [fixed-order proof](quadratic-product-window.md), the square-pair sum is at most $(2k\sigma^2)^k$, where $\sigma^2=\sum u_p^2\ll D^2$: It is the $2k$th moment for independent prime signs, bounded coefficientwise using $\cosh z\preceq\exp(z^2/2)$. Thus the count at level $W/2$ is

$$ \ll_\nu 1+ K^{1+2\nu}(8k\sigma^2/W^2)^k,\qquad \nu=\varepsilon/32. $$

The $1$ allows the principal character separately. Uniformly $k\ll_\varepsilon AU/L\ll_\varepsilon U$, $\log W\ge(1-\rho)L-O(1)$, and $\log(8k\sigma^2)\le L+O_\varepsilon(\log L)$. Since $D=2L+O(\log L)$, the moment ratio to the power $k$ is at most $\exp(O(L)) K^{-1/2+2\rho}$, including the floor loss. For $k=0$, the trivial $O(K)$ count also satisfies the resulting $\exp(O(L))K^{1/2+2\rho+2\nu}$ bound because $8K<X$. A grid of spacing at most $W/(2SD)$ covers the product times since $|P'|\le SD$. It takes $O(1+mR^a SD/W)=R^{a+o(1)}$ points. The rounding loss $\exp(O(L))$ is $R^{o(1)}$, not an uncontrolled power of the much larger base conductor.

Multiply the count on this grid by (2). The $K^{1/2}$ in the sieve cancels the $K^{-1/2}$ in the multiplicity bound. Summing over $O(1+m\log R)$ dyadic intervals and comparing with the Jensen lower bound gives

$$ (B\eta)^m/2\le R^{m/2+a+(2\rho+2\nu)m+o(m)}. $$

The errors are uniform over our bands for fixed $\varepsilon$. Since $\eta^{-1}=R^{o(1)}$ and $a/m\le\varepsilon/8$, this leaves slack to take a logarithmic union while keeping $O_\varepsilon(R^{1/2+\varepsilon})$ exceptions. The estimate uses a fixed-time quadratic sieve only.

## Use the height budget in units of the twist radius

Take $a_j=2^j$ from $a_0=1$ to the first $a_J\ge10AF$. At $j=0$ use $V_0=U/L$. On the subsequent cutoffs use $V_j=a_j\log R/16$, applying the estimate only above $R^{a_j/2}$. Levels $V_j\ge S$ require no count. At level zero, $m=O_\varepsilon(1)$ and $\log(S/V_0)=O(\log L)$. At the others, $S\le3AU$ eventually gives

$$ m\log(S/V_j)\le (8/\varepsilon+2)a_j\log(48AF/a_j)\le (8/\varepsilon+2)(48/e) AF. $$

Choose $c_\varepsilon\le \rho/[48(8/\varepsilon+2)]$. This verifies (1), even at the stated boundary with a small fixed constant. The number of bands is $O(1+\log L)$.

For the good $d$, truncate the full-line signed two-shift operator at $X$, calling it $T$. Its multiplier is $2\Re P_\chi$ plus a term of modulus $O(D)$ (squares by partial summation, higher powers by absolute convergence). On the lowest band the prime part is bounded by $2U/L$, on intermediate bands by $(\log|t|)/4$, and above $R^{a_J}$ the entire absolute multiplier is at most $(4+o(1))AU\le (\log|t|)/2$. In both parities the Gamma symbol plus an absolute $C$ dominates $\log(2+|t|)$. Integration on the Fourier mass of each unit test gives

$$ |\langle Th,h\rangle|\le 2U/L+O(D)+(G(h)+C)/2. $$

For compact tests $X$ contains all active shifts. Subtract this bound from $\log c+G(h)$ and use $G(h)\ge-C$, $U\le2\log c$. A fixed unit smooth test of diameter less than $\log 2$ gives the reverse floor bound $\log c+O(1)$. For blocks, set $s_0=(\log\log c)^2$ and $J_0=\sum_n\log((n+s_0)/(n-s_0))$. The [block tail estimate](../adhoc/prime-translation-norm.md#4-a-whole-block-conductor-estimate) gives the autocorrelation bound $e^{J_0-s_0 t}$ for $t\ge0$, with $J_0/s_0\le D_c+O(1/L)$ by Taylor expansion and the node assumptions. Since $D\ge D_c+L^{-1/2}$, the shifts omitted above $X$ cost $O(\exp(J_0-(s_0-2)D))=o(1)$ per unit input. This proves the same lower bound without a rank restriction or any Fourier support assumption.

## A sharper alternative for the unmodulated endpoint alone

Let $q$ be any large odd prime, $\xi=(\cdot/q)$, $1<A<2$ fixed, $X_0=(A\log q)^2$, and $K>0$ fixed. Among **all** $|d|\le(\log X_0)^K$, at most one fundamental discriminant can have a nonpositive Weil quotient on its own unmodulated endpoint profile. This includes $d=1$ and does not require that $q$ pass any sieve. More quantitatively, for two distinct such $d_1,d_2$, let $H_i$ denote the [signed endpoint mean](endpoint-arithmetic-test.md) $H_{\xi\chi_{d_i}}(X_i,0)$ at $X_i=(A\log(q|d_i|))^2$. Then

$$ |H_1|+|H_2|\le 1+o_{A,K}(1). \tag{3} $$

To see this use the common positive prime weight $b_p=X_0^{-1}\log p\,\log(X_0/p)$ on $p<X_0$, zero otherwise. Its mass is $1+o(1)$ by PNT. The means $H_i$ equal $\sum_p b_p\xi(p)\chi_{d_i}(p)+o(1)$ uniformly: Prime powers contribute $O(X_i^{-1/2}\log^3 X_i)$, and $X_i/X_0=1+o(1)$ uniformly. For the latter replacement use $\sum_{p<x}\log p\,\log(x/p)\ll x$ and $\sum_{p<x}\log p\ll x$: Between the cutoffs the new log weights are at most $|\log(X_i/X_0)|$. Choose signs $e_i$ to take absolute values of the two real prime means. For $z_i=e_i\chi_{d_i}(p)\in\{-1,0,1\}$ one has $|z_1+z_2|\le1+z_1z_2$. Thus the sum of absolute values is at most

$$ \sum_p b_p + \left|\sum_p b_p\chi_{d_1}(p)\chi_{d_2}(p)\right|. $$

The product is a nonprincipal character modulo $\operatorname{lcm}(|d_1|,|d_2|)\le(\log X_0)^{2K}$, since the primitive inputs are distinct. By the Siegel-Walfisz theorem and partial summation its last signed mean is $o_K(1)$ uniformly (ineffectively). In detail, integrate the signed prime-log sum up to $v$ against $dv/(vX_0)$ for $1\le v\le X_0$: Below $\sqrt{X_0}$ use $O(v)$, and above it the modulus is at most $(\log v)^{2K+1}$ eventually, so the sum is $o_K(v)$. This proves (3).

On profile $i$ the unit Weil quotient is $(1-AH_i)\log(q|d_i|)+O(1+\log X_i)$, by the endpoint formula with its bounded Gamma energy. If $d=1$ gives a nonpositive quotient, then $H_1\ge1/A-o(1)$. Every other indicated twist has $H_i\le 1-1/A+o(1)$, hence **positive margin at least $(2-A-o(1))\log q$ on that profile**. Its log-weighted nonresidue mass (normalized by $X_i$) is at least $1/(2A)-o(1)$: Primes dividing $q d_i$ have weight $o(1)$, and the total mass is $1+o(1)$. This controls mass rather than the first nonresidue. It neither rules out the original endpoint exception nor makes a statement about all tests on these much shorter twist families.

**Next decision.** This is a local density bound, not propagation of positivity back to the base. In particular it does not force $d=1$ to be good. To shrink the twist radius at fixed $A$, test the middle band $a\asymp AF$ where $V/S$ is a fixed fraction. With $m\gg_\varepsilon a$, condition (1) fails for $F\gg L$, regardless of the collision count. An improvement there has to preserve more correlation through the product step, reduce the height cost, or use information on the base itself. For a truly individual result the [endpoint obstruction](endpoint-arithmetic-test.md) remains.

For the endpoint alone there is a different next test. To rule out *two nonpositive quotients* one need not extend the absolute bound (3). In its proof use $z_i=\chi_{d_i}(p)$ without rotating either sign. It suffices to bound the **upper** prime mean $\sum b_p\chi_{d_1}(p)\chi_{d_2}(p)$ by $2/A-1-\kappa$ for fixed $\kappa>0$. Test that bound when $|d_i|\le X_0^\theta$ for a sufficiently small constant $\theta(A)>0$, keeping the sign of any exceptional-real-zero term. This would extend the at-most-one conclusion to powers of $\log q$; it would still not identify which twist is the exception.

**Update.** The [power-radius endpoint proof](power-radius-endpoint.md) closes this one-sided test using the long-interval progression theorem with its signed secondary term. For modulations tending to zero it leaves at most two candidate twists, and a surviving opposite-sign pair must have exceptional product character. The possible base exception and the whole-window height problem remain.
