# A bounded exceptional list for compact Weil tests with low Gamma energy

Fix $A\ge1$, $0<\theta<2$, and $0<u<1-\theta/2$. Let $\xi$ be **any** primitive character of large conductor $q$, $X=(A\log q)^2$, and use fundamental discriminants $|d|\le X^\theta$ coprime to $q$, including $d=1$. The twist $\chi=\xi\chi_d$ has conductor $c=q|d|$. Write $D_c=2\log(A\log c)$, and normalize tests to unit $L^2$ norm. Put

$$ B=\left\lfloor\frac{2A^2}{1-u-\theta/2}\right\rfloor. $$

There are $\eta,\nu>0$ depending only on the three fixed parameters such that, outside at most **$B$ discriminants**, the Weil quotient is at least $\nu\log c$ for **every** test of diameter at most $D_c$ with at most $\eta$ of its squared Fourier mass outside $[-X^u,X^u]$ (Plancherel normalization). In particular this holds for all tests of Gamma energy $G\le c_0\log X$ for a sufficiently small fixed $c_0>0$, where $G$ excludes the conductor. Indeed the Gamma symbol in either parity is $\log(2+|t|)+O(1)$. No compactly supported test is required to be exactly band limited. The same exceptional set works on the [Pick blocks](../adhoc/prime-translation-norm.md#4-a-whole-block-conductor-estimate) with the same Fourier-mass restriction on the input. This is a restricted floor, not positivity for every vector on those blocks.

For instance, at $A=3/2$ and $|d|\le X$, there are at most nine exceptions for sufficiently small fixed $u>0$. For $1<A<\sqrt{3/2}$ and sufficiently small fixed $u,\theta>0$, there are at most two. The distinction from the [power-radius endpoint bound](power-radius-endpoint.md) is that the witnesses may have **different shapes**, not just different characters and modulations. At sufficiently small power radius, the matching argument below improves the arbitrary-shape count to $2\lfloor A^2\rfloor$ even with $u=1/32$. For the real Legendre base and $1<A<2$, it leaves at most two modulated endpoint exceptions and restricts the separation of their heights.

## Short cells: Sieve the Gram form, not the base character

Take $N=B+1$ putative exceptions. Choose $u<\alpha<1$ and $\gamma>0$ so that

$$ 2\gamma+\alpha+\theta/2<1,\qquad 1/\gamma<N/A^2. \tag{1} $$

This uses the strict inequality for $N$, even when the expression inside the floor is integral. Put $z=X^\gamma$. On any interval $I\subset[sX,2X]$ of length $h\asymp X^{1-\alpha}$, with $s>0$ fixed, write $m_i=h^{-1}\sum_{p\in I}\xi(p)\chi_{d_i}(p)\log p$ and $b_I=h^{-1}\sum_{p\in I}\log p$. We claim, uniformly in the chosen $N$ distinct discriminants and the cell, that

$$ \sum_{i=1}^N |m_i|^2\le (1/\gamma+o(1)) b_I. \tag{2} $$

No short-interval asymptotic for $b_I$ is needed. By duality and Cauchy-Schwarz on the prime measure, it suffices to bound $h^{-1}\sum_{p\in I}\log p\,|\sum_i v_i\chi_{d_i}(p)|^2$ by $1/\gamma+o(1)$ for $\|v\|_2=1$. This step removes $\xi$, even if it is complex or vanishes at some active primes.

Use the Selberg square $W(n)=(\sum_{k\mid n,\ k\le z}\lambda_k)^2$, which is one at primes in $I$. Here are the normalizations. Put $J=\sum_{j\le z}\mu^2(j)/\varphi(j)\ge\sum_{n\le z}1/n\ge\log z$: Group by the radical of $n$ and extend the exponents to infinity. Define $y_j=\mu(j)/(J\varphi(j))$, $\lambda_k=k\sum_{k\mid j,\ j\le z}\mu(j/k)y_j$. Then $\lambda_1=1$ and $|\lambda_k|\le1$. Indeed for squarefree $k$ the absolute numerator is $(k/\varphi(k))\sum_{l\le z/k,(l,k)=1}\mu^2(l)/\varphi(l)$, at most $J$ by inserting all divisors of $k$ into the latter sum; nonsquarefree $k$ give zero. Divisor inversion and $\sum_{a\mid(d,e)}\varphi(a)=(d,e)$ give

$$ \sum_{d,e\le z}\frac{\lambda_d\lambda_e}{[d,e]}=\sum_{j\le z}\varphi(j)y_j^2=1/J,\qquad \sum_{n\in I}W(n)=h/J+O(z^2). $$

In the sieved Gram form on integers, each diagonal is at most this last sum by positivity. For an off-diagonal character $\psi=\chi_{d_i}\chi_{d_j}$ modulo $m=[|d_i|,|d_j|]\le X^{2\theta}$, its primitive inducing character is nonprincipal by distinctness. For any fixed $r\ge2$, on intervals of length $T\ge1$ its sum is

$$ \ll_{r,\epsilon} T^{1-1/r}X^{\theta(r+1)/(2r^2)+\epsilon}. \tag{3} $$

Here we use the classical cubefree [Burgess inequality](https://arxiv.org/abs/2511.17778) on **integers**, not a Burgess bound on primes. To check the modulus, remove primes of $m$ absent from the primitive conductor by inclusion-exclusion, at cost $2^{\omega(m)}=X^{o(1)}$ terms. Each is a character constant times a primitive sum on a rescaled interval, of at most $T+1$ integers. The primitive character is a product of a character of conductor dividing 8 and one of odd squarefree conductor $k\le X^{2\theta}$. If $k>1$, split by residues modulo 8: The odd part on each progression becomes a constant times an ordinary shifted interval sum modulo $k$ because $8$ is invertible. Burgess gives $\ll_{r,\epsilon'}(1+T)^{1-1/r} k^{(r+1)/(4r^2)+\epsilon'}$, uniformly in the starting point. Full periods may be discarded. For $k=1$ the nonprincipal primitive part alone has bounded interval sums by periodicity. This also handles endpoints of the rescaled intervals of length below one. Thus (3) covers erased primes and conductors divisible by eight without using a high-$r$ bound modulo a noncubefree conductor.

Expand $W$. Each $d,e$ costs at most the bound (3) for $T=h/[d,e]\gg1$, since $\psi([d,e]b)=\psi([d,e])\psi(b)$. Writing $d=ga$, $e=gb$, $(a,b)=1$, and dropping coprimality after bounding absolute values gives

$$ \sum_{d,e\le z}[d,e]^{-1+1/r}\ll_r z^{2/r}\sum_{g\le z}g^{-1-1/r}\ll_r z^{2/r}. $$

After division by $h$, the off-diagonal is $\ll_{r,\epsilon}(z^2/h)^{1/r}X^{\theta(r+1)/(2r^2)+\epsilon}$. By (1) first choose $r$ large and then $\epsilon$ small to save a fixed power of $X$. The diagonal remainder $z^2/h$ also saves a power. Since $N$ is fixed, multiplying the sieved form by $\log(2X)/h$ proves the required dual bound and hence (2). Positivity is used *before* expanding the square, not to majorize a signed character sum term by term.

## Turn the prime measure into one crossing operator

Use a common upper endpoint $Y=(A\log(qX^\theta))^2\exp((\log\log q)^{-1/2})=(1+o(1))X$, $D=\log Y$. A compact input can be translated into $[0,D]$ and zero-extended. Its unit Weil value is $\log c+G$ minus the signed two-shift prime form with coefficients $\chi(n)\Lambda(n)/\sqrt n$, truncated at $Y$ since larger shifts have zero correlation. The [$O(\log Y)$ cost of squares and higher powers](local-quadratic-twists.md) and the $O(\sqrt{sX})$ cost of primes below $sX$ follow by partial summation. Partition $[sX,Y]$ into equal cells of length $h\asymp X^{1-\alpha}$. On each cell extend $m_i$ as a constant function $m_i(v)$.

In the forward form replace the prime weights by $m_i(v)\,dv/\sqrt v$ at translation $\log v$. This replacement is valid on the stated **inputs**, not in operator norm. The correlation $C_f(t)=\langle f,U_t f\rangle$ is the Fourier transform, up to sign convention, of its unit spectral measure. On shifts in the same cell, $|C_f(\log v)-C_f(\log p)|\le O_s(X^{u-\alpha})+2\eta$ by splitting at $X^u$. The relative variation of $v^{-1/2}$ is $O_s(X^{-\alpha})$. Subtract cell averages of $v^{-1/2}C_f(\log v)$ from the prime samples; the summed error in the two directions is $O(\eta\sqrt X)+o_s(\sqrt X)$ since $\sum_{p\le Y}\log p/\sqrt p\ll\sqrt X$. This avoids differentiating the input. The part discarded at $sX$ is bounded before any smoothing.

For $\log v\ge\log(sX)>D/2$, the smeared forward shift on $[0,D]$ only maps the right half to the left half. Its integral kernel at $x<y$ is $e^{(y-x)/2}m_i(e^{y-x})$ on the indicated differences and zero otherwise. Denote this crossing block by $K_i$. The symmetric form has norm $\|K_i\|$, not $2\|K_i\|$, by the off-diagonal block decomposition. Integrating the squared kernel along lines of constant difference gives exactly

$$ \|K_i\|_{\rm HS}^2 = \int_{sX}^Y \log(Y/v)\,|m_i(v)|^2\,dv. $$

Thus the endpoint log weight also controls tests **not** of endpoint shape. Summing over $i$, apply (2). The analogous integral with $b_I$ in place of $|m_i|^2$ is at most $(1+o(1))Y$: Coarsening $\log(Y/v)$ on each cell costs $O_s(X^{-\alpha})$ times the total prime-log mass $O(Y)$, and the ordinary PNT gives $\sum_{p\le Y}\log p\log(Y/p)=(1+o(1))Y$. No equidistribution of primes within the individual cells was used for this trace. We conclude that

$$ \sum_{i=1}^N \|K_i\|^2\le (1/\gamma+o(1))X. \tag{4} $$

At least one of the $N$ norms is $\le (1/\sqrt{N\gamma}+o(1))\sqrt X$. On that twist *all* the indicated inputs have signed prime cost at most $(1/\sqrt{N\gamma}+O(\sqrt s+\eta)+o_s(1))\sqrt X$. By (1), this is strictly below $\sqrt X/A=\log q$ by a fixed fraction after taking $s$ and $\eta$ small. Since $G\ge-O(1)$ and $\log c/\log q\to1$ uniformly, one can choose a fixed $\nu>0$. This contradicts the choice of $N$ witnesses to failure of the margin.

For the block assertion take distinct real nodes $m\ge (\log\log c)^3$ and $\sum 1/m\le D_c/2$, and form the normalized exponential polynomial on the half-line. With $b=\log\log c$, $t_0=b^2$, the [block tail bound](../adhoc/prime-translation-norm.md#4-a-whole-block-conductor-estimate) gives $\|1_{[t,\infty)} f\|_2\le e^{J_0-t_0t}$ with $J_0/t_0\le D_c+O(1/b)$. Thus the shifts beyond $Y$ in its full formula cost $O(e^{J_0-(t_0-2)D})=o(1)$ and the norm beyond $D$ is $o(1)$. Smooth the correlations on the **original** input satisfying the Fourier condition. In the resulting operator only, truncate this input to $[0,D]$ at cost $o(\sqrt X)$, since $\int_{sX}^Y|m_i(v)|\,dv/\sqrt v\ll\sqrt X$ by the absolute prime bound on the cells. Then (4) applies unchanged, also for a list mixing block and compact witnesses. No Gamma estimate on an abruptly truncated input is needed.

## Small power radius: Keep the exceptional character in the Gram matrix

For each fixed $A\ge1$ one can take $u=1/32$ and $\theta(A)>0$ sufficiently small and improve the list from $B$ to **$2\lfloor A^2\rfloor$**, still for all the compact tests and block inputs above. This improvement records the arithmetic structure of possible exceptions. In a set of bad twists, any sublist without an exceptional-product pair has size at most $\lfloor A^2\rfloor$, with exceptionality tested at the common modulus of the list under consideration (of fixed bounded size).

Take $N=2\lfloor A^2\rfloor+1$ candidates and $M$ the lcm of their discriminant magnitudes, so $2\le M\le X^{N\theta}$. In this section use $\alpha=1/16$. [Thorner and Zaman, Theorem 1.1 and (1.8)](https://arxiv.org/abs/2108.10878v2) give a main term $\lambda_a h/\varphi(M)$ for prime-log mass in each reduced class, with relative error of absolute value at most any prescribed $\delta>0$ for small enough fixed $\theta$ and large $X$. In detail the right endpoint $x\asymp_s X$ and $h\asymp X^{15/16}$ satisfy $h\ge x^{1-1/15}$, $M\le x^{2N\theta}$, and $1/15+3N\theta<1-32/37-1/100$ for small $\theta$. This verifies the depleted-class hypothesis $\lambda_a h/\varphi(M)\ge x^{32/37+1/100}$ using their effective $\lambda_a\gg M^{-1/2}$, not merely the upper bound $\lambda_a<2$. The denominator in their error exponent is $\log M+O((\log x)^{2/3}(\log\log x)^{1/3}+(\log x)^{2/5}(\log\log x)^{1/5})$, so the fixed relative precision follows. The nonnegative $\lambda_a$ have mean one, and their only possible nonconstant component is the unique exceptional real character modulo $M$, independent of the cell. We may take $M<sX$; no sampled prime divides $M$.

In fact $\lambda_a=1-\rho_I\chi_1(a)$ if the exceptional character $\chi_1$ exists, with $0\le\rho_I\le1$; otherwise $\lambda_a=1$. Multiplication by $\chi_1$ pairs some of the distinct quadratic lifts in a matching, the same in every cell. Select a subset $S$ of at least $\lceil N/2\rceil$ with no matched pair. The lifts indexed by $S$ remain orthonormal under the probability measure $\lambda_a/\varphi(M)$ on units: The putative extra Gram entries vanish by ordinary character orthogonality. Applying Cauchy-Schwarz as for (2), the cell's total prime-log density is at most $1+\delta$, and the Gram upper bound for the selected characters is also $1+\delta$ by the class majorant. Hence $\sum_{i\in S}|m_i|^2\le(1+\delta)^2$. Integrating as for (4) gives total squared crossing norm at most $(1+\delta)^2 Y$ on $S$, less than $|S|X/A^2$ by a fixed margin for small $\delta$, since $|S|\ge\lfloor A^2\rfloor+1$. This proves the improved list with positive Weil margin. The same calculation applies to any shorter list with a matching-free subset of this size, using its own common modulus. In particular for $1\le A<\sqrt2$, even a pair of arbitrary bad shapes needs an exceptional product.

## Two modulated endpoints at small power radius

For the real Legendre base and fixed $1<A<2$, one can keep the list of **two** for the specific endpoint profiles throughout $|y|\le X^{1/32}$, with $\theta(A)>0$ sufficiently small. The heights may differ between twists. Any surviving pair must have exceptional product character on the units of its common modulus. This is not a claim of at most one with unrestricted sign. Use the class estimates just proved, now at the common modulus of any two or three candidates.

For any pair whose product is not the exceptional character, the cell prime-log mean of that product has magnitude $\le\delta$ by orthogonality, and $b_I\le1+\delta$. Choose signs on each cell to take the absolute values of its two real $m_i$. As in the [unmodulated pair proof](power-radius-endpoint.md), $|e_1\chi_{d_1}+e_2\chi_{d_2}|\le1+e_1e_2\chi_{d_1}\chi_{d_2}$. Hence $|m_1|+|m_2|\le1+2\delta$ there, even though the signs may change between cells. In the normalized endpoint means the cutoff can be replaced by $X$ and prime powers dropped with uniform $o(1)$ error in absolute value as in the same proof (the factors $p^{iy}$ have modulus one). The primes below $sX$ cost $O(s(1+|\log s|))$ by partial summation. On the other cells the weight $\log^+(X/v)v^{iy}$ varies by $O_s(X^{-1/32})$ uniformly, where here $\log^+(t)=\max(0,\log t)$. Thus the sum of the two real endpoint means, at their own heights, is at most

$$ (1+2\delta)X^{-1}\int_{sX}^X\log(X/v)\,dv+O(s(1+|\log s|))+o_s(1)<2/A $$

with fixed slack by choosing $\delta,s$ small. Each nonpositive endpoint needs mean $\ge1/A-o(1)$ by its [quotient formula](endpoint-arithmetic-test.md). For a list of three, their lifts are distinct on the units modulo $M$, so not all three pair products can equal the single exceptional character there. This excludes three, and taking a list of two proves the asserted necessary condition at the pair modulus. This short-cell argument uses real base values; the earlier trace bound did not.

There is also a restriction on the heights of a surviving pair. Write $b=2/A-1$ and $t_\pm=y_1\pm y_2$. By taking $\theta(A)$ smaller if needed, a nonpositive pair with exceptional zero $\beta$ must satisfy

$$ -\frac{X^{\beta-1}}2\Re\left(\frac{X^{it_+}}{(\beta+it_+)^2}+\frac{X^{it_-}}{(\beta+it_-)^2}\right)\ge b/2. \tag{5} $$

Indeed $|a+b'|\le1+ab'$ for $a,b'\in[-1,1]$. Apply this pointwise with $a=\chi_{d_1}(p)\cos(y_1\log p)$ and $b'=\chi_{d_2}(p)\cos(y_2\log p)$. Since the base is real and bounded by one, the sum of the two means is at most $1+o(1)$ plus the prime mean of $\chi_{d_1}\chi_{d_2}\cos(y_1\log p)\cos(y_2\log p)$ with weight $X^{-1}\log p\log(X/p)$. For either $|t_\pm|\le2X^{1/32}$ the cell variation of $\log^+(X/v)v^{it_\pm}$ is $o_s(1)$. The common-modulus class estimate after summing against the product character gives cell density $-h^{-1}\int_I v^{\beta-1}dv+O(\delta)$, by the exact definition of $\lambda_a$ in Theorem 1.1. Thus the normalized complex mean for $p^{it_\pm}$ equals

$$ -X^{-1}\int_0^X v^{\beta-1+it_\pm}\log(X/v)\,dv=-\frac{X^{\beta-1+it_\pm}}{(\beta+it_\pm)^2} $$

up to $O(\delta)+O(\sqrt{s}(1+|\log s|))+o_s(1)$. Here $\beta\ge1/2$ for an exceptional zero, so this bound also covers extending the integral below $sX$. Only the ordinary Chebyshev bound is needed for the error. Take the real parts, use the cosine product identity and the lower bound $2/A-o(1)$ for the sum, and choose the errors below $b/2$. In particular $\min(|t_+|,|t_-|)\le\sqrt{2/b}$; the two absolute heights cannot be far apart. This necessary condition imposes no sign on the base.

**What remains.** An exceptional product at nearly equal absolute heights is not ruled out. The low Fourier-mass floor does not control arbitrary intermediate-energy witnesses. The [hybrid moment bound](hybrid-height-weil-list.md) extends the band beyond every fixed power of $X$, but spends a growing exceptional list. A next threshold is $\log |y|\asymp(\log X)^2$ with a *bounded* list: Can one exploit the product constraint for a pair without taking a high power of a correlation strictly smaller than one?
