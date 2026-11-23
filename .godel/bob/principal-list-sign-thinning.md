# Thin the high endpoint lists by the actual quadratic signs

For $Q\le q\le Q+J\le 2Q$, take odd squarefree $q$, $\xi_q=(\cdot/q)$, and $y(q)=q^{3/5}$. Fix $B>0$ and allow fundamental discriminants $|d|\le(\log Q)^B$ coprime to $q$. Write $b_p(x)=x^{-1}\log p\,(\log(x/p))_+$ and $X_0(q)=((9/5)\log q)^2$. The statistic to retain is

$$ R(q,d)=\sum_p b_p(X_0(q))\xi_q(p)\chi_d(p)\cos(y(q)\log p). $$

Using a twist's own cutoff $((9/5)\log(q|d|))^2$ gives the same bounds below. A nonpositive own-cutoff quotient at the named height requires $R(q,d)\ge 8/9-o(1)$ by the [endpoint identity with Gamma](fixed-strip-endpoints.md#signed-pairs-versus-the-gram-bound). It also lies in the [eight signed principal lists](high-endpoint-harmonics.md#actual-principal-peak-threshold), taken at a fixed positive threshold just below $0.58712243824$. The following count concerns the **actual signed statistic** on the lists, not only the number of floor exceptions.

**Count.** For any fixed $\tau>0$, a single returned cell of the [principal block search](principal-block-search.md) contains at most $H^{49/74+o(1)}$ admissible $q$ with $R(q,d)\ge\tau$ for some allowed $d$, where $H\asymp Q^{2/5}/(\operatorname{bitlength} Q)^2$ is the cell length in the conductor variable before clipping. In the list's regime $Q^{2/5+\delta}\le J\le Q$ with fixed $\delta>0$, the union of any fixed finite collection of these harmonic lists has at most

$$ \ll_{\varepsilon,\delta,B,\tau} Q^\varepsilon\min\{J^{1/2}Q^{12/185},\ Q^{1/2}\} \tag{1} $$

such bases, for every $\varepsilon>0$ (constants may also depend on the fixed list parameters). This improves the **bounds** from integer population and ambient counting by a power throughout $J\le Q^{161/185-\rho}$ with any fixed $\rho>0$, subject to the list's lower length restriction. It is not a claim about the actual number of entries in a particular list.

## 1. Freeze in one cell

The cell for harmonic $j$ and left endpoint $v_0$ has $2j y(q)\in[v_0,v_0+1/g]$, $g=(\operatorname{bitlength}Q)^2$. Its inverse, clipped to the target block, is an interval of length $\le H=C Q^{2/5}/g$ for a fixed sufficiently large $C$, by the derivative of $2j q^{3/5}$. Put $t=v_0/(2j)$ and $V=X_0(Q)$, $D=\log V$. The moving weights cost $O_B(\log\log Q/\log Q)$ in $\ell^1$ even at the own cutoff: The sum of their absolute derivatives in $r=\log x$ is bounded a.e. by $e^{-r}\vartheta(e^r)+\sum_p b_p(e^r)=O(1)$, and the weights are continuous at entry. At the frozen cutoff the maximum effect of the phase change is $O(D/g)$, since $\sum_p b_p(V)=O(1)$ and $|y(q)-t|\le 1/(2jg)$. Neither estimate depends on the center, on $q$ in the cell, or on the character values.

Discard primes $p\le D$ at cost $O(D\vartheta(D)/V)=o(1)$ and write $w_p=b_p(V)\mathbf 1_{p>D}$. This also keeps the local trace functions below away from small characteristic. For sufficiently large $Q$ a hit implies

$$ T_q=\sum_p a_p(p/q)\ge\tau/2,\qquad a_p=w_p\chi_d(p)\cos(t\log p),\qquad |a_p|\le w_p. $$

In fact the local moment bound below is uniform for **arbitrary real** $|a_p|\le w_p$ fixed throughout the interval. The proof works whenever $H$ is between fixed positive powers of $Q$, and for an interval of length at most $H$ inside the positive integers. Short clipped intervals may instead be charged their actual integer population.

## 2. Local moments: smoothness is in the prime-product kernel, not in $q$

Enlarge the nonnegative moment $\sum_q |T_q|^{2k}$ to all odd integers in the interval, extending $(p/q)$ by the Jacobi symbol. Set $Y=V^k$ and $\sigma^2=\sum_p w_p^2\ll D^2/V$, using $\max w_p\le D^2/V$ and the bounded weight mass. The square-product part of the expansion, in absolute value, is at most

$$ (H+1)(2k\sigma^2)^k. \tag{2} $$

Indeed its coefficient majorant is the $2k$th moment of $\sum_p w_p\epsilon_p$ for independent uniform signs $\epsilon_p$. The coefficientwise bound $\prod_p\cosh(w_p z)\preceq\exp(\sigma^2 z^2/2)$ gives $(2k\sigma^2)^k$. This prices all repeated primes, not just equal ordered tuples.

For a nonsquare product, let $m>1$ be its squarefree kernel (primes of odd multiplicity) and $s$ the product of the primes of positive even multiplicity. They are odd and coprime. On a class $q\equiv r\bmod 4$ the product of the Jacobi symbols is a fixed sign times $(q/m)\mathbf 1_{(q,s)=1}$, by quadratic reciprocity including the zeros. Expand the indicator as $\sum_{h\mid s,\ h\mid q}\mu(h)$. For each $h$, the congruences give $q=A+4hu$ with $u$ in a translated integer interval of at most $H+1$ points. Since $4h$ is invertible modulo $m$, the summand $(q/m)$ becomes a constant of modulus one times $( (u+c)/m)$ for an integer $c$. Thus each sum is of a primitive nonprincipal character modulo $m$ over an arbitrary **translated interval**, with no residual additive phase. The two residue classes and the $\le 2^{2k}$ erasure terms cost $H^{o(1)}$ for the orders used here. The squarefree and twist-coprimality restrictions were dropped on a positive moment, not after taking the signed expansion.

Use $k=\lfloor (25/37)\log H/D\rfloor$, so $m\le Y^2\le H^{50/37}$. For $m\le 2(H+1)$, Pólya–Vinogradov gives $O(\sqrt H\log(2H))$ for each interval, removing complete periods if necessary. For the remaining $m$ the following bound holds uniformly in the translated interval of at most $H+1$ points:

$$ \left|\sum_u ((u+c)/m)\right|\ll_\epsilon H^\epsilon m^{11/30}H^{1/6}. \tag{3} $$

To check (3) use Wu–Xi with Sawin's appendix, [*Arithmetic exponent pairs for algebraic trace functions and applications*, Theorem 8.3, BA$^J$B-estimate](https://arxiv.org/pdf/1603.07060v5#page=33) (Algebra Number Theory 15 (2021), 2123–2172). The [addendum](https://arxiv.org/abs/2104.14508) supplies a proof of (9.14) in the Brun–Titchmarsh application, not a replacement for this short-sum estimate. Here the deformation modulus is $1$, the interval length is $<m$, and we use $J=4$ **in that theorem**. The normalized Fourier transform of each local Legendre symbol is, by the Gauss sum identity, a unit scalar times that symbol (CRT dilation only changes the scalar). The Kummer sheaf has bounded conductor and is geometrically irreducible and pure of weight zero. It is ramified at $0$, so it cannot be an Artin–Schreier sheaf of a polynomial; this verifies composite $4$-amiability of the Fourier transform under Definition 2.4. The theorem, with length bounded above by $U=H+1$ and $m=m_1m_2m_3m_4$, gives the majorant

$$ m^{1/2+\epsilon}\left((Um_4/m)^{1/2}+(Um_3/m)^{1/4}+(Um_2/m)^{1/8}+(U^2m_1/m^2)^{1/16}\right). $$

All terms increase in $U$ and there is no complete-period term here. For $m_1,m_2,m_3,m_4$ target, respectively,

$$ m^{-2/15}U^{2/3},\qquad m^{-1/15}U^{1/3},\qquad m^{7/15}U^{-1/3},\qquad m^{11/15}U^{-2/3}. $$

Their product is $m$, and each is $\ge U^{1/15}$ when $U<m\le H^{50/37}$. All primes of $m$ are $\le V$, so greedily filling the first three targets to within a factor $V$ (stop just below each target), then taking the remainder, gives pairwise coprime factors within $V^{O(1)}$ of their targets. In detail, the unused product before each fill is at least the product of the remaining targets, so a next prime is available until the target is reached or would be exceeded. The four terms at the targets each equal $m^{-2/15}U^{1/6}$. Since $V=H^{o(1)}$, this proves (3) with any fixed $H^\epsilon$ slack after tuning the theorem's epsilon. This argument checks the length and factorization directly rather than assuming a general exponent pair applies on every shortened interval after erasure.

The total absolute coefficient mass of the off-diagonal is at most $(\sum w_p)^{2k}=H^{o(1)}$. The diagonal (2) is $H Y^{-1/2+o(1)}$ as an upper bound: $\log k=D/2+O(\log D)$ uniformly in the polynomial-length regime, so $\log(2k\sigma^2)\le-D/2+O(\log D)$. The off-diagonal is $\ll_\epsilon H^{1/6+\epsilon} Y^{11/15}$, with the small-$m$ contribution absorbed for this order. Both bounds have exponent $49/74$, since

$$ 1-\tfrac12\tfrac{25}{37}=\tfrac16+\tfrac{11}{15}\tfrac{25}{37}=\tfrac{49}{74}. $$

Rounding $k$ and dividing by $(\tau/2)^{2k}$ cost only subpowers. Here $H^{e+o(1)}$ for an upper bound means $\ll_\epsilon H^{e+\epsilon}$ for each fixed $\epsilon>0$, uniformly in the intervals and coefficients. The union over allowed $d$ is also a subpower. No random model for the signs or for the choice of cells enters.

**Elementary fallback.** Using only Pólya–Vinogradov up to $m\le Y^2$ gives $H Y^{-1/2+o(1)}+Y H^{o(1)}$ and exponent $2/3$ at $Y=H^{2/3+o(1)}$. More generally a uniform per-term estimate $H^\alpha m^{\beta+o(1)}$ with $\alpha<1$ and $\beta\ge0$ gives the balance $(\alpha+4\beta)/(1+4\beta)$ in this argument, provided it applies to the resulting order. The [classical cubefree Burgess bound](https://arxiv.org/abs/2511.17778) has $\alpha=1-1/r$, $\beta=(r+1)/(4r^2)$: $r=2$ gives $5/7$, and $r\ge3$ does not beat $2/3$ (already $\alpha\ge2/3$). The gain in (3) uses the special smooth squarefree moduli in the expanded moment.

**Why a direct sieve is not the cell estimate.** The fixed-time quadratic large sieve (Corollary 2 below), even after dropping all bases outside a cell, has size parameter $Q$, not $H$. With the same diagonal majorant, optimizing $(Q+Y)Y^{-1/2}$ gives $Q^{1/2}$, larger than the cell population bound. The all-primitive [Gallagher hybrid sieve, as stated in Young, Theorem 2.3](https://arxiv.org/abs/2205.07754), has cost $Q^2 T+Y$ for a time interval of length $T\ge1$ (translate by changing the coefficients), not $HT+Y$. A fixed-threshold peak persists on length $\gg_\tau1/D$ by the derivative bound. Using the squared coefficient norm, bounded by the same square-pair majorant, this route gives a balance of order $Q\sqrt T$ up to subpowers for polynomial $T$; even taking $T=1$ for a cell does not help. These are limits of these substitutions, not lower bounds on possible hybrid estimates.

## 3. The ambient count also applies to raw hits

The [ambient floor theorem](local-quadratic-twists.md) counts actual floor exceptions; membership in the raw sign-hit set does not imply such an exception. For comparison (1), adapt its product argument to prove the ambient $O_\varepsilon(Q^{1/2+\varepsilon})$ bound on raw hits directly. Fix $d$, freeze only the cutoff uniformly as in Section 1, and normalize $w_p$ to total mass one, say $\omega_p=w_p/\sum w_p$. The mass was $1+o(1)$ by the prime number theorem and partial summation. For each raw hit choose $z_q$ of modulus one so that $z_q\sum_p\omega_p\xi_q(p)\chi_d(p)p^{iy(q)}\ge\eta$ is real, for a fixed $\eta>0$ depending on $\tau$. For $L$ hits and even fixed $b$, Hölder over the prime probability $\omega$ gives

$$ (L\eta)^b\le \mathbb E_\omega\left|\sum_q z_q\xi_q(p)p^{iy(q)}\right|^b. $$

Expand with $b/2$ conjugates. At least $(L\eta)^b/2$ ordered tuples have a product-character prime sum of modulus $\ge\eta^b/2$ at some $|t|\le b(2Q)^{3/5}$: all other normalized terms contribute at most $L^b\eta^b/2$, and every term has modulus $\le1$. If $n=\prod_i q_i=s h^2$ with squarefree $s$, the product character agrees with $(\cdot/s)$ away from primes dividing $n$. Replacing it costs $O(D\log n/V)=o(1)$ for fixed $b$. The primitive character modulo $s$ then has a prime sum of fixed positive modulus; cover times by a mesh of pitch $c_{\eta,b}/D$ using the derivative bound $D$. There are $Q^{3/5+o(1)}$ mesh points.

For $K\le s<2K$ and one mesh time, [Heath-Brown's quadratic large sieve, Corollary 2, p. 238](https://matwbn.icm.edu.pl/ksiazki/aa/aa72/aa7234.pdf#page=4) applied to the $k$th power of the normalized sum, $k=\lfloor\log(2K)/D\rfloor$, costs $(2K V^k)^\nu(2K+V^k)$ times the square-product coefficient sum. The polynomial length is $V^k\le2K$, and the complex coefficients have the same square-product majorant as in (2), without the interval factor and with $w_p$ replaced by $\omega_p$. Dividing by the fixed threshold to the power $2k$ gives at most $Q^{o(1)} K^{1/2+2\nu}$ characters: $\log k\le D/2+O_b(\log D)$, $kD=\log(2K)+O(D)$ and $k\ll_b\log Q/D$. For $k=0$ the same bound follows from $K<V$ and the trivial count; $s=1$ can be counted separately. This is a fixed-time sieve on the **reduced** conductors, not a translated or hybrid quadratic sieve.

For each $s\in[K,2K)$ there are at most $Q^{b/2+o(1)}/\sqrt K$ tuples: Choose $h\le (2Q)^{b/2}/\sqrt s$, then bound the number of ordered factorizations of $n$ by $\tau_b(n)=Q^{o(1)}$ for fixed $b$. Thus the $K^{1/2}$ sieve cost cancels against the multiplicity bound. Summing the dyadic bands through $(2Q)^b$ and the mesh points proves $L^b\ll_{\eta,b,\nu} Q^{b/2+3/5+2b\nu+o(1)}$. Choose $b$ fixed and large, then $\nu$ small in terms of $\varepsilon$, and take the polylogarithmic union over $d$. This is the ambient term of (1) for the very same observable as the local term.

## 4. Charge the whole list

The contract gives $N^{1/2+o(1)}$ cells for $N\asymp JQ^{-2/5}$. Multiply their number (not their integer population) by the cell bound and take a finite harmonic union. One can charge the actual integer population instead for any smaller clipped cell and can count overlaps only once. The resulting upper bound is $N^{1/2+o(1)}H^{49/74+o(1)}\le J^{1/2}Q^{12/185+o(1)}$, versus $N^{1/2+o(1)}(1+H)=J^{1/2}Q^{1/5+o(1)}$ for the trivial list bound. The saving over the latter is $Q^{5/37-o(1)}$ in the upper bounds. The ambient comparison crosses at $J=Q^{161/185}$, with strict power improvement below this exponent by a fixed margin. For example $J\asymp Q^{1/2}$ gives $Q^{233/740+o(1)}$ versus the list population bound $Q^{9/20+o(1)}$. The elementary fallback gives $J^{1/2}Q^{1/15+o(1)}$ and crossover $J=Q^{13/15}$. On dyadic-size blocks neither local sum improves the ambient exponent. Below the list's polynomial-height regime there is no claim on the number of cells; the local estimate still holds in any single cell with polynomial conductor-length envelope.

These are population bounds, not a certified algorithm listing the signed survivors in that time, a proof that a list is empty, or a count for all endpoint heights. There is no optimality claim for the chosen smooth-modulus estimate. To extend the gain to longer blocks, a next test is whether one can sum the nonsquare-kernel contributions over the *selected* cells with cancellation despite their different frozen coefficients, rather than multiplying a worst-case local count by the cell budget.
