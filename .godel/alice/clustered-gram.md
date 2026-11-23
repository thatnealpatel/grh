# The signed short-block Gram on a union of unit intervals

In the [point-sampled detector](dense-detector-cost.md), let $q$ be prime, $N=q^{1.99+o(1)}$, $T=q^{1.11}$, and let $w$ be the fixed smooth nonnegative cutoff supported in $(7/8,17/8)$ and equal to one on $[1,2]$. Pick one $|t_i|\le T$ per distinct character $\chi_i\bmod q$. If the times can be covered by $K$ intervals of length one, anywhere in the band, then the **signed** Gram satisfies

$$ G_{ij}=\sum_n w(n/N)\chi_i(n)\overline{\chi_j(n)}n^{i(t_i-t_j)},\qquad \|G\|_{\rm op}\ll_w N+Kq\sqrt T. $$

In particular, $K\le q^{.440-\eta}$ with fixed $0<\eta<.440$ suffices for $\|G\|_{\rm op}\ll q^{1.995-\delta}$ for any $0<\delta<\min(.005,\eta)$. This includes the [two-class obstruction to unsigned bounds](unsigned-gram-cycles.md), but does not assume a bound on any absolute row sum.

**Exact centers.** First give all rows of a group the same time, with at most $K$ groups of disjoint characters. Within a group the time cancels. For a row coefficient vector $v$, group the integers by residue and use character orthogonality: The quadratic form is bounded by $(q-1)\max_{a\ne0}\sum_{n\equiv a\ (q)}w(n/N)\,\|v\|_2^2\ll_w N\|v\|_2^2$.

Across groups let $u$ be the common time difference. With $e(z)=\exp(2\pi iz)$, Poisson summation in residue classes gives the cross block as the restriction to its row and column groups of

$$ \frac{1}{q}\sum_{h\in\mathbb Z} F\,\mathrm{diag}_{a}\big(e(ha/q)\big)F^* I_h(u),\quad F_{\chi,a}=\chi(a)\ (a\in(\mathbb Z/q)^\times),\quad I_h(u)=\int w(x/N)x^{iu}e(-hx/q)\,dx. $$

The $h=0$ block vanishes by disjointness. Each **whole matrix** multiplying $I_h(u)$, including $1/q$, has operator norm at most one since $FF^*=(q-1)I$. This is where the signs of the Gauss sums matter.

Write $V=N/q$. In $z=x/N$ the phase, up to a constant, is $u\log z-2\pi hVz$. If $|u|\le V$, all $h\ne0$ have derivative of magnitude $\gg |h|V$ on the support. If $|u|>V$, the same is true for $|h|>2|u|/V$. In either nonstationary range the higher phase derivatives are $O_j(|h|V)$ there, so repeated integration by parts costs $O_{w,b}(N(|h|V)^{-b})$ per such $h$. Their sum is negligible for $b$ sufficiently large. In the remaining range there are $O(|u|/V)$ nonzero $h$, each with $|I_h(u)|\ll_w N/\sqrt{|u|}$ by the second derivative estimate ($|u|/z^2\asymp |u|$). Thus the cross-block norm is $O_w(q\sqrt T)$ uniformly for $|u|\le 2T+2$. Applying Cauchy-Schwarz to the sum of the group vector norms bounds the exact-center Gram by $O_w(N+Kq\sqrt T)$.

**Do not round an entry's phase with a pointwise error.** Assign each time to one of its covering intervals and write it as $s_i+\tau_i$ with $s_i$ the center and $|\tau_i|\le1$. Let $A(s)_{in}=\sqrt{w(n/N)}\chi_i(n)n^{is_i}$ on the supported integers, and $L=\sup_{w(n/N)\ne0}|\log(n/N)|=O(1)$. Up to a diagonal unitary with entries $N^{i\tau_i}$, $A(t)$ equals

$$ \sum_{k\ge0}\mathrm{diag}_i\big((i\tau_i)^k\big)\, A(s)\,\mathrm{diag}_n\big(\log^k(n/N)\big)/k!. $$

The operator series converges absolutely with norm at most $e^L\|A(s)\|_{\rm op}$. Squaring gives the asserted bound for $G=A(t)A(t)^*$.

**What this removes.** On one dyadic block the pinned detector has squared coefficient norm $\le q^{-.995+o(1)}$ and each assigned peak costs at least $q^{-o(1)}$ in squared value. By duality the number of such characters with chosen times in any one union as above is $\ll q^{1-\delta+o(1)}$; the cutoff is one on the coefficient block. Summing over $O(\log q)$ blocks does not lose a fixed power. There is no count of the number of possible unions here: The bound is uniform in the chosen list. To treat unrestricted lists it remains to control peaks spread over more intervals, or prove a signed bound that exploits cancellation across the different center pairs. A common $I_h(u)$ on a cross block is not a common multiplier on the whole arbitrary-time matrix. This result does not bound all peaks or the rectangle count.
