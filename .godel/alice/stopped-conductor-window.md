# Stop the prime moment at a product, not a degree

The each-prime [masked Weil-window theorem](masked-conductor-window.md) holds with $c=53/50$ in place of $183/200$. For every fixed $0\le a<c$, let $L=\log q$, $B=\log L$, $A=2+a/B$, and $b=\log(AL)$. With the conductor and Gamma normalization in the [original theorem](prime-conductor-window.md), outside a single fraction $O(\exp(-\delta L/B))$ of the primitive characters at each sufficiently large prime $q$,

$$Q_\chi(f)\ge(c-a-o(1))(L/B)\|f\|_2^2 \qquad(f\in C_c^\infty(-b,b;\mathbb C)).$$

The corresponding relative floor holds simultaneously on all finite right-hand Pick blocks at distinct real nodes $m\ge B^3$, $\sum_m1/m\le b$, relative to $C_{mn}=1/(m+n)$. This is a paper theorem. It enlarges a second-order term, not the limiting fixed constant $A=2$.

## A length-stopped moment

Use $Y=q\exp(cL/B)$, $D=2b+B^{-5/4}+2q^{-\alpha/2}$, $X=e^D$, and $E=\sqrt X$ as in the masked theorem, with $0<\alpha<1$ fixed. Let $w\ge0$ be fixed, nonzero in $L^2$, supported on $[0,R]$, bounded, and of bounded variation. Put $I=\int_0^R e^{-r/2}w(r)^2\,dr$, $b_p=(\log p)w(D-\log p)/\sqrt p$ (zero outside the slice), and $S_\chi(t)=\sum b_p\chi(p)p^{it}$. For every fixed

$$v>e^{c/4-1/2}\sqrt I,$$

we have $\sup_{|t|\le4Y}|S_\chi(t)|\le vE$ outside a fraction $\exp(-\Omega(L/B))$ at this prime. In the fixed-degree moment the corresponding factor was $(I_0 I_1)^{1/4}$, with $I_j=\int e^{-jr}w^2$. Cauchy-Schwarz gives $\sqrt I\le (I_0 I_1)^{1/4}$. The reason we can now use the intermediate weight is that **all terms** in the detecting polynomial have product comparable, up to a factor $X$, to the hybrid mean-value length.

To prove this, put $U=qY$. Start with the empty ordered prime tuple and append primes with $b_p>0$, stopping each branch the first time its product reaches $U$. Every leaf has product $U\le n<UX$ and length $k$ between $\log U/D$ and $1+\log U/(D-R)$. Throughout these degrees $k=(1+o(1))L/B$ and $kD=(2+o(1))L$. Let $P_{k,\chi}(t)=\sum_n d_{k,n}\chi(n)n^{it}$ sum the leaf monomials of length $k$, each ordered leaf weighted by the product of its $b_p$. The coefficients and stopping rule are independent of both $t$ and $\chi$. Whenever $z=S_\chi(t)\ne0$,

$$1=\sum_k z^{-k}P_{k,\chi}(t).$$

Indeed at each internal node replace its monomial by that monomial times $\sum_p b_p\chi(p)p^{it}/z=1$, starting from $1$ and including one factor $z^{-1}$ at each descent. The tree is finite; no positivity at a peak is needed. If $|z|\ge v_0 E$ with $e^{c/4-1/2}\sqrt I<v_0<v$, at least one $|P_{k,\chi}(t)|/(v_0 E)^k$ is at least $1/K_0$, where $K_0=O(L)$ counts the possible degrees.

The single-prime hybrid mean-value estimate in the [each-prime proof](prime-conductor-window.md#cancellation-below-a-frequency-cutoff), applied to each stopped polynomial on $[-5Y,5Y]$, costs $O(Y+UX\log(2UX)/q)=Y L^{O(1)}$ times its squared coefficient norm. It uses character orthogonality and the reciprocal-gap sum, with no sparsity hypothesis. Coefficients are nonnegative and bounded by their counterparts in the full $k$th power. In each square use $1\le(n/U)^{1/2}$ on the stopped support. Unique factorization and the multinomial bound give

$$\sum_n d_{k,n}^2\le U^{-1/2} k! \left(\sum_p \sqrt p\,b_p^2\right)^k,\qquad \sum_p \sqrt p\, b_p^2=(1+o(1)) ED I.$$

The last estimate is PNT by partial summation on the fixed log slice: One $\log p$ is $D+O(1)$, and $dp/\sqrt p= -E e^{-r/2}dr$ after reversing endpoints. Multiplying the mean-value bound by $(v_0 E)^{-2k}$ and using Stirling gives, uniformly in the allowed $k$, an upper bound with logarithm at most

$$\log(Y/\sqrt U)+k\log\!\left(\frac{kD I}{e v_0^2 E}\right)+o(k)=\left[\frac c2+\log\!\left(\frac{I}{e v_0^2}\right)+o(1)\right]\frac{L}{B}.$$

Here $E=(2+o(1))L$ and $\log(Y/\sqrt U)=cL/(2B)$. The bracket is negative. The derivative $|S'_\chi|\ll ED$ gives an interval of length $\gg 1/D$ above $v_0 E$ around any peak above $v E$, within $[-5Y,5Y]$. Integrating the union bound over this interval costs only powers of $L$: Use $K_0^2\sum_k |P_{k,\chi}|^2/(v_0 E)^{2k}$ to majorize the indicator of $|S_\chi|\ge v_0 E$ on the whole time interval. Thus we do not need a persistence estimate for a *stopped* polynomial or a degree that witnesses the entire interval. Averaging includes the principal character; removing it does not change the exceptional-fraction estimate.

## A profile and an exact margin

Keep $K=\int_0^\infty e^{-x}m(x)^2\,dx$ and $M=\iint e^{-x-z}m(x)m(z)w(x+z)\,dx\,dz$ from the masked Schur proof. Its sufficient criterion is now $e^{c/4-1/2}\sqrt I<M/K$: Choose the slice supremum strictly between them, allowing a further $o(E)$ for the prime powers. For fixed $m$, the numerator $M$ is a linear functional of $w$ with measure $e^{-r/2}dr$. This suggests matching $w(r)$ to $e^{-r/2}(m*m)(r)$, rather than optimizing two independent polynomials.

Put $p(x)=1+3x/2+2x^2$ and $m(x)=e^{-x}p(x)$ through $x=32$, smoothly tapered to zero on $[32,33]$ without increasing it over the untapered profile. Use a smooth compact extension at the left end as in the masked proof. Define $h(r)=\int_0^r p(x)p(r-x)\,dx=r+3r^2/2+41r^3/24+r^4/2+2r^5/15$. Set $w(r)=e^{-3r/2}h(r)$ on $[0,32]$ and zero elsewhere. Then $M=I=\int_0^{32}e^{-7r/2}h(r)^2\,dr$ exactly, since $x+z\le32$ is untapered. The untruncated integrals, using $\int_0^\infty r^j e^{-ur}\,dr=j!/u^{j+1}$, are

$$\bar K=319/162,\qquad \bar I=684915632/282475249.$$

We have $K\le\bar K$ and $I>(1-10^{-7})\bar I$. Indeed $h(r)\le r^5$ for $r\ge32$ by dividing by $r^5$; the lost tail is at most $32^{10}e^{-112}/(7/2-10/32)$ by $\log(r/32)\le (r-32)/32$. For an exact margin at $c=53/50$ one can multiply the rationals

$$ (1-10^{-7})\frac{\bar I}{\bar K^2}\sum_{j=0}^5\frac{(47/100)^j}{j!}=\frac{1797467863021507653445236972357}{1796560238343062500000000000000}>1.$$

Since $1-c/2=47/100$, this gives $I/K^2>e^{c/2-1}$ as required. No numerically optimized eigenvalue is used.

Only the forward slice estimate changes in the [masked proof](masked-conductor-window.md#schur-estimate-including-the-diagonal). The positive margin $M-vK$ allows a fixed small edge deletion, charging the signed cost to the two mask norms. The corrected Schur weight bounds the middle-band cost by $(1-\gamma)E$ per squared norm, up to $o(L/B)$ per original unit input. Choose $\alpha<1$ with $1+\alpha>2(1-\gamma)$. The low-band full-multiplier estimate has a further exceptional fraction $q^{-(1-\alpha)/2+o(1)}$. Above $Y$, $L+\log Y-O(1)-(1+o(1/B))E=(c-a-o(1))L/B$. Leakage, omitted shifts for blocks, and recombination are unchanged since $D$, the input class, and the bounded fixed masks obey the same hypotheses. Neither the degree witness nor the exceptional set is selected from the test or the nodes.

At a fixed height $Y=q^t$, $t>1$, the stopped moment still pays $Y/\sqrt{qY}=q^{(t-1)/2}$. For fixed slice and fixed level in units of $E\asymp L$, the factorial and profile factor changes its logarithm only by $O(L/B)$. Thus this upper-bound calculation does not solve the [fixed-window pair problem](fixed-window-height.md).
