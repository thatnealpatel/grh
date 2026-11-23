---
evidence_revision: bbca37033019090f6f40e6223b5054d382c9d789
outcome: established
---

# Does cumulative convolution detect both fixed-strip witnesses?

Set $b=7/8$ and $\chi=\chi_4$. For each sign and each
prime $p$, let $w_\pm(p)=1\pm\tfrac12\chi(p)p^{b-1}$,
$\Lambda_{w_\pm}(p^k)=w_\pm(p)\log p$ for every $k\ge1$,
and let $\Lambda_{w_\pm}$ vanish off prime powers. For
real $x\ge1$ define

$$
R_\pm(x)=\sum_{n\le x}
\big[(\chi*(\chi\Lambda_{w_\pm}))(n)-\chi(n)\log n\big],
$$

where $*$ is Dirichlet convolution with the genuine
character kernel. Does the cumulative constraint
$\sum_{n\le x}(\chi*(\chi\Lambda_w))(n)=O(\log(2x))$
exclude each of these weights separately? Test the
quantitative proposition that both limits exist and
satisfy

$$
\lim_{x\to\infty} x^{-b}R_\pm(x)
=\pm\frac{L(b,\chi)}{2b},\qquad L(b,\chi)>0.
$$

**Source and payoff:** Bob's [(1) and signed-pair and
Gram uses](../../bob/fixed-strip-endpoints.md#the-product-mean-at-the-original-endpoint-weight)
concern the product means, with $(1,-4)$ giving $\chi_4$.
Take the two witnesses as defined in the
[prior resolution](fixed-strip-product-mean-resolution.md)
at `00c05d82fc7da829d7e5b0efe624c1a0c1af385c`.
The operator proposes the cumulative identity as new
input, not an implication claimed by Bob. Test whether
this input removes both witnesses without an operator
trace, not whether it implies an individual sharp bound.

**Discriminating test:** Subtract the genuine identity
using complete multiplicativity and the divisor sum of
$\Lambda$. In the resulting finite hyperbola sum, split
first powers from all higher powers and keep the even
prime and inclusive boundaries explicit. For first
powers, fix an outer character-sum cutoff, use the prime
number theorem and partial summation on its finite head,
and bound the remaining tail uniformly by periodicity
and monotonicity before sending the cutoff to infinity.
Check the limit normalization and the sign for each
weight. As a finite audit, compare direct divisor
convolution and the regrouped formula with exact formal
prime coefficients at integer cutoffs. Separately
identify what cancellation an inverse transfer would
still need.

**Decision.** The cumulative size constraint excludes each
weight. The plus and minus residuals have respective limits
$+4L(7/8,\chi_4)/7$ and $-4L(7/8,\chi_4)/7$ after division
by $x^{7/8}$.

**Exact residual.** Complete multiplicativity, even at zeros,
gives $(\chi*(\chi\Lambda))(n)=\chi(n)\sum_{m\mid n}\Lambda(m)
=\chi(n)\log n$. Put $S(t)=\sum_{d\le t}\chi(d)$; it is one
when $\lfloor t\rfloor$ is 1 or 2 modulo 4, and zero otherwise.
Partial summation gives $G(x)=\sum_{n\le x}\chi(n)\log n
=S(x)\log x-\int_1^x S(t)\,dt/t=O(\log(2x))$. Subtracting
the genuine identity leaves only the perturbation to the inner
coefficient. Summing the kernel over $d p^k\le x$ gives

$$
R_\pm(x)=\pm\tfrac12\sum_{p^k\le x,\ p\text{ odd},\ k\ge1}
 p^{b-1}\log p\,\chi(p)^{k+1}S(x/p^k).
$$

At 2 the perturbation is zero. At odd primes the character
factor is one for odd $k$ and $\chi(p)$ for even $k$. The
inequality is inclusive, with no half term at an integer.

**Limit.** Write $H(y)=\sum_{p\le y,\ p\text{ odd}}p^{b-1}\log p$.
The ordinary prime number theorem and partial summation give
$H(y)\sim y^b/b$ and $H(y)\ll_b y^b$ for $y\ge1$. Since
$|S|\le1$, all $k\ge2$ together cost at most a constant times
$\sum_{2\le k\le\log_2 x}H(x^{1/k})\ll_b x^{b/2}\log(2x)$.
Before the signed prefactor, the $k=1$ term is the finite sum
$\sum_{d\le x}\chi(d)H(x/d)$. Its first $D$ terms divided by
$x^b$ tend to $b^{-1}\sum_{d\le D}\chi(d)d^{-b}$ for fixed
integer $D$. For $u>D$ we have $|S(u)-S(D)|\le1$. Summation
by parts against the nonincreasing nonnegative $H(x/d)$ thus
bounds the absolute tail by $H(x/(D+1))$ (zero for an empty
tail). After normalization this is $O_b((D+1)^{-b})$ uniformly
in $x$. Now send $D\to\infty$. The limiting series is
$L(b,\chi)=1-3^{-b}+5^{-b}-\cdots\ge1-3^{-b}>0$.
This proves the stated limits. Adding back $G(x)=o(x^b)$
preserves both, so neither cumulative convolution is
$O(\log(2x))$.

**Boundary check.** At each $x=n,n+1/2$ for $1\le n\le513$,
a scratch calculation enumerated prime-power divisors $m=p^k$,
using $\chi(n/m)\chi(m)$, and subtracted $\chi(n)\log n$ by
factoring $n$. Prefix coefficients of $\log p$ and
$p^{b-1}\log p/2$ matched the displayed residual with the
floor in $S$, for both signs and the genuine coefficients.
At $x=9$ the plus perturbation vector at $(3,5,7)$ is
$(-1,1,1)$. This checks the finite formula, not the limit.

**Scope.** Bob's (1) and its signed-pair and Gram uses do not
assume this constraint. The prior witnesses satisfy the same
absolute inequalities, not necessarily equal means. Excluding
both needs no operator trace but yields no square-root estimate:
The convolution inverse of $\chi$ is $\mu\chi$, so the genuine
signed prime-power sum equals $\sum_{d\le x}\mu(d)\chi(d)G(x/d)$.
Taking absolute values using the size constraint gives only
$O(\sum_{d\le x}\log(2x/d))=O(x)$. Cancellation in this
weighted inverse sum, or a different comparably strong input,
is still needed; forward periodicity does not supply it.
Neither this test nor the exact identity proves GRH or gives a
new zero-free region.
