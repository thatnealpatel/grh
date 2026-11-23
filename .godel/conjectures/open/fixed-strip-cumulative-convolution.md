---
evidence_revision: bbca37033019090f6f40e6223b5054d382c9d789
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
[prior resolution](../closed/fixed-strip-product-mean-resolution.md)
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
