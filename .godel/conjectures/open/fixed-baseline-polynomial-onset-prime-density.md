---
evidence_revision: 6a7a69610f307bbc5427e262d04cebe3c69a408b
---

# Prescribe a polynomial onset at the fixed baseline

**Proposition to test:** There are absolute $C,D\ge1$
such that, for every integer $q\ge2$, joint GRH for the
primitive inducers modulo $q$, including zeta, is
equivalent to nondecrease of $W_{q,m}(X)/X$ on the
entire real interval $[(2q)^D,\infty)$, where
$m=\max(8,\lceil C\log(2q)\rceil)$. Under joint GRH its
derivative is strictly positive at every point of that
interval. Use the same fixed $M=10^{15}$ and the same
windows: $a=\log 2$, $h_m=\mathbf1_{[0,a]}^{*m}$,
$k_m=4h_m^{(4)}-5h_m''+h_m$, and
$$W_{q,m}(X)=\sum_{p\nmid q}(\log p)
 [Mh_m(\log(p/X))+\mathbf1_{p\equiv1\bmod q}k_m(\log(p/X))].$$
No numerical $C,D$ or unconditional finite certification
of monotonicity is sought.

**Source and payoff:** This is an operator strengthening
of the logarithmic-order landing at the evidence pin:
that landing bounds the critical-zero budget uniformly
but only claims a fixed-modulus tail. The exact kernel
and converse are at
`f5fbeb09e9b972565848e25ac295f3341a537afd`; the quartic
all-prime margin is at
`a08d9dfe9adc87383319f9e970b60bd443cfcca2`.
A uniform remainder would prescribe the onset without
changing the weights or assuming GRH for other moduli.

**Discriminating test:** In $X^2$ derivative units test
whether the perturbation error after the critical zeros
is $O(A^m X^{3/8}\operatorname{polylog}(2qX))$ with
absolute constants. Bound the full imprimitive log
derivative on $\Re s=1/4$ by a primitive Hadamard
difference using absolute local zero counts. For signed
squares test the full $\chi^2$ prime-power sums at scale
$\sqrt X$ with transform $G_m(s/2)/2$ and shift only to
$\Re s=3/4$. Check the principal pole cancellation,
normalized orthogonality, and crude subtraction of
higher powers using convolution from order eight. Then
test absorption after division by $\Phi(1/2)^m\sqrt X$
for every $X\ge(2q)^D$, rational-prime exclusions, and
derivative regularity at all knots. Check the converse
on the same interval and with the same prescribed order.
