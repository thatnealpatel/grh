---
evidence_revision: f5fbeb09e9b972565848e25ac295f3341a537afd
---

# Prescribe logarithmic order at the fixed baseline

**Proposition to test:** There is an absolute $C\ge1$
such that for every integer $q\ge2$, set
$m=\max(8,\lceil C\log(2q)\rceil)$. Joint GRH for the
primitive functions inducing all characters modulo $q$,
including zeta, is equivalent to eventual nondecrease
of $W_{q,m}(X)/X$ for every real $X$ on a full tail.
Use exactly the window at the evidence pin: $M=10^{15}$,
$a=\log 2$, $h_m=\mathbf1_{[0,a]}^{*m}$,
$k_m=4h_m^{(4)}-5h_m''+h_m$, and

$$W_{q,m}(X)=\sum_{p\nmid q}(\log p)
  [Mh_m(\log(p/X))+\mathbf1_{p\equiv1\bmod q}k_m(\log(p/X))].$$

On joint GRH seek eventual strict derivative positivity.
The beginning of the tail may depend on $q$ and $m$.

**Source and payoff:** The operator proposes strengthening
[the fixed-baseline criterion](../closed/fixed-baseline-variable-order-prime-density.md)
at the evidence pin, whose fixed-$q$ dominated convergence
provides no order in $q$. A bound uniform in $q$ for the
normalized zero budget would prescribe a single order
without changing the window, proving GRH, or promising a
uniform onset. The inputs are the quartic derivative
margin at `a08d9dfe9adc87383319f9e970b60bd443cfcca2`,
the contour argument at
`76d66112fa30b3a9cc28d24759ac6f8fe78f9e94`, and the
converse inputs in the fixed-baseline card, including
`d5301e8af8a5b4a76db76248f3264d9c9b5a394c`.

**Discriminating test:** Put $L=\log(2q)$. Under joint
GRH, derive or refute an absolute $O(\sqrt L)$ family
average of $\sum_\gamma \exp(-bL\gamma^2)$ for some
fixed absolute $b>0$. Check the explicit-formula signs,
conductor, gamma integral, and single zeta pole pair.
Test orthogonality of the primitive inducing values at
all $p^j$, including $p^e\Vert q$, where ordinary
orthogonality modulo $q$ does not apply directly. Then
combine the Gaussian with the central zero of $(s-1)Q(s)$,
quadratic decay of the normalized box transform near zero,
and an absolute per-unit zero count for its remote tail.
Test whether the resulting bound gives $D_{q,m}<M/400$
simultaneously for the prescribed orders. Check that the
pinned forward remainders need only be fixed-$q,m$ and
that its converse applies to this same prescribed order.
