# Assemble one cubic modulus from both axis fibers

Use the actual filters and smooth cubics of the
[quotient determinant](jet-quotient-determinant.md). At fixed $v,h,f,C$,
write $Q=(i,j)$, $P=[A:B:q]$, $l=d/f$, and

$$n_x=A-qi=lY,\qquad n_y=B-qj=lZ.$$

Both $n_x,n_y$ are eligible-smooth of polynomial height. Keep the
uncompressed box, so $l=q^{.7998+o(1)}$, $N=q^{.1348+o(1)}$, and
$w=\log_q(H/N^3)\ge0$ for the weighted coefficient norm $H$. On the
remaining low-norm cubics both axis fibers are squarefree. Let
$S_x,S_y$ be their respective bad sets from leading coefficients,
discriminants, and $q$, and keep the full bad parts $b_x,b_y$ of the
two outputs. Form the single good-axis modulus

$$M=\operatorname{lcm}(n_x/b_x,n_y/b_y).$$

This uses the larger valuation at every prime, never their sum.
Let $S$ be one prescribed set of $O(\log q)$ primes at this filter.
For example, $S$ can include both bad supports, the support of $f$,
and chosen reference supports. It is held fixed across the points
being counted. We prove an additional paid screen, not a lower bound
on what the actual columns supply.

## Local divisibility with the jet normalization

For $G\mid M$ and $p^k\parallel G$, label a good axis whose output
has valuation at least $k$. If it is the first axis, put
$t=i-A/q$, and choose the root of the vertical fiber modulo $p$ that
the second coordinate occupies. If it is the second, exchange the
coordinates. The root is simple, and its Hensel lift at $t=0$ gives
an integral analytic parametrization on $p\mathbb Z_p$ by $t$ as in
the [one-axis test](through-point-components.md#one-paid-test-on-a-smooth-plane-cubic).
The class is *marked* if the chosen root is the other coordinate of
$P/q$ modulo $p$. Otherwise $p\nmid l$, because both displacements
are in $l\mathbb Z_p$. On a marked branch both displacements are
integral power series with constant term zero. In particular the
valuation of the selected displacement is the minimum of the two
valuations; they are equal if both axes are good. This holds even
if $p\nmid l$ on the marked branch. Thus marked status is not a test
for membership in the support of $l$.

For the degree-$m$ jet lattice $K_{m,r}$, the normalized evaluation
on a marked branch is $(t/l)^r$ times an integral power series in
$t$, with coefficients integral linear in the jet form. Indeed each
form vanishes to order at least $r$ at $P$, so substitution of the
parametrization has no terms of degree less than $r$. On an unmarked
branch it is $l^{-r}$ times an integral power series, with no forced
row factor. This gives the following divisor of the wedge coordinates
on any $a$ distinct evaluations in one class, in valuation notation:

$$
 \sum_{u<v} v_p(t_v-t_u) +
 \begin{cases}
 r\sum_u (v_p(t_u)-v_p(l_u)), &\text{marked},\\
 0, &\text{unmarked}.
 \end{cases} \tag{1}
$$

To prove the first sum, extract the row factors. Each square minor
of the truncated analytic rows is an alternating polynomial in the
$t_u$, divisible over $\mathbb Z_p$ by the Vandermonde. Pass to the
$p$-adic limit, where divisibility by the fixed prime power persists.
For points on the same branch, equal parameters would give equal
points, so there is no difference zero in a nonzero wedge. For (1)
each prime has its own branch, axis, and parameters.

Define $J=J_Q(G)$ to have $p$-valuation $(k-v_p(l))_+$ at the
marked primes of $G$, and zero at the others. The marking is in fact
independent of which qualifying good axis is chosen: It means both
outputs are divisible by $p$. At a marked prime with a good axis,
$v_p(l)+\min(v_p(Y),v_p(Z))$ is the valuation of its parameter.
Thus $J\mid(Y,Z)$ even if only one axis is good, and at full selected
exponent the marked gain is exactly the excess above $l$. In
particular, two coincident good-axis powers coming entirely from
$l$ contribute just one Vandermonde factor and **no** row factor.

Group by $G$, the axis and root at each prime, and the divisor $J$ of
$G$. With $V=\binom a2$, (1) gives the common divisor $G^V J^{ra}$
in the integral wedge. The reduction to a primitive wedge on the
saturated quotient $K_{m,r}/C K_{m-3,r-1}$ works exactly as in (1) of
the quotient proof. Hence full rank requires

$$G^V J^{ra} (\inf l)^{ra} H^b
  \ll_{m,r} N^{2S_{m,r}}\|(A/N,B/N,q)\|^{L_{m,r}}, \tag{2}$$

where $a,b,S_{m,r},L_{m,r}$ are its cubic ranks and exponents (the
subscripts distinguish $S_{m,r}$ from the prime support). Failure
of full rank costs at most $3m$ points by the same Bézout argument.
This determinant uses the branch divisor instead of a separate
crossing divisor; overlapping primes cannot also be used as an
independent crossing in (2).

## Pay once for the outside radical

Use $(m,r)=(10000,1200)$ and write $V_2=V/b$, $V_1=ra/b$ as in the
quotient proof. Put $\tau=.0207$ and $D_* = T+\tau V_2$, where its
$T=23533757663/123164002500$ is the norm threshold *after* the ordinary
crossing. We can price all points admitting a $G\mid M$ such that the
second inequality below holds with fixed positive slack:

$$\operatorname{rad}(G_{\bar S})\le q^{\tau+o(1)},\qquad
 w+V_2\log_q G+V_1\log_q J>D_*. \tag{3}$$

Here the radical bound is uniform, and a first-crossing overshoot by
one eligible prime is allowed. Indeed, enumerate the outside radical
by the eligible-prime half-power estimate (cutoff at most
$(\log q)^{2+o(1)}$). Its support and $S$ together have $O(\log q)$
primes. Enumerate all exponent patterns on this support of polynomial
height at subpower cost by the fixed-support Rankin argument. The
axis and root labels cost at most $6^{\omega(G)}$, and the choice of
$J$ costs divisor-many, both subpower. The archimedean bound in (2)
gives (3) using $\|(A/N,B/N,q)\|\le q^{2.110+o(1)}$. Thus there are
at most $q^{.01035+o(1)}$ columns per filter on the priced family,
using divisor recovery per point. Including the existing joint
$(h,f)$ sum, the price is $q^{.13795+o(1)} < q^{1121/8125+o(1)}$ in
exponent. This is the same restricted cofactor budget as before.

There is a convenient seed criterion. For $G_0\mid M$, with
$\operatorname{rad}((G_0)_{\bar S})\le q^\tau$, put $J_0=J_Q(G_0)$.
The following suffices, with fixed slack:

$$w+V_2\log_q\frac{G_0}{\operatorname{rad}((G_0)_{\bar S})}
       +V_1\log_q J_0 > T. \tag{4}$$

Add unused outside primes of $M$ until the outside radical reaches
$q^\tau$, then apply (3); the old exponents need not be changed.
If the full outside radical is too small to cross, take $G=M$ in
(3). In the small-bad class $M\ge l/l_{S_x\cap S_y}\ge
q^{.7198-o(1)}$: Primes of $l$ good on at least one axis are included,
and $l_{S_x\cap S_y}\mid b_x,b_y$, one of which is below $q^{.080}$.
Thus (3) holds in this fallback without any surplus. The seed is not
enumerated separately.

In particular take $G_0=M_S$. At $w=0$, the required logarithm of the
free modulus without surplus is $T/V_2= .02269924\ldots$, so
$M_S\ge q^{.023}$ prices a point. With the entire free part marked
and surplus (no contribution to $l$), the required logarithm is
$T/(V_2+V_1)=.02095309\ldots$, so $q^{.021}$ suffices. This is a
joint screen: For example, the price inequality allows disjoint
supported contributions of exponent $.012$ from each axis, even
though each would miss the former $.0243$ one-axis credit. This is
an example of the credit arithmetic, not an assertion that these
sizes occur in the retained list. Also, at $w\ge.0024$, a seed of
outside marked primes carrying two copies in $M$ and at most one
in $l$, with radical first crossing $q^\tau$, suffices directly by
(3) with $G$ the square of this radical. A first crossing of the
radical is allowed here since its overshoot is subpower. Neither
repetition nor supported credit is forced by eligible smoothness.

## Why a fresh purchased modulus does not suffice at low norm

For the finite parameters above, an unsupported squarefree $G$ at
the crossing budget, **even granting $J=G$**, needs
$w>.17655546\ldots$ for (3) to pass at the leading exponents. Granting two
copies per purchased prime with one surplus improves that threshold
to $.00230800\ldots$, still positive. The latter failure at $w=0$
holds for **all** admissible $(m,r)$ for this determinant test, even
using the full available exponent $\tau_*=2(1121/8125-.1276)=337/16250$.
In fact $a=3m-r$, and the exponent of the right side of (2) less its
left side at $w=0$, granting $\log_q G=2\tau_*$ and
$\log_q J=\tau_*$, is bounded above by the usual archimedean exponent
calculation. The *computed bound*, which is the one that would need
to be negative to force rank loss uniformly at the stated heights,
is

$$
 (.2022-9\tau_*)m^2+(-.2894+3\tau_*)mr+.8672r^2
             +(.0674+\tau_*)(3m-r)-.1348 . \tag{5}
$$

Here $S_{m,r}=(3m^2-3m+2-r^2+r)/2$, $L_{m,r}=rm$, and
$b=(m^2-3m+2-r^2+r)/2$, and $2V+ra=(3m-r)(3m-1)$.
The quadratic part is positive definite by its discriminant,
and the remaining part is positive for $1\le r\le m-2$. Thus
these credits cannot force a contradiction from the uniform upper
bound alone, even if every selected prime is so favorable. This is
not a lower bound for the actual archimedean determinant, nor does
it rule out two surplus copies, supported parts, or an independent
source of small archimedean height. The exact arithmetic is in
[`check-jet-axis-lcm.py`](check-jet-axis-lcm.py).

**Decision.** Add (3) and (4) to the priced component tests, with
the same conditional ordered-triple and all-reference sums as
before. A simultaneous modulus is useful for jointly supported
parts, repeated powers, or marked surplus; simply switching the
paid crossing from $l$ to the LCM does not price the low-credit
smooth cubic residual. On the residual the missing input is either
an independent reason that the seed credit in (4) must occur, or a
sharper determinant estimate there. In (1) the precise unused local
term is the pairwise parameter difference beyond the common prime
power. A next test using actual references should price that
pairwise credit before treating it as a common divisor. Unrestricted
cofactors and the full denominator-pair complement remain open.
