# The interior-line completion need not have an L² boundary trace

**Result:** Proposition 9.2.2.4(2), p. 414, (9.2.2.20), fails
at $s=2$, $I=[-1,1]$, and $b=1$ for an allowed family of interior
lines. The exhibited completion element has a holomorphic
interior representative and its right-edge limit exists for
every $\tau\ne 0$, but it is not locally in $L^2(d\tau)$ near zero.
Changing the value at zero does not help. This is ordinary
mathematics, not Lean.

The [accepted point-evaluation audit][point] instead showed that
evaluation on the edge is discontinuous on the dense test class.
That did not rule out an $L^2$ trace. Its separate source checks
of the point cutoff and of the positive Sobolev norm are inherited,
not repeated here. The [weighted log jet theorem][lean] concerns
the positive norm, not the completion tested below.

## Printed statement and domain

In the [pinned edition][pin], Definition 9.2.2.3, p. 414,
completes $A\mathcal S(\mathbb C)$ in the metrizable topology of
the **separate** norms (9.2.2.19). The real sequence must have
both boundary points as accumulation points; it need not include
either edge line. We interleave, for $n\ge0$,

$$
\sigma_n^\pm=\pm\left(1-\frac{1}{n+2}\right).
$$

The strip convention (B.5.3.1), p. 632, puts these lines in
$\mathbb C_{\mathrm{Int}(I)}$. Set $c_{2n}=\sigma_n^+$ and
$c_{2n+1}=\sigma_n^-$. Proposition 9.2.2.4 admits real
$s\ge0$. Part (2) says that for **every** element $u$ of the
completion and **every** finite $b\in\partial I$, the limit
$u_b(\tau)=\lim_{\sigma\to b,\,\sigma\in\mathrm{Int}(I)}
 u(\sigma+i\tau)$ exists for almost all $\tau\in\mathbb R$ and
belongs to $W^{s,2}(\mathbb R)$. This entails $L^2$ membership:
The nonnegative degree Sobolev weight is at least one under
Plancherel (9.1.1.3)–(9.1.1.5), p. 396, with Sobolev notation
as in (9.1.2.1)–(9.1.2.3), p. 399. Independently, the proposition's
even-degree $b$-line $\mathrm{HS}_b^{s,2}$ conclusion includes the
order-zero $L^2$ norm by (9.2.1.3), p. 404. No trace assertion
about a single point is needed.

Take a smooth $0\le\eta\le1$ that is zero on $(-\infty,1/2]$
and one on $[1,\infty)$. For integers $R\ge2$, let $0\le\chi_R\le1$
be smooth, one for $x\le R$, and zero for $x\ge R+1$. Put
$f(x)=\eta(x)e^{-x}$, $f_R(x)=\chi_R(x)f(x)$, and
$\phi_R(t)=f_R(\log t)$. The $\phi_R$ are smooth and compactly
supported in $\mathbb R_{>0}$. In the positive-sign convention of
Proposition D.3.2.5, p. 802, (D.3.2.2), their transforms are

$$
u_R(z)=M(\phi_R)(z)=\int_{\mathbb R} f_R(x)e^{zx}\,dx.
$$

Compact support gives entireness. For bounded real parts, repeated
integration by parts in $x$ gives rapid vertical decay, also for
each derivative obtained by replacing $f_R$ with $x^j f_R$.
Thus each $u_R$ lies in the dense test class
$A\mathcal S(\mathbb C)$ of Definition D.3.1.3, pp. 800–801.

## Completion membership: Each fixed line

Write $q_{\sigma,j}(v)=(2\pi)^{-1}\|v^{(j)}(\sigma+i\,\cdot)\|_2$
for the norm in (9.2.2.19) with derivative order $j$. By Plancherel
for the kernel $e^{i\tau x}$, for fixed $\sigma<1$, $j\ge0$, and
integers $R,S\ge2$,

$$
q_{\sigma,j}(u_R-u_S)^2
=\frac{1}{2\pi}\int_{\mathbb R} x^{2j}e^{2\sigma x}|f_R-f_S|^2\,dx
\le\frac{1}{2\pi}\int_{\min(R,S)}^\infty
      x^{2j}e^{-2(1-\sigma)x}\,dx \longrightarrow 0.
$$

The sequence is Cauchy in the completion. The estimate holds
for every choice of interior lines accumulating at both edges,
including if **all** fixed derivative orders are imposed on each
line. It does not use an interpretation of the ranging of $k$
in (9.2.2.19), nor any uniform estimate as $\sigma\to1$.

## Boundary limit: Compute it from the interior function

Independently of the Cauchy calculation, on every compact set in
$\Re z<1$ choose $\delta>0$ with $\Re z\le1-\delta$. Then the
error from replacing $f_R$ by $f$ in the integral for $u_R$ is
bounded by $\int_R^\infty e^{-\delta x}\,dx$, so the locally
uniform limit is the holomorphic function

$$
u(z)=\int_{\mathbb R}\eta(x)e^{(z-1)x}\,dx
    =H(z)+\frac{e^{z-1}}{1-z},\qquad
H(z)=\int_{1/2}^1\eta(x)e^{(z-1)x}\,dx.
$$

This is the natural interior representative, without assuming
the boundary assertion: Its derivatives agree with the line
$L^2$ limits by the same Plancherel estimate with $f$ in place
of $f_S$. A holomorphic representative consistent with the
order-zero line limit is unique by continuity on that line and
the identity theorem.

For every $\tau\ne0$ the right-edge limit is
$H(1+i\tau)+e^{i\tau}/(-i\tau)$. Since $|H(1+i\tau)|\le1/2$,
the triangle inequality gives $|u_1(\tau)|\ge 1/(2|\tau|)$
for $0<|\tau|<1$. The square is not integrable on any
neighborhood of zero. Thus the tested Sobolev clause fails even
though the almost-everywhere existence clause holds for this
witness. The calculation does not test whether a boundary limit
exists almost everywhere for all completion elements.

## Cited input and scope

The proof on p. 414 cites Lemma 9.2.2.2 for the compact interval,
and cites Theorem B.2.2.4 in the reduction for the general case.
The compact-case norm comparison, p. 412, (9.2.2.5), compares the
positive norm with norms on the **actual endpoints** $\{a,b\}$.
The estimate in (9.2.2.14)–(9.2.2.16), p. 413, bounds an
interior weight by the endpoint weight, not conversely. It does
not supply endpoint control from separate interior-line Cauchy
estimates. In fact on $\sigma=1$, $f_R(x)e^x=1$ on $[1,R]$
and vanishes for $x\ge R+1$. For $S>R+1$ the squared order-zero
endpoint norm of $u_S-u_R$ is at least $(S-R-1)/(2\pi)$ by
Plancherel on $[R+1,S]$. This comparison does not use the
proposition's asserted transport. The witness is not a Cauchy
sequence in the topology that already controls that endpoint.

The obstruction is not tied to symmetric width or to a particular
Sobolev degree: Translating the Mellin variable by replacing
$e^{-x}$ with $e^{-b x}$ gives the same right-edge obstruction
at any finite right endpoint $b$ of a nondegenerate closed
interval for interior-only families in (9.2.2.19), regardless
of any fixed derivative orders used there. The check at $s=2$
does not rely on any particular convention for Sobolev order:
The limit fails the weaker $L^2$ requirement. It does not refute
trace or jet results formulated in the positive weighted norm,
and does not address idelic transport, quotient annihilation,
spectral totality, or trace assembly.

## Review evidence

Independent read-only review against
`1ae78700ba0d26934b4a59aa6fedfb88d545e078`: Yah session
`01a2023c-1df0-7791-a8fb-063d0b3dd75f`, agent `tDrIbWS`
(`trace-review`). Both readers matched the pinned digest and
inspected direct raster crops located with PDF layout coordinates.
The reviewer found separately:

- **Completion membership:** The rendered (9.2.2.19) permits the
  chosen abscissas and imposes separate line norms. The reviewer
  checked the strip, test-class, and Mellin definitions on
  pp. 632 and 800–802, verified rapid decay for the compact log
  tests, and independently obtained the fixed-line Plancherel
  bound for every fixed derivative order.
- **Actual boundary trace:** From the defining integrals, not an
  asserted extension of the Mellin transform, the reviewer
  obtained local uniform convergence, identified the resulting
  holomorphic representative with the line data, and derived
  the $1/(2|\tau|)$ lower bound on the punctured interval.
  The rendered (9.2.2.20), p. 414, requires both a.e. existence
  and $W^{s,2}$ membership; the reviewer checked the latter's
  $L^2$ implication and the independent even-degree line norm
  on pp. 396, 399, and 404.
- **Cited topology:** The rendered compact comparison on p. 412
  uses endpoint lines, and the estimates on p. 413 go from
  endpoint control to interior control. The reviewer separately
  checked that the truncations are not Cauchy in the endpoint
  norm. The p. 414 footnote says only “Return here”; the general
  reduction via B.2.2.4 is not needed for the compact verdict.

These findings agree with the membership and trace calculations
above. No manuscript reading needed for this verdict remains
provisional. The displayed derivative-index range is ambiguous,
but no resolution is used.

## Bounded successor

Test an **endpoint-controlled replacement** at degree two for a
nondegenerate compact interval $[a,b]$: Given a Cauchy sequence
for the order-zero and order-one norms on both actual endpoint
lines, determine whether its weighted log limit gives uniform
inward convergence in $\tau$ to the Fourier boundary value at
each endpoint. This would establish the pointwise trace step for
a repaired scalar topology, not reinstate the printed one.
Higher and fractional degrees, idelic realization and transport,
and the passage to quotient annihilation, totality, and trace
assembly are separate obligations.

[point]: boundary-point-evaluation.md
[pin]: ../sources/masullo/README.md
[lean]: ../../Proofs/Props/BoundaryLogJet.lean
