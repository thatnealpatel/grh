# Fixed-positive delete-33 laws cannot repair the cap by extending to −10

**Decision at depth $c=39/20$.** Keep the positive-side law of the
[tail-fiber near-witness](tail-fiber-deletion-33.md), and keep its third
field $B$ on the entire line. Allow any measurable law on $0\le u\le1$
on $[-10,0)$ with this $B$, including $B=0$ on the new interval
$[-10,-144/25)$. Set $A=0$ to the left of $-10$. Then the normalized
unfolded first cap at $t$ exceeds **$1.00000117$** for every such law.
No negative-side partition or smallness of the change in $A$ is assumed.
This does not exclude deeper left support or changes to the positive law.

## Exact feasibility test and starting point

Use the 1,257-knot [`delete-33-tail-baseline.txt`](deletion-laws/delete-33-tail-baseline.txt)
and the [fiber triples](deletion-laws/delete-33-tail-fiber.triples) of
`e8dc22900089fcb941e1a25756aa6243cb15d487`. Write $X=2u^2-1$,
$T(X)=4X^3-3X$, and $(A,B,U)=\mathbb E(X,T(X),u)$. On each positive
slab select the rational law from the triples if it improves $U$,
otherwise keep the reference. Mix $53/1000$ of the upper-branch
atom $X=f(B)$, $f(b)=\cos(\arccos(b)/3)$, into $[49/25,393/200)$.
The triple-angle identity shows that this preserves $B$ exactly.
The checker verifies the three-site weights against the reference
moments and recomputes the resulting $M-8/9$, where
$M=\int_0^\infty ze^{-z}U(z)\,dz$. It encloses the surplus near
$9.38794592175\cdot10^{-9}$. Every proposed negative law keeps this
same objective, since its weight vanishes on the negative side.

The third-field cap and the simultaneous three-site second completion
are unchanged. Independently replaying the retained checker on the
unchanged $B$ gave cap below $0.999975$ and repaired Gram multiplier slack
above $1.4098\cdot10^{-6}$ (degree 256, grid 65,536, multipliers
$113.71074849,153.65856922,156.52872908$). No Gram data enter the
exclusion. At the target depth the first-cap test is exactly
$\|V_A\|_\infty\le 1$ on the whole real frequency line, where, for
step laws and $C_t=\cosh(39/20)/(6\cos(\pi/12))$,

$$V_A(x)=\frac{\sum_j e^{(-1/2+ix)z_j}\Delta A_j}{C_t(1/2+ix)}.$$

On a slab $[l,r)$ an increment of $A$ acts through the difference of
the endpoint exponentials divided by $C_t(1/2+ix)$; the term at an
infinite right endpoint is zero. On this reference the value at zero
is $1.000003424292674\ldots$, so it is not a witness at the target.
For step-law searches the jump envelope
$\sum_j e^{-z_j/2}|\Delta A_j|/(C_t|x|)$ bounds **both** frequency
rays. The exclusion does not need that envelope: A strictly positive
weighted violation at finitely many frequencies is already a failure
of the original continuous cap.

## A cut priced against all measurable negative laws

For measurable $A$ the equivalent normalized field is

$$V_A(x)=\frac{1/2-ix}{C_t(1/2+ix)}
  \int_{\mathbb R} e^{(-1/2+ix)z}A(z)\,dz.$$

The unit phase is important for the cuts, although not for the cap.
The weighted integral converges on both tails, and agrees with the
jump formula by integration on every slab. Use the exact decimal
entries $(x_j,\Re h_j,\Im h_j)$ in the
[144-cut table](deletion-laws/delete-33-left-extension.cuts).
Put $W=\sum_j|h_j|$. For any admissible candidate the cap requires
$\sum_j\Re(h_j V_A(x_j))\le W$. The left side is $\int \rho(z)A(z)\,dz$,
where

$$P(z)=\Re\sum_j\frac{h_j e^{(-1/2+ix_j)z}}{C_t(1/2+ix_j)},
\qquad \rho(z)=-P'(z).$$

The checker independently evaluates the reference cut sum by slab
primitives and by the original jump fields. With the original
negative side and its zero extension, the certified reference gap
$\sum_j\Re(h_jV_A(x_j))-W$ encloses $2.6063713306952\cdot10^{-6}$.

For each fixed $B=b$, the possible $A$ form exactly
$[-f(-b),f(b)]$. Indeed $f$ is the concave inverse of the increasing
convex branch of $T$ on $[1/2,1]$, and $X\le f(T(X))$ on $[-1,1]$.
Jensen gives the upper bound; symmetry gives the lower one. Both
endpoints are attained by atoms of third moment $b$, and mixtures
fill the interval. The new $B=0$ region is therefore charged at the
full amplitude $\sqrt{3}/2$. Let $m_b$ and $R_b$ be the midpoint and
radius of the allowed interval. On any reference cell $[l,r)$ of
constant $b$ and reference $A_*=a$, the exact minimum possible change
in the cut sum is

$$(m_b-a)(P(l)-P(r))-R_b\int_l^r |\rho(z)|\,dz.$$

The formula allows a change of the optimizer's endpoint at *every*
sign switch of $\rho$. It requires no restriction on the new law at
or between the old knots. Left of $-10$ the change is zero, and right
of $0$ it is zero by the fixed-profile hypothesis, including the
infinite terminal slab. All breakpoints of the reference are included
in the primitive sum and negative-side price.

### Rigorous absolute integral

Write $\rho(z)=e^{-z/2}\phi(z)$ with $\phi$ a finite real exponential
sum. On each cell expand $\phi$ about the midpoint to degree five.
With midpoint coefficients $a_j$, half-width $d$ and uniform sixth
coefficient bound $J_6$ obtained by the triangle inequality on the
exponentials, $|\phi(z)-a_0|\le E=\sum_{j=1}^5|a_j|d^j+J_6d^6$.
When $|a_0|>E$, the absolute integral is exactly $|P(l)-P(r)|$.
Otherwise it is at most
$2(e^{-l/2}-e^{-r/2})(|a_0|+E)$. Accept this envelope only if it
overpays the signed-integral modulus by less than $10^{-10}(r-l)$;
otherwise bisect. Both branches are rigorous upper bounds on the
absolute integral. The extension cells of width $1/25$ are solely
for integration, not a law mesh.

The checker uses 128-bit Sage balls. Rounded summaries of the
allowances subtracted from the reference gap are $6.00263009\cdot10^{-7}$
on the extension and $8.29177923\cdot10^{-7}$ on the original negative
side (1,722 signed cells, 117 envelope cells). Dividing the remaining
positive gap by $W$ gives the lower bound on the cap minus one.
In particular even if the positive profile is released, a necessary
condition for a repair with this left cutoff is that its change
contribute **less than $-1.1769\cdot10^{-6}$** to the same cut sum,
that is, to $\int_0^\infty \rho(z)(A(z)-A_*(z))\,dz$.

## Search and replay

The cuts were nominated by a tangent-cut minimax LP, allowing the full
admissible negative intervals on the original 494 slabs plus 106 new
slabs of width $1/25$. It added tangents at numerical off-grid maxima
as well as sampling near zero. At the last successful exchange solve
on this mesh the LP reported a sampled optimum excess near
$2.1134\cdot10^{-6}$ but the candidate had off-grid modulus exceeding
3.67. The retained cuts are the weighted tangent directions, not a
candidate law. The LP neither proves optimality nor proves infeasibility
of the cap. The certificate proves the latter independently of the LP
and even covers refinements at arbitrary new negative knots. In further
exploratory runs to $-12$ and $-14$, the sampled candidates had much
larger off-grid excursions, and the repriced $-12$ cuts did not yield a
positive gap for that extension. Those cutoffs are unresolved.

From the repository root, with assertions enabled:

```sh
PYTHONDONTWRITEBYTECODE=1 /opt/sage-10.9/bin/python .godel/bob/check-left-extension-deletion-33.py
```

The replay bounds the normalized lower-bound expression in
`[1.0000011769303809503196036139340 +/- 5.16e-32]`. This is an
expression that lower-bounds the norm, not an enclosure of the norm
itself. No proposed law passed the original continuous cap at $39/20$.

**Next decision.** Do not refine the negative mesh at cutoff $-10$
for this fixed positive law. A refit that leaves the cutoff at $-10$
must pay the signed positive-side score above while keeping $M>8/9$.
If instead retaining the positive profile, reoptimize the cut *after*
pricing its absolute integrals on the deeper extension; the present
cut's numerical extension price already consumes its margin at
$-10.1$. A result with no left cutoff needs a continuous-frequency
certificate: [any finite set of samples can be canceled far enough
left](fixed-third-price-deletion-33.md#why-finite-cuts-cannot-settle-unbounded-left-support).
