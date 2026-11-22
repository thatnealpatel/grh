# Common good heights for the quadratic class denominator

**Result (also proved in Lean for the explicit product):** Put
$D=L(\cdot,\chi_{-4})L(\cdot,\chi_5)$, the entire finite denominator
identified in the
[prime-by-prime calculation](isotypic-euler-factorization-q-sqrt-minus-five.md).
There are constants $C,A>0$ such that every real $H\ge1$ admits a
$T\in(H,H+1)$ with

$$
\inf_{-1/2\le\sigma\le2}|D(\sigma+iT)|\ge C^{-1}T^{-A}>0.
$$

This supplies the $m=0$ horizontal edge in the
[corrected inverse range](isotypic-inverse-range-q-sqrt-minus-five.md)
at $S=S_\infty$ for the nontrivial class character of
$\mathbb Q(\sqrt{-5})$. The same height also gives polynomial
reciprocal bounds for both individual factors. The segment estimate
alone does not bound derivatives; the [Cauchy step below](#all-orders-cauchy-bound-at-the-same-height)
uses the full closed disks.

## Source interface

The [accepted inverse-range note](isotypic-inverse-range-q-sqrt-minus-five.md)
records independent visual inspection of pp. 308–309 of the
[pinned edition](../sources/masullo/README.md). It distinguishes the
omitted product in the initial quotient from the retained product in
(6.3.2.16)–(17), p. 309, §6.3.2. Here we bound the omitted product
$D$, not the retained Archimedean factor or a completed $L$-function.
Masullo's upper-growth input on p. 642, (B.6.1.37), is a provisional
reading from the Appendix B Markdown and numbered PDF layout: A
polynomial upper bound for the omitted product on a bounded strip
for large $|\Im s|$. The radius-six estimate here serves the same
purpose for this explicit product, with different scope. It does not
assume (B.6.1.37) or the other provisionally read estimates on
pp. 641–643, (B.6.1.35) and (B.6.1.45), and does not certify the general
Appendix B argument.

## Upper growth and anchor

For one of the two characters $\psi$ of period $q$, let
$A_0(x)=\sum_{1\le n\le x}\psi(n)$ on $[1,\infty)$. The sum of one
period is zero, so $A_0$ is $q$-periodic and bounded. Recursively take
$a_j=q^{-1}\int_1^{1+q}A_j(x)\,dx$ and
$A_{j+1}(x)=\int_1^x(A_j(u)-a_j)\,du$. Each $A_{j+1}$ is bounded,
$q$-periodic, locally absolutely continuous, and zero at $1$.
Initially for $\Re s>1$, summation by parts gives
$L(s,\psi)=s\int_1^\infty A_0(x)x^{-s-1}\,dx$. Removing the mean
and integrating by parts five times gives, with
$(s)_j=\prod_{k=0}^{j-1}(s+k)$ and $(s)_0=1$,

$$
L(s,\psi)=\sum_{j=0}^4 a_j(s)_j
            +(s)_6\int_1^\infty A_5(x)x^{-s-6}\,dx.
$$

At step $j$ the constant contributes $a_j(s)_j$, and the primitive
contributes the next integral with prefactor $(s)_{j+2}$. The boundary
terms vanish by boundedness at infinity and $A_{j+1}(1)=0$. The final
integral converges locally uniformly for $\Re s>-5$, as do the
integrals with extra powers of $\log x$ on compact subregions. Thus
entireness and uniqueness of continuation extend the equality there.
For $\Re s\ge-4$, the last integral is bounded by
$\|A_5\|_\infty\int_1^\infty x^{-2}\,dx=\|A_5\|_\infty$. Consequently
$|L(s,\psi)|\ll (1+|s|)^6$ there, with constants fixed for these two
characters. No convexity estimate or Stirling approximation is needed
for this upper bound.

Use the center $c=2+i(H+1/2)$ and radii $3,5,6$. On the outer closed
disk $\Re s\ge-4$ and $1+|s|\ll H$ for $H\ge1$, so choose
$M=C_0H^{12}\ge1$ bounding $|D|$ there. The whole rectangle
$[-1/2,2]+i[H,H+1]$ fits in the closed radius-three disk, since
$|\Re(s-c)|+|\Im(s-c)|\le5/2+1/2=3$.

At $c$ the two absolutely convergent Euler products give
$|D(c)|^{-1}\le\prod_p(1+p^{-2})^2\le\zeta(2)^2$. In particular,
$|D(c)|\ge b>0$ independently of $H$. Equivalently, one can majorize
the two absolutely convergent Möbius-twisted reciprocal series at real
part two.

## Full-order disk factorization

Let $\rho$ range over the zeros in $|s-c|\le5$, with orders
$m_\rho$ and total order $N=\sum_\rho m_\rho$. Jensen at radius six
gives

$$
N\log(6/5)\le\log(M/|D(c)|)\le\log(M/b).
$$

If there is a zero on radius six, apply Jensen at radii approaching
six from below and take the limit in this inequality. In particular
$N=O(\log(2H))$. Set $P(s)=\prod_\rho(s-\rho)^{m_\rho}$ and
$g=D/P$ with removable singularities filled. This is entire and is
zero-free on $|s-c|\le5$. On the circle of radius six each
$|s-\rho|\ge1$, whence $|g(s)|\le M$ there and inside by maximum
modulus. At the center $|g(c)|\ge b\,5^{-N}$.

The nonnegative harmonic function $u=\log M-\log|g|$ on the open
radius-five disk satisfies $u(s)\le4u(c)$ on $|s-c|\le3$ by Harnack's
inequality (radius ratio $(5+3)/(5-3)$). Hence

$$
\log|g(s)|\ge\log M-4\big(\log(M/b)+N\log5\big)
$$

throughout the rectangle. This costs $O(\log(2H))$, independent of
how close the zero ordinates are to one another.

## Average the total logarithmic loss

For real $t$ not equal to a listed ordinate set

$$
S(t)=\sum_\rho m_\rho\log^+\!\left(\frac{1}{|t-\Im\rho|}\right).
$$

Each summand without its multiplicity has integral at most
$\int_{-1}^1-\log|u|\,du=2$ over the unit interval. Values at the
finitely many exceptional ordinates do not affect the integral. Thus
$\int_H^{H+1}S(t)\,dt\le2N$. For $N>0$, the set in the open
interval with $S(t)\le4N$ has measure at least $1/2$ by Markov's
inequality; discard the finitely many exceptional ordinates. For
$N=0$, any interior height works. At the chosen $T$, uniformly in
$\sigma$, the inequality $|\sigma+iT-\rho|\ge|T-\Im\rho|$ gives

$$
\log|P(\sigma+iT)|\ge-S(T)\ge-4N.
$$

Combining with the lower bound for $g$ gives
$-\log|D(\sigma+iT)|\le C_1+C_2\log H$ for constants independent
of $H$ and $\sigma$. Exponentiate and use $T>H\ge1$, increasing
the exponent to a positive one if necessary. This is a single height
for the product and both factors, counting coincident zeros with the
sum of their orders. The individual upper bounds above imply the
individual reciprocal bounds there, by $|L_1|^{-1}=|L_2|/|D|$ and
vice versa. A minimum gap estimate of size $1/\log H$ by itself
would charge $\log\log H$ per zero, losing the polynomial conclusion.

By real Dirichlet coefficients and continuation,
$D(\bar s)=\overline{D(s)}$. The same good heights with the opposite
sign provide the second horizontal edge for maximum modulus. No
reciprocal estimate in the interior through its zeros is implicit in
this step.

## Lean boundary and next check

- [`Masullo.exists_qSqrtNegFiveDirichletProduct_right_anchor`](../../Proofs/Lemmas/DirichletRightAnchor.lean)
  proves a uniform positive center bound via the Möbius series.
- [`Masullo.exists_goodHeight_disk_factorization`](../../Proofs/Lemmas/AnalyticGoodHeightDisk.lean)
  bounds the full zero count and lower modulus of the residual factor
  via Jensen, maximum modulus, and Borel–Carathéodory.
- [`Masullo.exists_goodHeight_sum_posLog`](../../Proofs/Lemmas/LogLossGoodHeight.lean)
  chooses an interior height avoiding every listed ordinate with
  aggregate loss at most $2N$ (sharper than the $4N$ above).
- [`Masullo.qSqrtNegFiveDirichletProduct_good_heights_of_circle_growth`](../../Proofs/Theorems/IdealClassGoodHeights.lean)
  combines these into the common-height bound with nonvanishing,
  conditional only on the radius-six circle upper bound $C_0H^k$ for
  real $H\ge H_0\ge1$. It needs no Hecke identification hypothesis.

The upper-growth premise is discharged for the explicit product:

- [Centered periodic primitives](../../Proofs/Lemmas/DirichletPeriodicPrimitives.lean)
  start from the actual step partial sums of a nontrivial character;
  periodicity, measurability, boundedness, and right continuity hold at
  every stage. The [improper integration-by-parts step](../../Proofs/Lemmas/BoundedPrimitiveIntegral.lean)
  applies even when the initial sum jumps.
- [`dirichlet_LFunction_eq_five_primitives`](../../Proofs/Lemmas/DirichletLFunctionGrowth.lean)
  identifies the five-step expression with Mathlib's `LFunction`
  by partial summation on $\Re s>1$ and holomorphic uniqueness on
  $\Re s>-5$. `exists_norm_dirichlet_five_primitive_tail_le` bounds
  the remainder **without** its rising prefactor uniformly on the
  closed half-plane $\Re s\ge-4$. The degree-six estimate for each
  factor holds on that same closed half-plane.
- [`qSqrtNegFiveDirichletProduct_circle_growth`](../../Proofs/Theorems/IdealClassGoodHeights.lean)
  gives one $C_0\ge1$ for all real $H\ge1$ and every point on the
  required circle, with $k=12$. `qSqrtNegFiveDirichletProduct_good_heights`
  applies the conditional endpoint at $H_0=1$ with this bound.

There is no growth hypothesis left for the explicit product. The
[all-prime grouped identity](isotypic-euler-factorization-q-sqrt-minus-five.md#checked-all-prime-grouped-identity)
now identifies it in Lean with the actual finite Hecke product on
$\Re s>1$ for the constructed class character.

## Closed disks at the same good height

[`Masullo.qSqrtNegFiveDirichletProduct_good_height_disks`](../../Proofs/Theorems/IdealClassGoodHeightDisks.lean)
proves that there are $c,C,A,B>0$ such that for every real $H\ge1$,
one $T\in(H,H+1)$ works for every $\sigma\in[-1/2,2]$ and every
$z$ with $|z-(\sigma+iT)|\le cT^{-B}$:

$$
D(z)\ne 0,\qquad |D(z)^{-1}|\le CT^A.
$$

The proof reuses the height from the segment theorem, not a separate
height for each disk. Write $s=\sigma+iT$ and $a=2+i(H+1/2)$.
The center satisfies $|s-a|\le3$. For any $w$ with $|w-s|\le1$,
the unit circle about $w$ lies within distance $5$ of $a$.
Maximum modulus extends the radius-six growth bound to that circle,
and the unit-radius Cauchy estimate gives $|D'(w)|\le C_0T^{12}$.
The convex mean-value estimate on the closed unit disk about $s$
then controls motion in every direction, also at the endpoint centers
$\sigma=-1/2,2$. With segment constants $C_s,A$, the choices
$B=A+12$ and $c=\min(1,(2C_sC_0)^{-1})$ limit the motion to at most
$(2C_sT^A)^{-1}$, half the guaranteed center modulus. The new
reciprocal bound has $C=2C_s$.

The [accepted rendered reading](isotypic-inverse-range-q-sqrt-minus-five.md#printed-versus-corrected-denominators)
of Masullo, pp. 308–309, §6.3.2, (6.3.2.16)–(17), supplies the
omitted-versus-retained distinction. The estimate is for the corrected
forward denominator, not the printed retained factor. No new source
reading is needed. The Lean statement uses the explicit entire $D$ and
no Hecke identification hypothesis. The separate half-plane identity
identifies the convergent finite Euler product only on $\Re s>1$.

Independent statement and reduction review: Yah
`01a2034f-03ff-70f0-801f-c1abcd71ab17`, agent `uwQNjpH`. The review
checked the quantifier order, full closed disks, reuse of the height,
and applicability of the inherited reading. No unverified manuscript
normalization is used in the disk proof.

Recovery session `01a203d3-a354-7089-ae50-bcb5f1d71d4d` adopted
`edca34eca146e3f6340c7a7f05d8cf5a0a4308b3` after its exact-candidate
`audit-local` passed the warning-as-error `Proofs` build, joint import,
and kernel replay of `Theorems.IdealClassGoodHeightDisks`. The built
`qSqrtNegFiveDirichletProduct_good_height_disks` matched the reviewed
statement and used only `propext`, `Classical.choice`, and `Quot.sound`.
A separate fresh import in the integration workspace applied it with
both Dirichlet factors written out. Neither check assumes or proves a
bound for higher derivatives.

## All-orders Cauchy bound at the same height

[`Masullo.qSqrtNegFiveDirichletProduct_good_height_inv_iteratedDeriv`](../../Proofs/Theorems/IdealClassGoodHeightDerivatives.lean)
reuses the constants $c,C,A,B>0$ and the witness $T\in(H,H+1)$ from
the closed-disk theorem for each real $H\ge1$. The **same** $T$ works
for every $\sigma\in[-1/2,2]$ and every $m\in\mathbb N$:

$$
\bigl|(D^{-1})^{(m)}(\sigma+iT)\bigr|
  \le m!\,C\,c^{-m}T^{A+Bm}.
$$

At each center the positive radius is $r=cT^{-B}$. Entireness and
nonvanishing on the closed disk make the reciprocal differentiable
on the open disk and continuous on its closure (`DiffContOnCl`). The
sphere bound is $CT^A$, so Cauchy's estimate gives $m!\,(CT^A)/r^m$.
Substitution gives the displayed bound, including $CT^A$ at $m=0$.
Both endpoint centers use the same full disks as the interior centers.

Independent statement and reduction review: Yah
`01a203de-6ff5-7f39-bb69-3f2a117e55d3`, agent `nPAgazk`. The review
checked the product definition, complex differentiability, full closed
disk and Cauchy interfaces, both endpoints, the $m=0$ specialization,
and the quantifier order. It also checked applicability of the
[inherited rendered reading](isotypic-inverse-range-q-sqrt-minus-five.md#printed-versus-corrected-denominators)
of pp. 308–309, §6.3.2, (6.3.2.16)–(17). This is a repair for the
omitted finite product, not an estimate for the printed retained
Archimedean denominator. No new manuscript reading is used.

This supplies the reciprocal derivative input for the corrected
forward quotient at the selected heights. It does not give such
bounds at arbitrary heights, on either full vertical line, through
zeros, or for general Hecke characters. The all-prime identification
on $\Re s>1$ is a separate accepted result, not a premise here.

**Next check:** For an entire numerator whose derivatives have
uniform rapid decay on the closed strip, use the iterated Leibniz
rule and this endpoint to bound every derivative of the corrected
forward quotient on the same selected horizontal segments. For
fixed order $m$ and desired decay $T^{-N}$, a numerator bound of
order $T^{-(N+A+Bm)}$ for derivatives through order $m$ suffices,
since $T>1$ and every reciprocal order $j\le m$ costs at most
$T^{A+Bm}$. This would transfer the assumed numerator seminorms at
the selected heights, not derive them from the printed test space.

**Separate obligations:** The reflected identity and the local
image criterion are not formalized here. The
[inverse-range realization](isotypic-inverse-range-q-sqrt-minus-five.md)
still uses provisional readings of the completed and complex local
normalizations (pp. 123 and 129), the interior-strip Schwartz
convention (pp. 800–801, Definition D.3.1.3), and the local image
criterion (pp. 265–266, Theorem 5.4.1.1(1), (5.4.1.3)).
