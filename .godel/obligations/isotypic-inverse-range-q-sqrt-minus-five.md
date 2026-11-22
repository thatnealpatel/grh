# The inverse range at the archimedean stage

**Result (ordinary mathematics):** For $F=\mathbb Q(\sqrt{-5})$, its
nontrivial ideal-class character $\chi$, and $S=S_\infty$, every
$\Phi\in L(s,\chi)\mathcal O(\mathbb C)\cap AS(\mathbb C)$ is realized
by an archimedean Schwartz test after projected unit-ball insertion.
The [insertion](isotypic-exhaustiveness-q-sqrt-minus-five.md) and
[reflected gluing](isotypic-fourier-gluing-q-sqrt-minus-five.md) audits
started with a test. This repair starts with an arbitrary target and
uses the separated-height bound to divide through the zeros. It does
not prove the general converse theorem or require vanishing local
moments.

## Printed versus corrected denominators

The denominator switch was checked in the rendered pp. 308–309 of the
[digest-matched edition](../sources/masullo/README.md), inspecting pixel
crops for the subscripts and using the layout text to locate the
formulas. On p. 308 the definition of $\lambda_S$ and the displayed
definition of $\psi_S$ divide by the **omitted** product
$L_{\Sigma_F-S}(\chi,s)$ (with the common polar polynomial, which is
$1$ here). The unnumbered ratio on p. 309 still has that subscript.
In (6.3.2.16) and (6.3.2.17), p. 309, both denominators instead have
$L_S(\chi_S,s)$, the **retained** product. The final insertion equation
on the same page multiplies by the omitted product again. Keeping the
retained denominator in (6.3.2.16) cannot give that range inference:
At $S_\infty$, insertion multiplies by $L_f$, not by the complex Gamma
factor.

The corrected forward denominator is $L_f(s,\chi)$. For the *same*
numerator $\Phi$ on the reflected side it is
$E(s)L_f(1-s,\chi)$ with $E(s)=20^{1/2-s}$. This is consistent with the
*initial* omitted denominator used with the *different* reflected
numerator on p. 308: If $Z_S(f_0,s)=\Phi(s)$, then
$Z_S(\widehat f_0,1-s)=\Phi(s)/\rho_S(s)$ on the overlap, and
$\rho_S(s)L_f(s,\chi)=E(s)L_f(1-s,\chi)$. One need not construct $f_0$
for this repair. This reading of pp. 308–309 does not upgrade the
previous extraction-only readings of pp. 305–306.

## Holomorphy and overlap

Write $D(s)=L_f(s,\chi)$, and let $G(s)=2\pi(2\pi)^{-s}\Gamma(s)$ be
the Mellin transform of the self-dual Gaussian for the trace pairing.
By the completed product ((3.2.1.2), (3.2.1.5), p. 123), there is an
entire $U$ with $\Phi=U G D$, absorbing the constant between $G$ and
the printed complex factor. The completed function is entire on this
nontrivial norm-one isotype (Proposition 3.2.1.3(1), p. 123), and
$D$ is entire by division by $G$, whose reciprocal is entire. Use
the reflected insertion identity from the preceding audit:

$$
G(s)D(s)=E(s)G(1-s)D(1-s).
$$

Consequently the meromorphically continued quotients are exactly

$$
Q_+(s)=\frac{\Phi(s)}{D(s)}=U(s)G(s),\qquad
Q_-(s)=\frac{\Phi(s)}{E(s)D(1-s)}=U(s)G(1-s).
$$

These identities include cancellation to full order at the zeros in
the respective open half-planes. The only possible poles of $Q_+$ are
$0,-1,-2,\dots$, and those of $Q_-$ are $1,2,3,\dots$, hence neither is
singular inside its own half-plane. At $S_\infty$, $J_{F,S}$ is
$\mathbb C^\times/\{\pm1\}$ and the restriction of $\chi$ is trivial.
The section $t\mapsto[\sqrt t]$ has squared complex norm $t$, so the
coordinates of the two local characters are exactly $s$ and $1-s$.
By the self-dual Gaussian and (3.3.1.2), p. 129, the local factor is
$\rho_S(s)=G(s)/G(1-s)$. Thus $Q_+=\rho_S Q_-$ on $0<\Re s<1$,
including at the finite $L$-zeros. The p. 123 and p. 129 formula
readings are provisional (text, not rendered-page review).

## Separated-height estimate on the whole strip

Set $B(s)=sQ_+(s)=2\pi(2\pi)^{-s}U(s)\Gamma(1+s)$. This cancels
just the possible simple pole at $0$ and is holomorphic on $\Re s>-1$.
It need not be entire or vanish at $0$. Work on $-1/2\le\sigma\le 2$,
writing $s=\sigma+it$.

- On $\sigma=2$, the absolutely convergent Euler product gives
  $|1/D(2+it)|\le\zeta_F(2)$: Each reciprocal factor has modulus
  at most $1+q_v^{-2}\le(1-q_v^{-2})^{-1}$. This works uniformly on
  every right half-plane bounded away from $\Re s=1$.
- On $\sigma=-1/2$, the reflected argument has real part $3/2$ and
  $$
  \frac{1}{D(s)}=\frac{G(s)}{E(s)G(1-s)}\frac{1}{D(1-s)}.
  $$
  There is no Gamma pole on this line, and the Euler bound at $3/2$
  applies to the last factor. By Stirling, $|G(s)/G(1-s)|\ll |t|^{-2}$
  for $|t|\ge 1$. Also $|E(s)|$ is constant on this line. The bounded
  ordinates are harmless by continuity and the same nonvanishing
  argument. Thus the reciprocal is bounded on this entire edge.
- Corollary B.6.1.8, (B.6.1.45), p. 643, at $m=0$ bounds $1/D$ by
  $A|T|^\beta$ uniformly on $[-1,2]+iT$ at arbitrarily large $|T|$.
  Here the omitted product is exactly $D$. The real Euler coefficients
  give $D(\overline s)=\overline{D(s)}$ by continuation, so each good
  absolute height gives a pair of good opposite edges. We use the
  polynomial bound in the actual ordinate, not the sequence index.
  No bound on derivatives of $1/D$ is needed. This is use of the
  manuscript's estimate, not a new proof of that estimate.

For each $N\ge0$, the rapid decay of $\Phi$ on the closed strip gives
one constant $C_N$ bounding $|s^N B(s)|$ on the two vertical edges
and both horizontal edges at all sufficiently large good heights.
On these edges use $s^N B=s^{N+1}\Phi/D$, so the extra power from
regularization and the polynomial reciprocal bound are both absorbed
by a higher Schwartz seminorm of $\Phi$. For any point of the strip
choose a good height above its absolute ordinate and apply maximum
modulus to $s^N B(s)$ on that rectangle. The uniform bound $C_N$
therefore holds throughout the strip, across all the zeros and $s=0$.
This uses no a priori bound for $1/D$ in the interior.

## Transfer and realization

For $Q_+$ on a closed interior strip in $\Re s>0$, use $B/s$ up to
$\sigma=2$ and the direct Euler bound farther right. For $Q_-$ between
$\sigma=-1/2$ and any fixed $b<1$, use

$$
Q_-(s)=\frac{G(1-s)}{sG(s)}B(s),\qquad
\frac{G(1-s)}{sG(s)}=(2\pi)^{2s-1}\frac{\Gamma(1-s)}{\Gamma(1+s)}.
$$

The factor has no pole at $0$ and is holomorphic on the working
strip. The exponent of $|t|$ in its uniform Stirling estimate is
$-2\sigma$, so it grows at most polynomially on this bounded-width
strip. For $\sigma\le-1/2$ use the direct bound on the reflected
Euler product at $1-\sigma\ge3/2$ and the boundedness of $E^{-1}$ on
any bounded-width strip. Joining these estimates gives rapid decay
on each closed strip strictly inside $\Re s<1$ as well. In either
half-plane the estimates for values give estimates for every
holomorphic derivative by Cauchy on fixed-radius circles in a
slightly wider interior strip. This is the interior-strip Schwartz
condition of Definition D.3.1.3, pp. 800–801 (provisional text
reading), not a bound uniform up to $s=0$ or $s=1$.

Theorem 5.4.1.1(1), pp. 265–266, takes a pair in
$AS(\mathbb C_{>0})\times AS(\mathbb C_{<1})$ and gives the exact
image criterion (5.4.1.3), the local overlap identity just checked.
It applies on the trivial local isotype, without assuming the global
class group trivial. It supplies a representative $f\in\mathcal
S(\mathbb C)$ with local transforms $(Q_+,Q_-)$. In particular, on
$\Re s>1$ the normalized inserted test has global transform
$D(s)Q_+(s)=\Phi(s)$ and hence realizes $\Phi$ by continuation.
For the literal measures the inserted multiplier is $A D(s)$ with
$A=20^{-1/2}$, so insert $A^{-1}f$ instead. The reflected leg scales
by the same constant. The possible poles at the local endpoints
encode, rather than suppress, the two local zero modes.

## Formal boundary and next check

The analytic specialization above is not a Lean theorem. The pinned
[`FiniteHeckeCharacterEulerProduct`](../../Proofs/Theorems/FiniteHeckeCharacterEulerProduct.lean)
addresses the finite product on $\Re s>1$, not its continuation or
its reciprocal at the separated heights. The exact analytic premise
for a formal specialization is a continued finite function with the
reflected identity and a uniform polynomial reciprocal bound on
arbitrarily far opposite edges covering $[-1/2,2]$. In a Lean
follow-up, test whether the accepted moving-disk zero-count and
horizontal-height machinery for the rational explicit formula can
supply the $m=0$ reciprocal bound for this actual continued class
character, rather than extrapolating the right-line Euler result.
The archimedean image criterion would also need a formal model.
