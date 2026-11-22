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
formulas. An independent reviewer confirmed the raster reading. On
p. 308 the definitions of $\lambda_S$ and $\psi_S$ divide by the
**omitted** product
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
for this repair. See the separate [rendered gluing audit](isotypic-fourier-gluing-q-sqrt-minus-five.md#source-interface)
for (6.3.2.11) and (6.3.2.13), pp. 305–306.

## Verified completed product and divisibility

**Result (ordinary mathematics, not Lean):** Proposition 3.2.1.3(1),
p. 123 of the [pinned edition](../sources/masullo/README.md), gives an
entire continuation of the **completed** $L(s,\chi)$ for the nontrivial
ideal-class character of $F=\mathbb Q(\sqrt{-5})$. The proposition's
opening refers to (3.2.1.2) on $\Re s>1$, as does Definition 3.2.1.2.
Part (1) says it is entire when $\chi|_{C_F^1}$ is nontrivial; the
exception in part (2) tests triviality on $C_F^1$, not triviality at
infinity. Here $C_F^1$ is the kernel of the descended idelic norm
(Definition A.1.4.1, (A.1.4.2), p. 542).

To test the hypothesis, take $a$ with a uniformizer at the unique
prime $\mathfrak p$ above $2$, $\sqrt 2$ at infinity, and $1$ at every
other place. The product norm ((A.1.3.3), p. 541) gives
$|a|_F=2\cdot 2^{-1}=1$, using squared complex norm and $N\mathfrak p=2$.
Its finite valuations give the class $[\mathfrak p]$, so
$\chi([a])=-1$ even though $\chi$ is trivial at infinity and on every
finite unit group. The [checked class character](isotypic-euler-factorization-q-sqrt-minus-five.md#checked-normalized-class-character)
and [idelic pullback](isotypic-euler-factorization-q-sqrt-minus-five.md#checked-idelic-realization-and-local-factors)
supply the continuous unitary character and uniformizer value. The
norm-one test works for every nontrivial ideal-class pullback: Lift a
class with nonidentity character value by finite valuations, then
adjust the norm at any one infinite place without changing that class.
The formula for $G$ below uses the signature with one complex place
and no real places.

The [inherited rendered product and complex factor](trace-theta-density-qi.md#source-interface)
in (3.2.1.2) and (3.2.1.5), p. 123, apply with angular index $0$, the
one complex place, and the same coordinate $c_s=\chi|\cdot|_F^s$ as
Theorem 6.3.2.1(1) (§3.2.1, p. 122, and p. 304). Every finite factor
is retained since the character, not the field, is unramified there.
For the trace-self-dual Gaussian normalization, set
$G(s)=2\pi(2\pi)^{-s}\Gamma(s)$, and write $D=L_f(\cdot,\chi)$. The
product on $\Re s>1$ is $(G/2\pi)D$. This equality extends by uniqueness
of meromorphic continuation: $D=(2\pi/G)L(\cdot,\chi)$ is entire since
$1/G$ is entire, and agrees with the [Lean-identified Dirichlet product](isotypic-euler-factorization-q-sqrt-minus-five.md#checked-all-prime-grouped-identity)
by the identity theorem. Lean's finite comparison is on $\Re s>1$;
it is not an identification with the manuscript's completed continuation.

The [inherited rendered divisibility premise](isotypic-good-heights-q-sqrt-minus-five.md#rendered-source-and-scope)
of Theorem 6.3.2.1(1), (6.3.2.3), p. 304, then gives
$\Phi=L(\cdot,\chi)V=UGD$ with $V$ entire and $U=V/(2\pi)$. This holds
for every target in that printed range condition and uses neither the
$AS$ estimates nor the printed gluing proof. This is an application
of the stated proposition, not a new proof of it.

**Review evidence:** The worker and independent reviewer `ebfjDVt`
(transcript Yah `01a2044b-499f-704a-983d-2c19771e76bd`) read the
p. 123 proposition's opening, (1), and the trivial-restriction test
in (2) from readable rendered crops. The worker also inspected the
Def. 3.2.1.2 cross-reference, p. 123, the norm product and kernel on
pp. 541–542, and the $s$-coordinate displays on pp. 122 and 304.
The reviewer used p. 542 extraction for the kernel definition,
checked the witness and its generalization mathematically, and
checked the applicability of the inherited rendered product, complex
factor, and divisibility readings. Those inherited readings are
credited in their linked notes, not reread as part of this audit.

## Holomorphy and overlap

With the [verified completed product](#verified-completed-product-and-divisibility),
write $\Phi=UGD$ with $U$ and $D$ entire. Use
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
including at the finite $L$-zeros. The [local source audit below](#verified-local-image-criterion)
checks the p. 129 equation and its normalization.

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
- The [common good-height proof](isotypic-good-heights-q-sqrt-minus-five.md)
  supplies an $m=0$ polynomial reciprocal bound uniformly on
  $[-1/2,2]+iT$ at some $T$ in every sufficiently high unit interval.
  Real Euler coefficients give $D(\overline s)=\overline{D(s)}$ by
  continuation, so each such $T$ provides a pair of opposite edges.
  The proof uses the explicit Dirichlet product, not (B.6.1.35) or
  (B.6.1.45), and no bound on derivatives of $1/D$ is needed.

For each $N\ge0$, the [converse target's uniform strip bounds](isotypic-good-heights-q-sqrt-minus-five.md#numerator-decay-from-the-converse-target)
give one constant $C_N$ bounding $|s^N B(s)|$ on the two vertical edges
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
slightly wider interior strip. This uses the [rendered membership
condition](isotypic-good-heights-q-sqrt-minus-five.md#rendered-source-and-scope)
of Definition D.3.1.3, pp. 800–801, and Lemma D.3.1.2, p. 799, not a
bound uniform up to the half-plane boundary or a claim about the
sampled topology.

The [verified local image criterion](#verified-local-image-criterion)
now supplies a representative $f\in\mathcal S(\mathbb C)$ with
local transforms $(Q_+,Q_-)$, as an application of Theorem 5.4.1.1(1),
pp. 265–266. In particular, on
$\Re s>1$ the normalized inserted test has global transform
$D(s)Q_+(s)=\Phi(s)$ and hence realizes $\Phi$ by continuation.
For the literal measures the inserted multiplier is $A D(s)$ with
$A=20^{-1/2}$, so insert $A^{-1}f$ instead. The reflected leg scales
by the same constant. The possible poles at the local endpoints
encode, rather than suppress, the two local zero modes.

## Verified local image criterion

**Result (ordinary mathematics, not Lean):** Theorem 5.4.1.1(1),
pp. 265–266, supplies a single Schwartz representative for the corrected
pair. This local implication takes the pair as input and does not depend
on the completed global factor's exact normalization on p. 123.

### Printed range and its source

In the [pinned edition](../sources/masullo/README.md), (5.4.1.2), p. 265,
has source $\mathrm H_{0,\mathrm{cont}}(\omega,\mathcal S(\mathbf A_{F,S}))$
for any $\omega\in\widehat{J^1_{F,S}}$. The hypotheses are a number
field, a finite $S$ containing all archimedean places, and a continuous
homomorphic norm section $\tau$. There is no principal-class or
nontrivial-local-character condition. On p. 266 the map sends the
class of $f$ to $(Z_S(f,c),Z_S(\widehat f,\widehat c))$; its range **is**
(5.4.1.3), not just contained in it:

$$
W_{F,S,\omega}
=\{(P_+,P_-)\in AS(\mathbb C_{>0})\times AS(\mathbb C_{<1}):
P_+(s)=\rho_{S,\tau}(s)P_-(s)\text{ on }0<\Re s<1\}.
$$

By (5.2.2.4), p. 232, the source is
$\mathcal S(\mathbf A_{F,S})/\ker\Phi_{F,S,\omega}$, a quotient of
actual tests. Thus a preimage class gives one representative with
both legs, not independent choices for the two transforms. In contrast,
Proposition 5.4.1.4, (5.4.1.7)–(8), p. 267, uses $\mathcal S_{00}$ and
requires the continuation of the forward function to be entire.
That extra requirement is not in (5.4.1.3).

### Character, domain, and constants

The [class-character and unit calculation](isotypic-exhaustiveness-q-sqrt-minus-five.md#the-missing-valuations-and-the-target-character)
gives $\mathbf A_{F,S}=\mathbb C$, $\mathcal O_{F,S}^\times=\{\pm1\}$,
and induced character $\omega=1$ on $J_{F,S}^1$. Apply (3.1.2.1), p. 120, and (3.1.2.5)
and §3.1.2.1, p. 121: $J_{F,S}=\mathbb C^\times/\{\pm1\}$, its norm
is $|z|^2$, and $\tau(t)=[\sqrt t]$ is a section. The trivial-isotype
coordinate is $c_s([z])=|z|^{2s}$. By (3.1.1.4), p. 119, the dual
is $\widehat c_s([z])=|z|^{2(1-s)}$ with no conjugation of $s$. Thus
the two positive-abscissa conditions for the defining integrals of
(3.3.1.1), p. 129, are $\Re s>0$ and $\Re s<1$, respectively.

Equation (3.3.1.1) integrates over $\mathrm{GL}_1(\mathbf A_{F,S})$,
not directly over its unit quotient. Definition A.3.4.1(1)–(2), p. 561,
reduces both measures to their complex local factors here.
Definition A.3.1.2(2), p. 556, and Example A.3.1.5, p. 557, give the
self-dual $2\,dx\,dy$ for the character $z\mapsto e^{4\pi i\Re z}$.
Section 3.3.1, p. 128, uses the standard $S$-local character and the
additive Tamagawa measure for Fourier transform.
Definition A.3.2.2(1), p. 560, gives $d\mu_v=2\,dx\,dy/|z|^2$.
In particular no factor $1/2$ is inserted for the two units. Equivalently,
unfolding over the quotient uses periodization by both units, not
the test itself with quotient Haar.

With these measures the [accepted Gaussian computation](isotypic-fourier-gluing-q-sqrt-minus-five.md#gaussian-discrepancy-and-boundary-cancellation)
gives $g(z)=e^{-2\pi |z|^2}=\widehat g(z)$ with pair $(G(s),G(1-s))$.
The rendered (3.3.1.2)–(3), p. 129, compares the forward integral
with $\rho_S(c_s)$ times the dual one on $0<\Re s<1$. Evaluating there
on $g$ gives $\rho_{S,\tau}(s)=G(s)/G(1-s)$, since $G(1-s)$ is finite
and nonzero there. This fixes the direction and normalization of the
agreement without importing the finite omitted factors into $\rho_S$.

### Application and endpoint control

The [inherited rendered membership reading](isotypic-good-heights-q-sqrt-minus-five.md#rendered-source-and-scope)
of Definition D.3.1.3, pp. 800–801, and Lemma D.3.1.2, p. 799, applies
to each open half-plane: The rapid bounds are on bounded-width strips
strictly inside it. The transfer estimates above give this membership
for both $Q_+$ and $Q_-$, and the same $U(s)$ in both legs gives the
printed overlap. Thus their preimage is a class of one $f\in\mathcal S(\mathbb C)$.
For its stated purpose, the criterion applies to every pair in $W$ on
this trivial local isotype, not just Gamma pairs from a global target.
It does not say every entire $U$ meets the half-plane growth requirements.

For a general representative the circular average of $f$ at squared
radius $t$ is $f(0)+O(\sqrt t)$ near zero. With the above measure its
constant term on $0<t<1$ contributes $2\pi f(0)/s$ to $Z_S(f,c_s)$;
the remainder is holomorphic near $0$. The same argument in $1-s$
gives residue $-2\pi\widehat f(0)$ at $s=1$ for $Z_S(\widehat f,\widehat c_s)$.
In particular, for the unscaled corrected pair every representative has
$f(0)=U(0)$ and $\widehat f(0)=U(1)$. The two boundary poles may be
removable, but need not be. For $g$ the residues are $2\pi$ and $-2\pi$;
this checks that $W$ is not secretly the polar-free range. The Gaussian
is a normalization and boundary control, not a proof of sufficiency
for arbitrary targets.

**Evidence:** Direct pixel crops of the digest-matched PDF were used for
(5.4.1.2)–(3), the quotient (5.2.2.4), the polar-free contrast, and the
local character, integral, and measure equations cited above. The
independent review (Yah `01a2043e-7daa-7fe4-b2c0-157c6a6e4f2c`, agent
`uTKGWsA`) confirms the rendered full source, pair, range, and quotient,
checks the norm and measure specialization, and confirms the two
residue comparisons. The half-plane membership and overlap estimates
are inherited, not reproved by the reviewer. This checks the local
range interface and its use, not the proof of the general Second
Structure Theorem, its topological assertions, or a Lean realization.

## Formal boundary and next check

Lean proves the maximum-modulus step as
[`Masullo.norm_pow_mul_le_on_strip_of_separated_heights`](../../Proofs/Lemmas/SeparatedHeightStripBound.lean).
With $f=B$, the endpoint adds the weight $s^N$ and transfers a common
bound on the two vertical edges and arbitrarily distant horizontal
edges to the whole closed strip. Independent statement review verified
that the hypothesis is differentiability on the open strip and
continuity on its closure, not entireness. The exact accepted candidate
`da4e9339f373d04b782a4e346dfbafe993c07e34` passed `audit-local` for
`Lemmas.SeparatedHeightStripBound`: Full warnings-as-errors build,
separate kernel replay, declaration provenance, and axiom check. A
separate `#check` confirmed the endpoint type. The only axioms are
`propext`, `Classical.choice`, and `Quot.sound`; the changed Lean source
has no placeholders or unsafe substitutes.

The [finite Euler factorization](isotypic-euler-factorization-q-sqrt-minus-five.md#checked-all-prime-grouped-identity)
now identifies $D=L(\cdot,\chi_{-4})L(\cdot,\chi_5)$ in Lean with
the actual finite Hecke product of the constructed class character
on $\Re s>1$. The unconditional identification on that half-plane
uses all grouped local factors, including those at $2$ and $5$.

The [horizontal reciprocal estimate](isotypic-good-heights-q-sqrt-minus-five.md)
is now unconditional in Lean for the explicit denominator $D$. Five
centered periodic primitives give $|D(z)|\le C_0 H^{12}$ on the
radius-six circle about $2+i(H+1/2)$ for every real $H\ge1$. This
supplies the $m=0$ good-height estimate. The separate
[all-orders Cauchy estimate](isotypic-good-heights-q-sqrt-minus-five.md#all-orders-cauchy-bound-at-the-same-height)
now bounds reciprocal derivatives in Lean at the same height and all
centers of the closed segment. The completed-source application, the
reflected insertion identity, and the archimedean image criterion
are ordinary mathematics, not Lean realization.

**Separate source check completed:** The [in-scope gluing control](isotypic-fourier-gluing-q-sqrt-minus-five.md#in-scope-control-and-scope-of-the-repair)
shows that the literal pair fails in the overlap at the principalizing
stage $S_\infty\cup\{\mathfrak p_2\}$, because it omits the Fourier
factor at $\mathfrak p_5$. The smaller stage is an extension outside
the printed stage conditions. This audit neither verifies the general
converse nor supplies a Lean realization of the repaired case.

### Checked forward closed-strip estimate

[`Masullo.qSqrtNegFiveForwardB_closed_strip`](../../Proofs/Theorems/NegFiveForwardStrip.lean)
uses the explicit Dirichlet product $D$ and the product $H_D$ of the two
`completedLFunction`s. In mathlib's normalization the forward regularization
is $B(s)=2\pi U(s)\Gamma_{\mathbb C}(s+1)$. The [regularization lemmas](../../Proofs/Lemmas/NegFiveForwardRegularization.lean)
prove that $B$ is holomorphic on $\Re s>-1$ for entire $U$, and equals
$s\Phi(s)/D(s)$ wherever $D(s)\ne0$, with $\Phi=U H_D$. The proof uses
$D=H_D/\Gamma_{\mathbb C}$ before cancelling any factor.

The sole decay hypothesis is that $(1+\|s\|)^m\,\|\Phi(s)\|$ is bounded
on the closed strip for each natural $m$. Exact norm reflection and the
right anchors give nonvanishing on the vertical edges. Real coefficients
of $D$, not any symmetry of $U$, give the lower good-height edge. For a
fixed $N$, the seminorm at $m=N+1+\lceil A\rceil$ absorbs the reciprocal
loss on all four edges. Maximum modulus applies to $s^N B(s)$ itself,
so the bound includes both endpoints and every interior zero of $D$.
This proves the forward estimate under the stated numerator hypothesis,
not its derivation from a manuscript test space, realization, or reflected
gluing.
