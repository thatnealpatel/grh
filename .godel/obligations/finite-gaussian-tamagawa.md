# The finite Gaussian retains the Tamagawa unit mass

**Verdict.** Theorem 3.4.3.3(1) forces its local scalar to be the raw
Gaussian pairing. It cannot be the Euler factor of (3.2.1.1)–(2),
pp. 122–123, at the place over 2 of $F=\mathbb Q(i)$ with
$c_v=|\cdot|_v^2$: The pairing is $2/3$, and the Euler factor is $4/3$.
The Gaussian definition on p. 152 permits a mass-weighted local
factor instead. This is an incompatibility with the earlier Euler
convention, not a refutation of the scalar identity with Gaussian
factors or of the existence of a correctly normalized distribution.

## Source and the two readings of $L_v$

The [pinned edition](../sources/masullo/README.md) was checked by digest.
Chapter 3 and Appendix A Markdown were read, then numbered PDF layout
used to locate the passages. The decisive rendered page crops were
inspected directly (Poppler grayscale pixels rendered in braille).
Independent rendered and arithmetic review: `ayiooyS`, read-only
output `8ba3aac6dbaf9e0625cdc816472703d3936d7815`. No provisional
manuscript reading is needed for the local mismatch.

- Theorem 3.4.3.3(1), pp. 152–153, uses local multiplicative Tamagawa
  measure, quantifies over $c\in\Omega(F_v^\times)$, and treats an
  unramified **quasi-character** at a finite place in (3.4.3.10). The
  test $E_v$ in (3.4.3.7), p. 152, is $1_{\mathcal O_{F_v}}$ with no
  prefactor. Theorem 3.4.3.3(1) gives $\langle\Delta_v'(c),E_v\rangle=1$,
  and (3.4.3.13) gives $Z_v(\cdot,c)=L_v(c)\Delta_v'(c)$ with $L_v$ the
  local factor of the completed Hecke $L$-function. Thus at a regular
  point these equations force $Z_v(E_v,c)=L_v(c)$, regardless of how the
  eigendistribution is constructed.
- Section 3.1.1, p. 118, defines quasi-characters as continuous
  homomorphisms into $\mathbb C^\times$. In §3.1.2.1, p. 120,
  $\mathcal O_{F_v}^\times$ is the kernel of the normalized norm, and
  $|\pi_v|_v=q_v^{-1}$. Lemma A.3.2.3, p. 560, identifies $q_v$ as the
  residue size. The definition following (3.1.2.6), p. 121, specifies
  unramified by triviality on the local integer units. In particular the
  witness is unramified even though the field extension is ramified.
  It also comes from the global squared idelic norm, using the local
  restriction in §3.1.2, p. 120, the normalized product (A.1.3.3), p. 541,
  and descent (A.1.3.6), p. 542. The latter two rendered readings are
  from the independent review. The trivial unitary character and
  $s=2$ in §3.2.1, p. 122, put it on the right of both convergence
  thresholds.
- Equation (3.3.1.7), p. 130, is the bilinear integral of $f_v(g)c_v(g)$
  on $F_v^\times$ against $\mu_v$, explicitly the multiplicative local
  Tamagawa measure of Definition A.3.2.2. Its finite unit mass
  (A.3.2.2), p. 560, is $M_v=|\operatorname{disc}(\mathcal O_{F_v}/
  \mathbb Z_p)|_p^{1/2}$. As a cross-check, the proof of Theorem 3.4.1.1,
  p. 144, takes the difference of the integer-ring and uniformizer-ball
  indicators and retains $N(\mathfrak d_{F_v/\mathbb Q_p})^{-1/2}$ on
  the units.
- Equations (3.2.1.1)–(2), pp. 122–123, give the unramified finite Euler
  factor $(1-c_v(\pi_v))^{-1}$, with places excluded by character
  ramification, not field ramification. Definition 3.2.1.2, p. 123,
  defines the Hecke $L$-function by that product with its Gamma factors.
  The prose following (3.3.1.25), p. 135, explicitly calls $L_v(c_v)$
  its local Euler factor.
- Section 3.4.3, p. 151, introduces the completed $L$-function in
  contrast to a finite partial Euler product. The paragraph after
  (3.4.3.9), p. 152, defines the completed $L(c)$ by $Z(E_\chi,s)$.
  The following theorem calls its $L_v$ a local factor of that completion,
  without explicitly giving an Euler denominator there. If the local
  factors are the raw local pairings in a product decomposition, the
  finite factor is $M_v(1-c_v(\pi_v))^{-1}$. This is consistent with the
  two *scalar* equations at the test, but it is not the Euler-factor
  convention. A definition of a global integral alone does not identify
  its individual factors. No global product decomposition is assumed
  in the local verdict.

## Exact local calculation

Put $\pi=1+i$. Its minimal polynomial $X^2-2X+2$ is Eisenstein at 2,
so $\mathbb Q_2\otimes_{\mathbb Q}F$ is the single quadratic completion
$K=\mathbb Q_2(i)$. In the extension $w$ of the additive valuation with
$w(2)=1$, $w(\pi)=1/2$ by $\pi^2=2i$ and $w(i)=0$. The two terms in
$a+b\pi$ for $a,b\in\mathbb Q_2$ have distinct valuations when both are
nonzero. Hence $w(a+b\pi)=\min(v_2(a),v_2(b)+1/2)$, with the same rule
at a zero term. This is nonnegative exactly for $a,b\in\mathbb Z_2$,
proving $\mathcal O_K=\mathbb Z_2[\pi]=\mathbb Z_2[i]$ and that $\pi$
is a uniformizer. Reduction maps $a+b\pi$ to $a\bmod 2$, so $q_v=2$.
The trace matrix on the integral basis $(1,i)$ is $\operatorname{diag}(2,-2)$,
with determinant $-4$. The discriminant exponent over $\mathbb Z_2$
is 2 and the Tamagawa unit mass is $|-4|_2^{1/2}=1/2$.

The punctured integer ring consists of the disjoint shells
$\pi^n\mathcal O_K^\times$ for $n\geq0$. Each has mass $1/2$ by
multiplicative invariance, and $c_v$ there is $2^{-2n}$. Thus

$$
Z_v(1_{\mathcal O_K},c_v)=\frac12\sum_{n\ge0}4^{-n}=\frac23,
\qquad L_v^{\mathrm{Euler}}(c_v)=(1-2^{-2})^{-1}=\frac43.
$$

The integral converges absolutely. Over $\mathbb Q_2$ the control has
the same residue size and ratio, with uniformizer $2$ and discriminant
$1$. Its unit mass is one and its pairing is $4/3$, matching the Euler
factor. No continuation or boundary value is involved in either check.

## Scope, repair, and next check

For any finite place and any continuous character trivial on the integer
units with $|c_v(\pi_v)|<1$, the same shell calculation (ordinary
mathematics) gives $M_v(1-c_v(\pi_v))^{-1}$. In particular, it covers
all unitary unramified twists with $\operatorname{Re}s>0$, not just the
norm-square test. To keep the standard Euler factor, use $M_v^{-1}E_v$
for the calibration, or put $M_v$ explicitly in (3.4.3.13) if the test
stays fixed. Unit-mass Haar would also give the Euler value, but is not
the printed measure at the ramified place. These scalar repairs do not
repair the separate angular or eigendistribution action conventions.

The [accepted Lean pairing](../../Proofs/Theorems/FiniteHeckeLocalZeta.lean),
`Masullo.finiteHeckeLocalZeta_unramified`, proves absolute integrability
and the mass-weighted Euler value for a unitary Mathlib Hecke character
unramified at $v$, $\operatorname{Re}s>0$, and a left-invariant Borel
measure with finite unit mass. The prior statement review is recorded
in the [branch note](hecke-right-line-majorant.md#finite-local-zeta-pairings-with-the-haar-unit-mass-retained).
The explicit arithmetic, numerical pairing, and rendered-source verdict
here are not new Lean endpoints.

**Checked follow-up:** The [two-set audit](weil-admissible-set.md)
uses the same place in the weight-zero global Gaussian at $s=2$.
Adjoining $v$ to $S_\infty$ halves both printed right-hand sides of
(3.4.1.5)–(6), p. 143, while their left-hand sides are fixed. This
uses the unit-shell mass, not the raw local zeta value, and does not
identify the globally normalized integral.

Separate open premises: General-field finite-stage Haar, the comparison
of the raw Gaussian and completed Euler products, the local conductor
and its global assembly, reflected-line integrability, and contour
exhaustion. The real-Haar reading in (13.3.1.4), p. 522, is separate.
