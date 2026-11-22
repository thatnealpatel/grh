# Both printed Weil factorizations depend on the admissible set

**Verdict.** In Theorem 3.4.1.1, (3.4.1.5)–(6), p. 143, take
$F=\mathbb Q(i)$, $\chi=1$, $s=2$, and the weight-zero standard Gaussian.
If $v$ is the place over $2$, each printed right-hand side at
$S=S_\infty\cup\{v\}$ is **half** its nonzero value at $S=S_\infty$.
Both sets satisfy the printed hypotheses, and neither left-hand side
has an $S$ argument. Neither formula can therefore hold for all
admissible $S$ as printed, independently of the global Haar calibration.
This does not rule out a corrected factorization.

## Source and admissibility

The [pinned PDF](../sources/masullo/README.md) was checked by digest.
Chapter 3, Chapter 5, and Appendix A Markdown were read first, and
numbered layout extracts located the passages. Rendered page crops
were inspected directly, including the signs and subscripts on
pp. 143–144. Independent rendered review: `AkciZWc`, read-only output
`25fe34f584aadecba729f1c35bca4d49899a26db`. No provisional manuscript
reading is needed for this verdict.

- Theorem 3.4.1.1, p. 143, requires a Schwartz-Bruhat tensor with
  $f_w=1_{K_w}$ for compact open $K_w$ at each finite $w$, and allows
  **any** finite $S$ containing $S_0=S_\infty\cup S_\chi$ outside which
  $f_w=1_{\mathcal O_{F_w}}$. The fixed character is $\chi$, and $S_\chi$
  concerns character ramification, not ramification over $\mathbb Q$
  (Notation 3.4.1.1, p. 142, and the definition after (3.1.2.6), p. 121).
  In particular, taking $\chi=1$ forces $S_\chi=\varnothing$, not a set
  containing $v$. The
  [accepted finite normalization audit](finite-gaussian-tamagawa.md)
  verified the product and descent of the idelic norm in (A.1.3.3),
  p. 541, and (A.1.3.6), p. 542, and the norm on local units in
  §3.1.2.1, p. 120. Thus $c=|\cdot|_F^2$ is a global quasi-character
  with unit-trivial restrictions, and $s=2$ is even in the initial
  half-plane $\Re s>1$ used in the proof on p. 144.
- Equations (3.4.3.5), (3.4.3.7), and (3.4.3.9), p. 152, give the
  weight-zero tensor with $f_\infty(z)=(2\pi)^{-1}e^{-2\pi|z|^2}$
  at the unique complex place and $f_w=1_{\mathcal O_{F_w}}$ at **every**
  finite place. Consequently $S_0=S_\infty$ for either choice of $S$,
  and the descended character $\chi_{S_0}$ is trivial. The “containing”
  hypothesis permits equality: The proof of Proposition 3.4.2.1,
  p. 145, invokes (3.4.1.6) with the union of the Archimedean,
  character-ramified, and test-exceptional sets, without adding a place.
- The cross-reference to Definition 5.1.1.1(2), p. 223, identifies
  $Z_{S_0}$ on this half-plane with (3.3.1.1), p. 129, the integral
  against $\mu_{S_0}$. Equation (A.3.4.2), p. 561, makes this the
  product over $S_0$ only. Thus both choices use the same positive
  finite number $A=Z_{S_\infty}(f_\infty,|\cdot|_{F,S_\infty}^2)$.
  The Gaussian and twist are positive on $\mathbb C^\times$; with the
  local Tamagawa measure in Definition A.3.2.2(1), p. 560, and the
  squared complex norm in §3.1.2.1, p. 121, the twist leaves a factor
  $|z|^2$ against the additive measure, integrable near zero and against
  Gaussian decay at infinity.
- The subscript in (3.4.1.6), p. 143, is $\Sigma_F-S_0$, **not**
  $\Sigma_F-S$. The displayed definition immediately below multiplies
  $L_f$ by a product over $S_\chi$, which is empty here. By (3.2.1.7),
  p. 124, the multiplier at $s=2$ is therefore the same
  $B=L_f(2,1)=\prod_{w\,\mathrm{finite}}(1-q_w^{-2})^{-1}$ for both
  choices, still including the Euler factor $4/3$ at $v$.
  Definition 3.2.1.4, pp. 123–124, gives absolute convergence at $2$.
  The limit is positive because the partial products are at least one.

## The one-shell check

The shift in (3.4.1.3), p. 143, is $g\mapsto\pi_v^{-1}g$. The
indicator difference is $1_{\mathcal O_{F_v}}-1_{\pi_v\mathcal O_{F_v}}
=1_{\mathcal O_{F_v}^\times}$. The proof on p. 144 explicitly integrates
this shell and retains its Tamagawa mass (the inverse square root of
the different norm), rather than replacing it with one. Here $c_v$ is
one on the shell. With the arithmetic of the
[accepted local check](finite-gaussian-tamagawa.md#exact-local-calculation)
($F_v=\mathbb Q_2(i)$, $\pi_v=1+i$, $q_v=2$, discriminant $-4$),
(A.3.2.2), p. 560, gives

$$
\widetilde Z_v(1_{\mathcal O_{F_v}},|\cdot|_v^2)
=\mu_v(\mathcal O_{F_v}^\times)=\tfrac12.
$$

This is the shell mass, not the raw pairing $2/3$ or the Euler value
$4/3$ from the earlier audit. The finite product over $S-S_0$ is empty
for $S_\infty$ and is this one shell for $S_\infty\cup\{v\}$:

| Display, p. 143 | RHS at $S_\infty$ | RHS at $S_\infty\cup\{v\}$ |
|---|---:|---:|
| (3.4.1.5) | $A$ | $A/2$ |
| (3.4.1.6) | $AB$ | $AB/2$ |

The first left-hand side is the all-place product of (3.4.1.1),
p. 143. The second, by Definition 5.1.1.1(1), p. 223, comes from the
global integral in (3.2.2.1), p. 124. Both are independent of $S$; the
comparison does not require their values. No continuation, global
product identification, or trace regularization is used.

## Reusable scope and remaining premises

For any two nested admissible sets $S\subset S'$ at a regular parameter,
each new place $w\in S'-S$ has the standard indicator and unit-trivial
local twist. The same shell inserts $M_w=\mu_w(\mathcal O_{F_w}^\times)$.
Each right-hand side is multiplied by $\prod_{w\in S'-S}M_w$ wherever
finite; this gives a ratio when the original value is nonzero. In
particular, simply adding places of unit mass does not exhibit the defect.
An explicit omitted-mass factor $\prod_{w\notin S}M_w$ would cancel
this dependence (all but finitely many $M_w$ are one). That is a
normalization repair for set independence, not a proof that the second
repaired expression equals the globally normalized integral.

This is a rendered-source verdict and ordinary mathematics. The
[accepted Lean pairing](../../Proofs/Theorems/FiniteHeckeLocalZeta.lean),
`Masullo.finiteHeckeLocalZeta_unramified`, gives integrability and the
mass-weighted Euler pairing for unitary Hecke characters unramified at
$v$, $\Re s>0$, and a left-invariant Borel measure with finite unit
mass. It proves neither printed global identity and was not changed.
General-field stage Haar calibration, raw Gaussian versus completed
Euler product identification, conductor assembly, reflected-line
integrability, and contour exhaustion remain separate.

**Next bounded source check (mapped):** Use (A.3.2.5), p. 560, on the
same Gaussian and $s=2$ to evaluate the left side of (3.4.1.6) by
increasing stages containing $v\mid 2$. Check whether the stage
calibration gives $AB/2$, identifying which RHS matches the global
integral for this witness without requiring general-field Lean Haar.

The real-place primed integral in (13.3.1.4), p. 522, is a separate
mapped [source gate](trace-divisor-uniqueness.md#a-pole-test-for-the-raw-haar-reading).
Neither its normalization, the common finite-place indexing, nor the
capped trace comparison is decided here.
