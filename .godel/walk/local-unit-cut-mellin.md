# The unit cut and the local Euler factor

**Printed passage.** Masullo, *The Music of the Primes*, §1.3.2,
printed p. 25, from “Under the local Mellin transform” through the
sentence on the reciprocal local Euler factor. Write $U=\mathcal
O_{F_v}^{\times}$, $O=\mathcal O_{F_v}$, $c=\chi_v|\cdot|_v^s$, and
$m=\mu_v(U)$. The unnumbered display called “Weil’s Identity” is
$m Z_v(1_U,c)=L_v(c)^{-1}Z_v(1_O,c)$ on the local character component.
The next sentence says “reciprocal local Euler factor” but prints
$L_v(c)$ without an inverse. The paragraph before this use has in view
the tensor factors at $v\notin S$, but the displayed equality does
not explicitly qualify the place. The following remark on the
product of masses is a separate passage.

Chapter Markdown and PDF layout extraction supplied the reading.
Inspection of pixel crops rendered from the digest-verified [pinned
PDF][source] checked the mass multiplier and inverse exponent in the
p. 25 display, the absence of that exponent in the sentence, the raw
integral against $\mu_v$ in (3.3.1.7), p. 130, and the discriminant
mass in (A.3.2.2), p. 560. The inverse in (3.2.1.2), printed p. 123,
confirms the Euler convention $(1-\chi_v(\pi_v)q_v^{-s})^{-1}$ used
with (3.2.1.1), printed p. 122.

**Checked scope.** For an unramified character, $c$ is one on $U$.
In the half-plane $|c(\pi_v)|<1$, the reviewer’s calculation gives

$$
Z_v(1_U,c)=m,\qquad
Z_v(1_O,c)=\sum_{n\geq 0}m\,c(\pi_v)^n=m L_v(c).
$$

Each shell $\pi_v^n U$ has mass $m$ by multiplicative invariance,
and these shells partition $O\setminus\{0\}$. The geometric sum
gives the meromorphic continuation, so the inverse Euler factor
alone effects the replacement. The extra multiplier on the left
makes the printed scalar equality require $m^2=m$. At the intended
places outside the stated $S$, both the field and character are
unramified, so the discriminant unit mass is one and the **display**
is valid there; in the explanatory sentence the reciprocal is
$L_v(c)^{-1}$, not $L_v(c)$. This is a local computation, not a proof
of fixed-$S$ theta representability or any global kernel identity.

**Counterexample to the unrestricted display.** Take $F=\mathbb Q(i)$,
the place over $2$, the trivial character, and $s=2$. The accepted
[finite Gaussian normalization audit][gaussian] computes the local
integer basis $(1,i)$, trace discriminant $-4$, and residue size
$2$. Thus (A.3.2.2) gives $m=1/2$, and the shell sum gives $Z_v(1_O,c)
=2/3$ and $L_v(c)=4/3$. The two sides on p. 25 are $1/4$ and $1/2$,
respectively. This place is intentionally not a counterexample to
the outside-$S$ application.

**Formal comparison.** At accepted revision
`71dbf2ff4f4f9c1b5344e894e5ebd964988da666`,
[`Masullo.finiteHeckeLocalZeta_unramified`][lean] proves integrability
and the raw integer-ring value $mL_v$ for a unitary Hecke character
unramified at $v$, $\operatorname{Re}s>0$, and a multiplicatively
left-invariant Borel measure with finite unit mass. It neither states
the two-test meromorphic identity nor evaluates the discriminant mass
at the witness. The nearby ramified endpoint uses an inverse-character
test on the units, not the plain indicator paired with a ramified
character. The shell comparison and numerical counterexample above
are ordinary mathematics; no new Lean endpoint is claimed.

**Independent review.** Fresh Yah reviewer `WXgZHtJ` (output
`4cbdcc55b2323dd0fcdc3b76f23c3e5773d5800d`) read the pinned
source and the exact accepted Lean signature at the revision above.
The reviewer used layout extraction and raster OCR, recovered the
same discrepancy at $s=1$ (the sides are again $1/4$ and $1/2$),
and confirmed the outside-$S$ reading and the limits of the Lean
statement. No fresh Lean build or axiom audit is claimed.

[source]: ../sources/masullo/README.md
[gaussian]: ../obligations/finite-gaussian-tamagawa.md
[lean]: ../../Proofs/Theorems/FiniteHeckeLocalZeta.lean
