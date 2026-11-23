# Pointwise pole-order growth along finite Euler products

**Printed passage.** Masullo, *The Music of the Primes*, §1.7.3,
printed p. 37, claim in the first bullet from “Then Theorem 1.8.2.2
alerts us” through “parametrized as χ|·|_F^s.” For the continuous
unitary Hecke character χ of a number field F fixed above, Masullo
says that as S exhausts all places, the pole orders of the finite
Euler products become unbounded at at most one point on the
quasicharacter component. No algebraicity or finite-order hypothesis
is printed for χ in this sentence. The next sentence, about examples
from Néron models, is not covered here.

Chapter Markdown and PDF layout extraction located the passage.
Raster OCR of the [digest-verified PDF][source] checked the prose;
direct inspection of rendered crops confirmed the printed citation
and the language of unbounded growth on p. 37 and the corresponding
heading on p. 43. The literal citation is not a polar-multiplicity
theorem: §1.8.2.2 introduces S-local and global θ-functions. The
preceding citation to Theorem 1.7.1.1 (p. 35) and the polar-multiplicity
Theorem 7.1.3.2 (pp. 324–325) are relevant, but changing the citation
does not repair the scope. The latter proof is used through the
[accepted finite-pole audit][poles].

**Meaning of growth at a point.** Fix a parameter s before allowing S
to grow. At an unramified finite place the local Euler factor is the
meromorphic reciprocal of `1 − χ_v(π_v) exp(−s log q_v)`, whose
zeros are simple, since the derivative at each zero is `log q_v`.
The reciprocal has simple poles and no zeros. Ramified factors are
one. The Archimedean local gamma factors have no zeros and their
combined contribution at any fixed point is bounded independently of
S, because there are finitely many of them. Thus the pole order at s
is unbounded along the exhaustion exactly when s is a pole at
infinitely many finite places. Since each prime fiber has at most
`[F:ℚ]` places, this is equivalent to occurrence above infinitely
many distinct rational primes. A maximum whose maximizing point
varies with S is not this pointwise assertion.

**Checked scope and missing step.** For a unitary χ obtained from an
algebraic character by a norm twist of exponent s₀, Masullo's
three-finite-place argument in Theorem 7.1.3.2(3.b) gives the
pointwise conclusion without Schanuel: Off `s = −i Im(s₀)`, three
finite poles at distinct residue characteristics would contradict
the Six Exponentials Theorem. For finite-order χ, Masullo's
root-of-unity argument in (3.a) already rules out a pole at two
distinct residue characteristics off `s = 0`. Both uses concern
finite local factors, not the global Hecke zeros. The translation
from these finite-place conclusions to pointwise unboundedness is
the reviewer's use of additivity of pole orders and the prime-fiber
bound.

For general continuous unitary χ, part (1) constrains the number of
common poles of each pair at distinct residue characteristics. It
does not prohibit two distinct points each occurring at infinitely
many places over disjoint sets of rational primes. Its exceptional
point count in a finite stage also grows with the stage. The missing
step is to use global restrictions on the local values of a general
χ to rule out two distinct solutions each supported over infinitely
many rational primes. No such argument is given here. The algebraic
and finite-order cases are not proofs of the unrestricted statement.

**Formal disposition: Open.** At the inspected accepted revision
`08fd2e8f3d0e183df048b670f49d5da031ab3675`, the Lean declarations
`Masullo.finiteHecke_localPolynomial_eval_uniformizer` and
`Masullo.finiteHeckeEulerFactor_eq_one_of_ramified` in
`Proofs/Theorems/FiniteHeckeCharacterEulerProduct.lean` give the
pointwise denominator at an unramified place with a chosen
uniformizer, and the pointwise unit factor at a ramified place,
respectively. They do not compute meromorphic pole orders, track
unboundedness in an exhaustion, or establish uniqueness of the
point of growth. The pointwise inverse is totalized at zero. No
formal establishment or refutation, trace obstruction, or zero
multiplicity bound follows from this review.

[source]: ../sources/masullo/README.md
[poles]: finite-local-polar-multiplicities.md
