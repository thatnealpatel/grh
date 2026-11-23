# The Néron-model examples announced in §1.7.3

**Printed passage.** Masullo, *The Music of the Primes*, §1.7.3,
printed p. 37, claim in the first bullet from “Using the theory of
Néron models” through “strictly exceeding [F:ℚ].” Masullo says one
can construct algebraic Hecke characters χ₀ over number fields F
with an infinitely repeated finite Euler pole, and that in such
examples the central zero of `L(s, χ₀|·|_F^(-w/2))`, where w is the
weight of χ₀, has order strictly greater than `[F:ℚ]`. The force of
“in such examples” is that a single example must meet both tests.
The sentence names a construction method but does not give a curve,
a set of places, an order computation, or an explicit hypothesis.
Coverage stops before the second bullet.

Chapter Markdown and PDF layout extraction located the passage and
the Chapter 14 comparison. Raster OCR checked the prose on p. 37
and pp. 531–532. Direct inspection of rendered pixel crops from the
[digest-verified PDF][source] checked the negative `−w/2` twist and
strict degree bound on p. 37, and the direction of (14.1.2.4) on
p. 531. The details of the Chapter 14 proof below follow the
extraction, cross-checked against raster OCR.

**What the later example supplies.** Proposition 14.1.2.5, printed
pp. 531–532, treats a Mordell curve over ℚ with CM after base change
to `F = ℚ(√−3)`. Its high central order is conditional on
`rk E_d(F) ≤ ord_(s=1) L(E_F/F,s)` for the chosen curve, not on the
algebraic rank alone. Remark 14.1.2.6, p. 532, explicitly notes
this proviso. Masullo uses the cited rank-12 example and Deuring
factorization (14.1.2.7) to get a sum of orders at least 12 under
that premise. At least one of the two normalized Hecke factors
then has order greater than 2 at `s = 1/2`; the shift from the
curve variable `s = 1` and the regular, nonzero gamma factors
preserve the orders. In this proof the twist is written
`χ = |·|_F^(1/2) ψ`; identifying ψ with the χ₀ of p. 37 requires
keeping track of the weight convention. This argument supplies a
conditional high-order comparison, not the repeated-pole assertion.

**Local check of the Chapter 14 route.** At an unramified place v,
a pole at a fixed s requires `χ_v(π_v) = exp(s log q_v)`, where
`q_v` is the residue size and `π_v` is a uniformizer. A real norm
twist changes the coordinate but not whether one point meets this
condition at infinitely many places. For the unitary factor χ of
(14.1.2.7), its real normalizing twist and Masullo's three-place
argument leave only `s = 0` as a candidate; see the
[finite-pole audit][poles]. Uniqueness of a possible point does not
imply existence.

The reviewer checked this candidate using the good-place factors
of the cited Deuring factorization. At a good split rational prime
p the unnormalized eigenvalues are roots of `T² − a_p T + p`
with `a_p ∈ ℤ`. Neither can equal `√p`, which would give
`a_p = 2√p`. At a good inert p away from 2 and 3, one has
`p ≡ 2 (mod 3)`; cubing permutes the residue field of size p, so
counting solutions of `Y² = X³+d` gives `a_p = 0`. Both eigenvalues
square to `−p` over the residue degree-two field. Dividing by
`√q_v = p` gives `−1`, not `1`. These checks apply to either CM
factor at all but finitely many places. Thus this particular
Chapter 14 construction does not supply the repeated pole, even
if its rank-to-order premise holds. The local calculation is the
reviewer's, not an argument printed on p. 37. It does not exclude
other constructions.

**Formal disposition: Open.** What is missing is a specified
algebraic character or curve for which the same normalized
character has the pole equation at one fixed parameter at
infinitely many finite places and has analytic central order
strictly greater than the field degree. In particular, provide a
central order computation or justify the needed rank-to-order
premise and transfer for that very example. No Lean statement for
the joint existence claim was identified. At accepted revision
`3dd6a52b23e3554d27ef1c6b563365f27451f477`,
`Masullo.finiteHecke_localPolynomial_eval_uniformizer` in
`Proofs/Theorems/FiniteHeckeCharacterEulerProduct.lean` computes
the pointwise denominator for an unramified restriction at a
chosen uniformizer. It does not identify meromorphic poles,
relate the values to CM Frobenius, or bound the order of a global
zero. Neither the printed joint claim nor the trace obstruction
is formally established or refuted here.

[source]: ../sources/masullo/README.md
[poles]: finite-local-polar-multiplicities.md
