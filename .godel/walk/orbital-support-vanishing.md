# Finite-place orbital support vanishing is conditional

**Printed passage.** Masullo, *The Music of the Primes*, §1.2.9,
printed p. 19, claim beginning “and so if” immediately below the
Poisson trace display. Masullo says that if the test is supported
strictly over $C_F^{(1,|\pi_v^{-1}|_v)}$, then the displayed trace is
zero. The rendered sentence, including the upper endpoint with its
place index, was inspected in a raster crop of PDF page 19, separately
from the chapter Markdown and PDF layout extraction. The
[edition](../sources/masullo/README.md) was verified against SHA-256
`e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5`.
This finding ends at that sentence, before the assertion about all
but finitely many places.

**Scalar check and scope.** Since $|\pi_v^k|_F=q_v^{-k}$, no sample in
the $v$-comb lies over $(1,q_v)$. The preceding display sums over
*all* $v\in S_p$, but the support sentence gives a $v$-indexed bound
without an explicit quantifier. It kills the individual $v$-term;
for the full $p$-primary sum a sufficient reading is that the bound
holds for every $v\in S_p$, equivalently that the norm support is in
$(1,\min_{v\in S_p}q_v)$. A bound for just one place with larger
$q_v$ does not suffice: If $q_w<q_v$ for another place above $p$,
a nonnegative radial bump at norm $q_w$, supported inside $(1,q_v)$,
gives a positive $w$-contribution for the trivial character.

The fixed-character point-sample identity is not needed. With the
norm Haar disintegration, each unramified Euler zero lattice in the
p. 18 Mellin sum gives a Poisson comb of character-weighted integrals
on the norm fibres $q_v^{\mathbf Z}$, not evaluations at individual
ideles. Ramified places have no lattice in that Euler sum. The
support condition makes the relevant **whole fibres** disjoint from
the support, so the corrected scalar sum also vanishes. The accepted
[rational angular audit](../obligations/trace-orbital-q.md#angular-poisson-summation-at-one-prime)
at `cbbdc8500375e7bf3e41cd6b877e1eae3135a0da` gives a one-place
instance of this fibre calculation. Masullo uses the preceding
point-sample display; the simultaneous support condition and use of
the fibre calculation instead are the reviewer's analysis.

**Open operator step.** To conclude vanishing for the printed
operator, establish that convolution on the intrinsic global
two-zero-moment $p$-primary theta quotient by the actual introductory
principal-value range is nuclear and has the multiplicity-weighted
Mellin trace asserted on p. 18. The
[accepted trace audit](global-orbital-mellin-trace.md) at
`b272fc6bbf7b9465a93f89c4aba168762e5c532b` distinguishes that
operator from the later unit-averaged product and identifies the
missing nuclear expansion. Vanishing of a scalar candidate does not
establish the trace formula or a zero geometric shell, and does not
assert that the operator itself vanishes. No Lean declaration is
used to establish or refute this passage.
