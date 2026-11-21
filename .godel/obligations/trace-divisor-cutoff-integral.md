# Integrating the two-scale cutoff majorant

**Status: Lean endpoint `Masullo.weightedCutoffIntegrals_le` in
[`Lemmas.CutoffMajorant`](../../Proofs/Lemmas/CutoffMajorant.lean).** This is the integration half of the
[Chapter 13 cutoff repair](trace-divisor-cutoff.md#uniform-weighted-bounds-for-the-cutoff-family).
The pointwise estimate in that handoff is an input here. No manuscript claim
or equality of the full and capped distributions is used.

The moving layer $[1/N,2/N]$ lies in the domain of integration for $N>0$.
Its Lebesgue mass is $1/N$, so the factor $N$ drops out exactly. The other
majorant term uses the exponential integral. The conclusion is a bound on
the sum of the two weighted integrals, matching the right-hand side of
[`norm_positiveLaplaceTest_mul_weight_le`](trace-divisor-compact-test.md).
Neither a common pointwise envelope for the differentiated family nor
nonnegativity of the two coefficients is needed for this integration step.

The independent [statement review](trace-divisor-cutoff-pointwise.md#checked-interface)
confirmed that the continuity and compact-support assumptions suffice for
integrability and that the two left-hand integrals match the exact
`CompactTestLaplace` endpoint. It did not infer smooth test admissibility
from these weaker hypotheses. Local elaboration required unfolding the
restricted measure and indicator explicitly and simplifying the sign in
the exponential integral. The reviewed type was unchanged.

In the family application, take $N=n+2$ and use the *same* $C_0,C_1,\delta$
for all $n$. Both weighted integrals are nonnegative, so the sum bound also
bounds each individually. Apply the compact-test estimate and divide by
$1+|w_i|^2$ before multiplying by $|d_i|$. This gives a uniform bound for
all pairs $(n,i)$, not a moving majorant for the spectral sum. The scalar
integral limits and zero-mean correction are separate steps.
