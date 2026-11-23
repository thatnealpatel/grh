# The a posteriori trace formula on unrestricted tests

**Status: Open.** Masullo, *The Music of the Primes*, printed p. 30,
§1.4.6, claim in the paragraph beginning “The condition” and ending
“Explicit Formulas.” Masullo says that the norm-one vanishing condition
cannot be removed before GRH, but that the Trace Formula holds for every
Bruhat test once the zero information deduced from the restricted trace
is incorporated into Weil's Explicit Formulas. This is distinct from
[the preceding extension to tests vanishing on the fibre](norm-one-trace-extension.md).
Coverage stops before §1.4.7.

Chapter Markdown and PDF layout extraction located the paragraph in the
[digest-verified edition](../sources/masullo/README.md). Raster OCR
checked the prose. Direct inspection of rendered crops checked both
occurrences of $\varphi(C_F^1)=0$, “any test function,” “a posteriori,”
and the closing “Explicit Formulas.”

**What zero location could give.** For a strip of positive half-width
centered at $1/2$, putting every nontrivial zero on the critical line
would make the full-order interior zero sum of Theorem 12.5.1.1,
pp. 519–520, coincide with the full zero sum in the same character
components. This uses the [trace assembly audit](../obligations/trace-assembly.json)
for the strip and weights, and the [zero-location audit](logarithmic-derivative-to-zeros.md)
for the still-open premise. It is a change in spectral indexing, not
an extension by continuity from tests vanishing on the fibre.

**Scalar identity versus operator trace.** As read provisionally from
extraction, Theorem B.4.4.7, p. 623, (B.4.4.16), already states an
all-test scalar idelic explicit formula with an all-zero sum and without
assuming GRH. Its display does not write a separate order factor;
§B.4.2.1, p. 614, specifies counting by multiplicity. To obtain the
all-test strip identity by the proposed substitution, one needs an
all-test formula with those full orders and an actual match of the
polar moments, global Haar scaling, and local principal values,
including terms proportional to evaluation at the identity. On the
provisional reading of (B.4.4.20)–(21), p. 625, the finite normalization
includes a local different correction. It cannot be discarded by
invoking vanishing on the now unrestricted class. The capped
critical-line weights and additional moment conditions of the restatement
in Theorem 13.3.1.1, p. 522, are not obtained by knowing zero locations;
see the [common-test audit](../obligations/trace-divisor-uniqueness.md).

If “Trace Formula” also means the same geometric cutoff trace, the
scalar identity alone does not identify it. In the provisional
extraction of Theorem 12.4.1.1, p. 514, (12.4.1.1)–(3), the normalized
local cutoff diagonal has a term $\varphi(1)\log(\lambda\lambda')$.
The [geometric audit](../obligations/trace-geometric.md) distinguishes
that local calculation from the global diagonal. On unrestricted tests
one must show how the global calculation cancels or subtracts the log
term, and prove that its finite part has the very same normalization
and identity terms as the explicit distribution, with a matching
spectral evaluation. Zero location does not control this cutoff
limit. The paragraph locates the proposed extension after GRH in
Masullo's route, but supplies no proof that an extension by any other
argument is impossible.

**Provenance and checked scope.** The proposed a posteriori argument
is Masullo's; the distinction between scalar substitution and trace
regularization is the project audit's. The accepted
[`Masullo.rationalIdeleRadial_explicit_formula`](../obligations/rational-explicit-formula.md#checked-rational-radial-idelic-explicit-formula)
allows all smooth compact radial log profiles over $\mathbb Q$, including
ones nonzero at log norm zero. It has trivial compact isotype, normalized
scalar local Fourier terms, two polar moments, and all nontrivial zeta
zeros counted by order, with no RH assumption. It does not compare a
geometric cutoff diagonal with a strip spectrum, prove the general-field
normalization, or give zero location. No new Lean result is claimed.
