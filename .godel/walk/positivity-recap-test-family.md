# The test family in the positivity recap

**Status: Open.** Masullo, *The Music of the Primes*, printed p. 30,
§1.4.6, paragraph beginning “Positivity of the Weil functional from
Weil’s Explicit Formulas is not addressed,” through the logarithmic
quotient. The paragraph says the trace holds on a sufficiently large
class of tests to approximate a piecewise smooth holomorphic family
and obtain information about the finite Hecke logarithmic derivative.
It does not assert a positivity theorem. Coverage here stops before
“Indeed, the trace formula can only be proved.”

Chapter Markdown and PDF layout extraction located the paragraph in
the [digest-verified edition](../sources/masullo/README.md). Raster OCR
checked the prose. Direct inspection of rendered pixel crops checked
the exponent, the two intervals, the argument and value in the isolated
assignment, and the derivative in the numerator. The page prints
$\varphi_s(t)=t^s$ for $t>1$, zero for $0<t<1$, and
$\varphi(1/2):=1/2$, with target $L_f'(s,\chi)/L_f(s,\chi)$.

**Literal reading versus the preceding construction.** The isolated
assignment, read as part of the same profile, conflicts with the zero
branch at $t=1/2$. Reading it instead as an exception still does not
match the preceding approximants: They are identically zero below
norm one, including at $1/2$, which is a negative prime-power sample
over $\mathbb Q$. The [rendered §1.4.2 reading](holomorphic-test-family.md)
has the value $1/2$ at the breakpoint $t=1$ and only claims scalar
pointwise convergence for $t\ne 1$. Moving the assigned value to
$t=1$ would reconcile that part of the recap, but would not approximate
the assigned value on the norm-one fibre.

The preceding family is $t^{-z}$ above norm one, not $t^z$. With
$t=q_v^m$, the positive finite shell of §1.4.4 for the printed recap
profile contains $q_v^{-m(1/2-s)}$, not $q_v^{-m(s+1/2)}$.
Relabelling $z=-s$ also moves the Euler-product overlap. With the
preceding decaying profile, a consistent character lift, and ramified
coefficients set to zero, the [finite-place calculation](finite-prime-cutoff-sign.md)
gives $-L_f'(z+1/2,\chi)/L_f(z+1/2,\chi)$ on $\Re z>1$. Neither
an exponent correction nor a relabelling by itself verifies the trace
argument.

**Missing step.** To use the preceding construction, first justify a
common fixed-cutoff trace identity for the actual positive-log tests
in the chosen isotype and at the widths and degree used in §1.4.
Then prove a cutoff limit, or a specified subtraction with compatible
limits, that controls the Archimedean and strip-zero contributions
at a common normalization, locally uniformly in the parameter on
connected domains reaching $\Re z>a$ for arbitrarily small positive
strip half-widths $a$, and matches the correctly signed finite
derivative and actual polar parts on the right-hand overlap.
Pointwise scalar convergence is not continuity in a topology that
controls those trace terms. In particular, the [unsubtracted zero-sum
audit](unsubtracted-zero-sum-limit.md) exhibits divergence for the
full-width rational scalar formula; that check does not decide a
renormalized trace at narrower widths. The general limiting trace
comparison is not established by the recap.

The route and cutoff construction are Masullo’s; the cross-checks
and separation of the proof obligations are the reviewer’s. No Lean
result is added. `Masullo.finiteHeckeCharacterEulerProduct_logDeriv`
provides the signed finite Euler-product derivative on its right
half-plane, not the cutoff limit of an idelic trace.
`Masullo.tendsto_positiveLaplaceTest_cutoffTest` concerns scalar
Laplace limits of subtracted log-coordinate profiles under decay
hypotheses, not the printed family or its trace. Neither is evidence
of GRH.
