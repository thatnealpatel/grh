# A below-one test for the constant-weight orbital repair

**Scope.** Work over $\mathbb Q$ in the trivial compact isotype, with
$S=\{\infty\}$, the half twist, even Sobolev index $s\ge4$, and one of the
[common good widths](trace-theta-density-q.md#bounds-for-division-by-zeta)
$0<\alpha<1/2$. Put $\beta=2\alpha$. This tests the two-leg lift of a
specified projected global diagonal. The transfer needs the base of
that same diagonal to equal the local projection modulo the two polar
moments, since that is the local operator the transfer proposes to use
in the p. 520 identification. We prove that this requirement is
impossible for class-constant copy weights.
This does not exclude shells formed before projection or other lifts.

## Split the same diagonal before taking limits

Let $A_f$ denote convolution by the log profile of the test, $P$ the full
weighted geometric projection, $Q_B$ the increasing real-band theta
projector, and $M_\rho$ a compact smooth log position multiplier. Take the
Haar diagonal of $T_{\rho,B}=M_\rho P A_f Q_B=M_\rho A_f Q_B$, with the
[trace-class kernel and shrinking averaging repair](trace-spectral.md#from-the-weighted-kernel-to-the-haar-diagonal).
At fixed $\rho$ the band limit retains the terminal geometric projection,
giving $M_\rho A_fP$. Exhaust position only then. On tests away from one,
the [global model theorem](trace-even-separator-q.md) gives the whole
limiting trace $G(f)=-Z_{\rm strip}(f)$ with full interior orders. No claim
about a joint global limit is used.

Take the [rational positive-real, finite-unit window](../../Proofs/Theorems/RationalIdeleFundamentalDomain.lean)
$D$ and use the normalized counting/Haar splitting $\mathbb Q^\times D$.
Choose finitely many principal copies $2^jD$, $j\in\mathbb Z$, with
nonnegative weights $m_j$ summing to one; when a weight is constant on a
copy it is the same at every quotient point. Apply (12.2.2.1–2)'s
simultaneous two-leg averaging to the already formed kernel. In the lift
from a base output to input translate $2^\ell D$, the factor at classes
$x,y$ is $\sum_j m_j(x)m_{j+\ell}(y)$, allowing for now radial weights
that depend on the class. Summing over $\ell$ gives one. Input $y$ has
unit component at $2$ exactly when $\ell=0$, and every such translate is
unit at every prime outside $2$. Use the repaired right unit mask outside
$2$, not the original decreasing right mask that kills the shell.

For the base input block, the resulting operator is
$\sum_j M_{m_j}T_{\rho,B}M_{m_j}$. Its trace is
$\operatorname{Tr}(M_bT_{\rho,B})$, where $b=\sum_j m_j^2$, by trace
cyclicity. The positive shell $1-1_{D_0}$, restricted to these translates
where $D_0$ is the stage with all finite components units, gives the
complementary trace $\operatorname{Tr}(M_{1-b}T_{\rho,B})$. The sign
$\alpha_{k+1}-\alpha_k$ in (11.3.1.4) instead gives the negative of this
shell. Thus the additive decomposition is base plus positive shell, or
base minus literal signed shell. The angular integration at fixed norm
has mass one in the trivial isotype. No mask is moved through a Paley–Wiener projector, and no
additional norm-only right multiplier is identified with this projector.
Adding such a common input mask would factor out the same copy weights,
but around a different whole trace whose limiting value would first
need to be established.

Thus for constant weights the base and positive shell are exactly $b$
and $1-b$ times the **same** fixed-cutoff trace, with $0\le b\le1$.
This holds cutoff by cutoff even if the finitely many translates or
probabilities vary between cutoffs, provided the same already formed
quotient operator and regular diagonal are used. A zero whole iterated
limit forces zero for both pieces, by the bound by the absolute whole
trace. For moving weights the position limit of the inner limsup of
absolute values is zero, without a claim that the weighted inner limits
exist. The point-mass lift is included.

## A short test with zero whole trace and nonzero local trace

Write $t=-\log |g|$ and choose a real $f\in C_c^\infty(I)$, where $I$
is any nonempty open interval inside $(0,\log 2)$. The test on class
space has profile $f(-\log|g|)$; in the equation for $T_{\rho,B}$ use
convolution by that profile in the ordinary log coordinate. Set
$M_f(z)=\int e^{zt} f(t)\,dt$, so the class-space Mellin samples at $z$
use $M_f(-z)$. The two polar moments are $M_f(\pm1/2)$. The support
misses identity and every finite-prime norm power, including the inverse
powers below one. The [joint local model](trace-joint-local-q.md#below-norm-one-the-defect-is-not-a-sum-of-mellin-moments)
gives raw and genuine projected densities, respectively,

$$J(t)=\frac{e^{-t/2}}{1-e^{-2t}},\qquad
U_\beta(t)=\frac{e^{(\beta-5/2)t}}{1-e^{-2t}}.$$

We need $G=0$, not just zero raw pairing, because the two share a common
cutoff only on the global side. We arrange equality $G=\langle J,f\rangle$
on the witness **without assuming RH or the absence of omitted zeros**.
The [fixed-width zero-density estimate](trace-carving-weight-q.md#the-short-window-detects-any-omitted-zero)
used in the [short even test](trace-even-separator-q.md) gives
$\sum_{|\Im w|>1}|\Im w|^{-1}<\infty$ for the distinct omitted shifted
zeros $w$ at this fixed width, with the set invariant under negation and
conjugation. Split off a finite subset, stable under these symmetries, so
that $\sum \pi/|\Im w|$ for the tail is smaller than the slack from a
smaller open test interval to the right endpoint of $I$. For each tail
$w=a_w+i\gamma_w$, use the two-atom probability supported at $0$ and
$d_w=\pi/|\gamma_w|$, of masses proportional to $1$ and $e^{-a_wd_w}$.
Its Mellin transform at $w$ is zero. The law $\mu$ of the sum of the
independent displacements is a compact probability supported in the
reserved slack; the sum is absolutely bounded by $\sum d_w$. By
independence and bounded convergence, $M_\mu(w)=0$ at every tail
location, and $M_\mu(\lambda)>0$ for real $\lambda$.

### Checked dependency: The compact tail measure

[`Masullo.exists_probability_measure_kill_frequencies`](../../Proofs/Props/ProbabilityMeasureKillFrequencies.lean)
proves the measure construction in the preceding paragraph. For any
sequence $w:\mathbb N\to\mathbb C$ with every $\Im w_n\ne0$ and
summable $d_n=\pi/|\Im w_n|$, it produces **one** Borel probability
$\mu$ with $\mu([0,\sum_n d_n]^c)=0$. Every complex exponential
integrand is integrable; $\int e^{w_n t}\,d\mu(t)=0$ for all $n$,
and $\int e^{rt}\,d\mu(t)>0$ for all real $r$. The last clause gives
nonvanishing for the real coefficients of the transformed densities,
since $e^{rt}$ agrees with the real restriction of the complex
exponential. Carrying does not specify the exact topological support.

In [`Lemmas.BernoulliDisplacement`](../../Proofs/Lemmas/BernoulliDisplacement.lean),
the full displacement has probability $1/(1+\exp(\Re w_n\,d_n))$.
The half-turn identity kills the one-coordinate expectation. Finite
marginals of `Measure.infinitePi` and the product integral transfer that
zero to every initial-segment expectation containing the coordinate.
The displacements sum measurably and are bounded pointwise by the budget;
dominated convergence preserves the zero, and pushforward gives the
stated law. Compact carrying gives integrability and the real integral
is positive because the integrand is everywhere strictly positive.

This is an original repair for the omitted-sample comparison with
(12.5.1.3–4), pp. 519–520. It is not a consequence of Masullo's orbital
trace theorem or his local multiplier calculation. Given a summable
omitted tail, the theorem allows the convolution displacement to fit
arbitrarily small positive slack by choosing the finite split first.
It does not prove summability, form the filtered bump, or compare traces.

Writer check (Yah `01a20624-d19d-7566-86d3-0dc22f4adc92`):
`lake build --wfail +Lemmas.BernoulliDisplacement +Props.ProbabilityMeasureKillFrequencies`.
A fresh joint import and `#check @Masullo.exists_probability_measure_kill_frequencies`
confirmed the statement; `#print axioms` on it and the supporting
lemmas used only `propext`, `Classical.choice`, and `Quot.sound`.
The integration owner checks the exact candidate separately.

Independent read-only review `tail-statement` (`kijjoZR`, output
`3f772a9b867a2a4ed96f1ae0c3a297b73341e3cb`) confirmed the exact, unchanged
statement against the obligation at `0fa139d2d20de39dcc566b38d23103eb95ff957d`.
It checked the PDF digest and read Theorem 12.5.1.1, pp. 519–520,
(12.5.1.3–4), against Theorem 11.3.2.1, pp. 495–496 (strictly above-one
support), and (12.4.1.8–12), p. 517 (local Fourier multiplier). These are
provisional Markdown/layout readings, without rendered-page verification.
The review distinguishes the positive scalar transform from a claim of
smoothness or positivity of a density. The writer's two-revision diff
confirms that the assigned base `e58cab0cc9def603bd473be0bbd71da3a24ceff4`
adds only a separate same-width comparison note to the reviewed base;
the tail obligation is identical there.

### Applying the measure to the short test

For a real bump $\phi$ supported in the smaller interval let
$f=P_0(\partial_t)(\mu*\phi)$, where
$P_0(z)=(z^2-1/4)\prod_{w\,\mathrm{finite}}(z+w)$ has real coefficients.
Then $M_f(z)=P_0(-z)M_\mu(z)M_\phi(z)$. This kills both polar moments and
all omitted samples, hence also the sum weighted by their multiplicities;
no derivatives at zeros are needed for this scalar. By the
[rational explicit formula](rational-explicit-formula.md#checked-rational-radial-idelic-explicit-formula)
we have $G(f)=-Z_{\rm full}(f)=\langle J,f\rangle$ on these tests.

[`Masullo.exists_compactLogMellin_filter`](../../Proofs/Props/CompactLogMellinFilter.lean)
checks the filter construction given the tail sequence, budget, finite
polynomial, and seed support. One probability works for every polynomial
and seed. Translation enlarges $[a,b]$ only to $[a,b+D]$; the polynomial
differential operator does not enlarge support. The theorem states the
product and both vanishing implications, not the zero-density estimate
or the application of the explicit formula. If the omitted set is finite
or empty, use only the polynomial and the unaveraged seed; do not pad a
finite sequence by repeating a nonreal frequency.

Masullo gives the log-Mellin convention and iterated integration by
parts on PDF p. 599, (B.2.1.29–31), not the filter for the omitted samples
in (12.5.1.3–4), pp. 519–520. The existing
`Masullo.compactLogMellin_iteratedDeriv` proves the monomial multiplier
without division. `Masullo.compactLogMellin_logPolynomialDeriv` applies
it to the real finite combination, including the negative sign at the
Mellin argument. The composed filter uses that result and the
translation factor below. Independent Yah review `polynomial-filter-review`
(`xmWuntj`, output `77bf31be2d1dfccffa014992d94b8457ad1fc38b`) affirmed
all three fixed contracts at `42ed4c4b060b7bce6e750cd95a540f9e4d5f9935`,
including the reflected argument below norm one and the even-test use.
The manuscript reading is provisional Markdown/layout, not rendered-page
verification. Owner checks are in Yah `01a20624-d19d-7566-86d3-0dc22f4adc92`.

Remaining for the scalar witness: First justify in Lean the integration
by parts and Fubini identity transferring pairing against a density to
pairing against the seed. Then prove nonproportionality for the two
specific transformed densities, and supply the actual omitted-set
budget and strip/full sum comparison. None of these follows from
positivity of the real measure moments alone.

Integration by parts and translation send pairings with a density $D$
(here $J$ or $U_\beta$) to pairings against $\phi$ with

$$ K_D(t)=\int P_0(-\partial)D(t+u)\,d\mu(u). $$

For $t>0$ these are real analytic by the normally convergent geometric
exponential series, including after differentiation, on each
$\Re t\ge\delta>0$. The largest surviving exponent for $K_J$ is
$-5/2$: The $-1/2$ term is killed by $P_0$, and the coefficient at
$-5/2$ is $P_0(5/2)M_\mu(-5/2)\ne0$. For $K_U$ the largest exponent is
$\beta-5/2$, with coefficient $P_0(5/2-\beta)M_\mu(\beta-5/2)\ne0$.
The roots of $P_0$ have real parts in $[-1/2,1/2]$. These different
exponents, by dividing by $e^{(\beta-5/2)t}$ and taking $t\to\infty$,
exclude proportionality on $(0,\infty)$, hence by analyticity also on
the smaller test interval. If the functional with density $K_U$ vanished
on the kernel of the $K_J$ functional on bumps there, it would be a
scalar multiple of the latter. Testing against all bumps would identify
the continuous densities, contradicting the exponent comparison. Choose
$\phi$ in that kernel with nonzero $K_U$ pairing.

For this same test $G(f)=\langle J,f\rangle=0$, but
$\langle U_\beta,f\rangle\ne0$. Both constant-weight pieces of the actual
project global diagonal tend to zero, so this orbital shell cannot
supply the difference between the local projection and the multiplier
in either sign convention. In particular, identifying the base with the
local projection up to the two printed moments is impossible for this
family of lifts. The conclusion is independent of whether the orbital
circle quotient is the intended shell: Its twisted circle trace sums
vanish separately by Poisson summation because every point sample at
$j\log p$ vanishes. This does not make the individual Fourier–Mellin
coefficients vanish, or identify the circle with the lifted diagonal.

## Manuscript correspondence and exact scope

Provisional text/layout reading of the [pinned manuscript](../sources/masullo/README.md),
not a fresh rendered-page verification.

- Equations (11.2.1.8–10), p. 489, supply a named right projector and a
  fixed-position band limit on tests supported at norms at least one.
  Here we use the checked rational real-band exhaustion in a repaired
  weighted model, with the retained right projection, not the extension
  of the printed limit to tests below one.
- Equation (11.3.1.4), p. 494, supplies the signed input shell.
  Theorem 11.3.2.1, pp. 495–496, assumes support strictly above one and
  invokes the **orbital quotient** trace of Theorem 7.4.2.1, p. 367, via
  (11.3.2.5). That input does not evaluate the projected shell on these
  tests. Proposition 12.2.2.2, p. 508, (12.2.2.1–7), supplies the
  pattern for the simultaneous two-leg lift and diagonal unfolding.
  We use the direct counting/Haar disintegration on the rational window,
  not the proposition's connected fundamental-domain setup. The lift
  replaces (11.3.2.2), and using the outside-$2$ mask fixes the shell
  annihilation of (11.3.2.3); neither is a reading of the printed limit.
- Theorem 12.4.1.1, p. 514, is proved on pp. 515–519. The step
  (12.4.1.8–12), p. 517, uses a Fourier multiplier and the trace calculation
  gives the raw scalar, not our projected local value. Theorem 12.5.1.1,
  pp. 519–520, needs the pieces of one common diagonal, invokes orbital
  vanishing, and
  identifies its base with local terms minus the polar moments. Our
  test has support in $(1/2,1)$ in norm, admits $T<2$ in its support
  condition, and has both moments zero. Its vanishing at log norm zero
  is the value condition in §12.5, not a vanishing-integral condition.
  The obstruction is to using this class-constant transfer to reconcile
  the **projected** local
  model with the raw scalar there. It is not a new application of the
  printed above-one orbital theorem. Nor does it say that identifying a
  separately justified global base with the *raw* value would fail on
  this witness, where both are zero.

The full witness with omitted-sample filtering and its trace comparison
are reviewed ordinary mathematics, not Lean declarations. The conditional
filter is checked above; it does not machine-check this obstruction end
to end.

## Checked local scalar separation

Lean's
[`Masullo.exists_smooth_test_trace_scalar_separation`](../../Proofs/Props/TraceScalarSeparation.lean)
separates the local pairings in every nonempty open $I\subset(0,\log 2)$:
There is a real smooth $f$ with compact topological support in $I$, both
polar moments zero, $\langle J,f\rangle=0$, and
$\langle U_\beta,f\rangle\ne0$. All four products are Lebesgue
integrable. The density formulas come from the rational local model,
not from treating the manuscript's projection as its multiplier.

The Lean proof first factors a putative kernel inclusion through the
three moment functionals, then tests against all bumps to obtain an
identity of continuous densities. After multiplication by $1-e^{-2t}$,
the exponent $\beta-5/2$ is distinct from the four constraint exponents.
A differentiation argument excludes the resulting exponential relation.
This closes the local scalar separation only: The filtered witness above
requires a different independence argument and the omitted-zero input.

`scalar-statement-review` (`IolcisX`) independently checked the exact
statement, $g=e^{-t}$ and its Haar measure, the exponents and signs, and
the p. 517 and pp. 519–520 interfaces against the pinned text/layout.
The owning candidate build, joint import, signatures, and axiom report
are recorded in Yah session `01a20615-9d61-7879-bfbb-bb714a7cbca9`.

## Checked smoothing for the short test

[`Masullo.logTranslateAverage_smooth_supported`](../../Proofs/Lemmas/CompactLogMellinSmoothing.lean)
proves that a finite measure carried by $[0,D]$ sends a smooth test
supported in $[a,b]$ to the smooth real log profile
$g(x)=\int\phi(x-t)\,d\mu(t)$ supported in $[a,b+D]$. This uses
parametric integration on the carrying interval. With only continuity
of $\phi$ and the same support and measure hypotheses,
`Masullo.compactLogMellin_logTranslateAverage` uses absolute integrability
on a compact rectangle, Fubini, and Lebesgue translation to prove
$M_g(z)=M_\phi(z)\int e^{zt}\,d\mu(t)$ for every complex $z$.
This is the positive Mellin sign in the $t$ coordinate. Below norm one,
$t=-\log|g|$, so the shifted class sample uses $M_g(-z)$, and the
omitted set is stable under negation.

These Lean results supply smoothness, support, and the convolution
factor for the filtered test above and for the
[even separator](trace-even-separator-q.md). They are part of an
original witness construction for comparing the strip sum in
(12.5.1.3–4), pp. 519–520, with the full sum. They do not supply a
trace identity or compare a projected shell to a local cutoff.

Independent read-only `smoothing-review` (`naCfTGW`, output
`96604d689ac137b758de74c4feb6f004c91be714`) checked the fixed hypotheses,
translation sign, support slack, and the match to both witness arguments
against `4c06d9d8aff8d97563d20aae176f5dffe4834bc8` and the pinned Mathlib.
The review checked the manuscript's pp. 519–520 requirements, the
strictly above-one support of Theorem 11.3.2.1, p. 495, and the
multiplier at (12.4.1.8–12), p. 517, by Markdown and layout extraction;
this fresh reading is provisional, not rendered-page verification.
The owning exact-candidate build, joint import, and axiom check are
recorded in Yah session `01a20624-d19d-7566-86d3-0dc22f4adc92`.

**Next proof obligation:** For a real polynomial $P$, implement
$P(\partial_t)$ on a real smooth compact log profile without widening
its support, and derive the multiplier $P(-z)$ from the existing
[`compactLogMellin_iteratedDeriv`](../../Proofs/Lemmas/CompactLogMellin.lean).
This will assemble the two parts of the filter. It will not yet prove
the nonproportionality of the transformed $J$ and $U_\beta$, the
density bound giving the budget for the actual omitted zeros, or the
projected trace comparison.

## Exact successor for position-dependent weights

For fixed smooth bounded radial probabilities $m_j(x)$, the preceding
cyclicity argument instead gives an exact weighted trace at each cutoff.
Its level-first base limit is

$$ -\operatorname{Tr}\bigl(M_b A_f(1-P)\bigr),\qquad b=\sum_j m_j^2, $$

and the positive shell has the same formula with $1-b$. Indeed the band
limit at fixed $\rho$ first gives $\operatorname{Tr}(M_{b\rho} A_fP)$.
Inserting $P=1-(1-P)$ gives no unprojected term: $M_{b\rho} A_f$ is
trace class by compact convolution smoothing, with zero continuous
kernel diagonal since the test vanishes at the identity. Exhaustion of
position then converges in the trace-class ideal on $A_f(1-P)$.
A position-dependent lift must test this new weighted functional (and
justify its orbital identification), not merely choose another constant
spread. The off-diagonal block of $A_f(1-P)$ cannot be discarded under
$M_b$ just because it has trace zero without $M_b$. An upstream shell
inside the projected operator lies outside this calculation.

**Independent review:** `shell-review` (`nGRsVZp`), in Yah session
`01a20615-9d61-7879-bfbb-bb714a7cbca9`, checked the fixed-cutoff split,
filtered witness, scalar signs, and weighted successor, and compared the
interfaces with the pinned Markdown and numbered layout. The full
constant-weight obstruction is not machine-checked, and neither review
claims rendered-page inspection.
