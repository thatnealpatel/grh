# A below-one test for the constant-weight orbital repair

**Scope.** Work over $\mathbb Q$ in the trivial compact isotype, with
$S=\{\infty\}$, the half twist, even Sobolev index $s\ge4$, and one of the
[common good widths](trace-theta-density-q.md#bounds-for-division-by-zeta)
$0<\alpha<1/2$. Put $\beta=2\alpha$. This tests the two-leg lift of a
specified projected global diagonal. The transfer needs the base of
that same diagonal to equal the local projection modulo the two polar
moments, since that is the local operator the transfer proposes to use
in the p. 520 identification. The conditional separator tests this
requirement for class-constant copy weights. It does not exclude shells
formed before projection, a direct evaluation of the raw local terms,
or other lifts.

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

### Checked dependency: Moving the filter to the density

[`Masullo.integral_logPolynomialDeriv_logTranslateAverage`](../../Proofs/Props/CompactLogMellinAdjoint.lean)
proves that pairing the filtered test with a density $ρ$ is the same
as pairing the seed $φ$ with

$$ K_ρ(t)=\int P(-\partial)ρ(t+u)\,d\mu(u). $$

The theorem assumes $φ$ is smooth with topological support inside
$[a,b]$ for $a>0$, $μ$ is finite and carried by $[0,D]$, and $ρ$
is smooth on $(0,\infty)$. Both whole-line products are integrable.
No smoothness at zero or bound at infinity is imposed on the density.
The inner integral defining $K_ρ$ need only exist classically on the
seed support; Lean uses the totalized integral elsewhere.
First integration by parts moves the polynomial to the density with
one minus sign per derivative. Then Fubini on compact carrying
rectangles and Lebesgue translation replace the test shift $-u$ by
the density shift $+u$.

This step is an original argument for comparing the rational scalar
densities entering the proposed repair of (12.5.1.3–4), pp. 519–520.
Masullo gives integration by parts for a Mellin exponential in
(B.2.1.31), p. 599, not this identity for the filtered test and a
possibly singular density. The two densities here are the raw and
projected densities of the rational model, not an asserted equality
of Masullo's multiplier (p. 517, (12.4.1.8–12)) with the projection.
Independent read-only review `adjoint-statement` (`CZRgWxT`, output
`76bdb2dc039402979d592d5bf3ba53486aeb886c`) checked the fixed contract,
both signs, the compact carrying rectangles, and the absence of a
boundary at zero against `d17819758975e1028f23f72d46270931000adc11`.
It checked the pinned digest and the passages above plus the above-one
support in Theorem 11.3.2.1, pp. 495–496, using Markdown and layout,
not rendered pages. The owning exact-candidate checks are recorded in
Yah `01a20634-af61-7ca4-9490-2b578475735c`.

<a id="remaining-separation-of-the-transformed-densities"></a>

### Separation of the transformed densities

The adjoint identity reduces the kernel test to the two continuous seed
densities $K_J$ and $K_{U_\beta}$. They must not be proportional on the
smaller open seed interval: Otherwise every seed killing the filtered raw
pairing would also kill the filtered projected pairing.

[`Masullo.filteredLogDensity_not_eqOn_mul`](../../Proofs/Props/FilteredLogDensitySeparation.lean)
proves this nonproportionality on any nonempty open subset of $(0,\infty)$.
Its hypotheses are a probability $\mu$ carried by $[0,D]$, $\beta>0$,
$P(1/2)=0$, and $P(5/2-\beta)\ne0$. The latter two hold in the proposed
application to $P_0$: The polar factor gives the first, and all roots
have real parts in $[-1/2,1/2]$, whereas $5/2-\beta>3/2$ for the model's
$0<\beta<1$. The theorem does not require a nonzero coefficient at the
first possible surviving raw rate.

For $\rho_r(t)=e^{rt}/(1-e^{-2t})$, write $K_r$ for the average of
$P(-\partial)\rho_r$ at positive shifts. The supporting results in
[`Lemmas.FilteredLogDensity`](../../Proofs/Lemmas/FilteredLogDensity.lean)
prove analyticity on positive logs, the exact change in $K_r$ when the
$e^{rt}$ term is subtracted, and

$$ e^{-rt}K_r(t)\longrightarrow P(-r)\int e^{ru}\,d\mu(u) \quad(t\to\infty). $$

Here $K_J=K_{-1/2}$ and $K_{U_\beta}=K_{\beta-5/2}$. The identity
principle extends a putative proportionality to all positive logs. The
polar root makes $K_{-1/2}=K_{-5/2}$ there. After normalizing at the
projected rate, the raw side has the extra factor $e^{-\beta t}$ and
hence tends to zero. The projected side tends to a nonzero polynomial
value times a strictly positive real moment. This is an original scalar
argument for the proposed repair of (12.5.1.3–4), pp. 519–520. It uses
the rational model pair, not an identification of the actual local
projection with Masullo's Fourier multiplier (12.4.1.8–12), p. 517.
Theorem 11.3.2.1, pp. 495–496, cannot supply the below-one comparison
because its tests are strictly above one. These manuscript readings are
provisional Markdown/layout readings, not rendered-page verification.

Independent read-only Yah `density-review` (`EPtymgE`, output
`becb9ac7a7141b730aa0e812a95e058f5b99eda0`) checked the fixed statement
and supporting contracts, the two rates, the $P_0$ application, and the
scope against the pinned manuscript at
`47eb4b607ef17236bbc0e82d00a4346d7dc3d0a8`. Owning exact-candidate check:
Yah `01a20642-dbdb-7b6d-b0e5-218cf3eaa9e9`.

### Checked short filtered separator

[`Masullo.exists_smooth_test_filtered_density_separation`](../../Proofs/Props/FilteredLogTraceSeparation.lean)
fixes any carried probability $\mu$, polynomial $P$, and rate $\beta$
from the preceding nonproportionality theorem, and any $0<a<b$. If the
projected seed pairing vanished on the kernel of the raw seed pairing
in $C_c^\infty((a,b))$, `compactSmooth_moment_relation` would express the
projection as a scalar multiple on bumps. `eqOn_of_compactSmooth_moments_eq`
would then give the excluded equality of continuous densities on $(a,b)$.
The adjoint transfers the selected seed's zero and nonzero pairings to
one smooth filtered test, with support in $[a,b+D]$ and both products
integrable on the whole real line.

`Masullo.exists_compactLogMellin_filter_trace_separation` chooses the
measure using a given sequence of nonreal tail frequencies with
summable displacement budget $D=\sum_n\pi/|\Im w_n|$. The *same* test
has the two different pairings and kills all those Mellin samples and
all samples at roots of $P(-z)$. For the below-one band the application
must choose $b+D<\log 2$. The construction also works without a tail
by applying the first theorem with the probability point mass at zero.

This assembles an original short-test argument for the comparison in
Theorem 12.5.1.1, pp. 519–520, (12.5.1.3–4). The source supplies the
Mellin integration-by-parts template (p. 599, (B.2.1.29–31)), but neither
the simultaneous witness nor the identification of the weighted local
projection with the multiplier in (12.4.1.8–12), p. 517. The above-one
hypothesis at pp. 495–496, Theorem 11.3.2.1, still excludes these tests.
Independent read-only Yah review `filtered-test-review` (`mndmHjP`)
checked the exact contracts and the pinned manuscript at
`65c47377eac2080b1310073604660fd6d3f64ae1`. The source reading is
provisional (Markdown and numbered layout, not rendered pages).
The owning exact-candidate checks are in Yah
`01a2064d-01df-7985-9550-7d5295c124ee`.

### Conditional budget for the actual omitted divisor

[`Masullo.exists_omittedZetaTail_reciprocal_budget`](../../Proofs/Props/OmittedZetaTailBudget.lean)
reduces the tail hypothesis to a right-hand zero-density estimate. For a
fixed $0<\alpha$, assume the number of distinct critical-strip zeros
with $\Re\rho\ge 1/2+\alpha$ and $0<\Im\rho<2^{j+1}$ is at most $Cq^j$
for all $j\ge0$, with $0\le q<2$. Then for every $\varepsilon>0$ there is
$T\ge1$ such that the distinct actual zeros with
$|\Re\rho-1/2|\ge\alpha$ and $|\Im\rho|>T$ have summable displacement
costs $\pi/|\Im\rho|$, of total less than $\varepsilon$. The weak
inequality in the real coordinate includes both edges of the open
strip. All remaining omitted zeros are a finite set by
`criticalStripZetaZeros_boundedIm_finite`, using the enclosing open
height interval $(-T-1,T+1)$.

In `Lemmas.ZetaZeroHeightBudget`, reflection $\rho\mapsto1-\bar\rho$
and conjugation put each sign sector in the counted sector, yielding
a factor at most four. A dyadic shell with lower height $2^j$ then
costs at most $4\pi C(q/2)^j$. After summability, the cutoff is raised
above a finite set that accounts for all but the specified budget.
This is an original reduction for comparing (12.5.1.3–4), pp. 519–520,
which sum over the open strip, with (B.4.2.2), p. 614, which does not
cut down to that strip. Neither passage proves the density premise.
These readings are provisional from the pinned Markdown and PDF text
layout, not a rendered-page inspection.

Owning check session: Yah `01a20655-db3c-7878-9b63-9a84a996229f`.
The statement review and exact candidate build, joint import, signature,
and axiom checks are recorded in that session.

**Next analytic obligation:** Prove the above right-hand dyadic count
in Lean for every fixed $0<\alpha<1/2$, allowing $C,q$ to depend on
$\alpha$. The [reviewed classical power-saving estimate](trace-carving-weight-q.md#the-short-window-detects-any-omitted-zero)
would give it: Absorb the logarithmic factors into a slightly larger
power still less than one and inflate $C$ for finitely many low
shells. The checked quadratic full-divisor summability does not imply
this bound. The exact witness construction using this conditional
budget is now checked below. The rational strip index and conditional
RH endpoint (`rationalRadialStripIndexEquiv` and
`riemannHypothesis_of_ideleClassTraceFormula`) do not supply the count
or identify the analyzed global operator with either scalar trace.

### Checked conditional witness for the omitted divisor

[`Masullo.exists_compactLogMellin_omittedZeta_trace_separation`](../../Proofs/Props/OmittedZetaTraceSeparation.lean)
uses the right-upper dyadic count above, with $0\le q<2$, to build one
real smooth $f$ supported in any $(L,U)$ with $0\le L<U\le\log 2$.
For $0<\beta<1$ it has $\langle J,f\rangle=0$,
$\langle U_\beta,f\rangle\ne0$, and
$M_f(\pm\tfrac12)=0$. For every distinct critical-strip location outside
or on the boundary of the open $\alpha$ strip, it gives
$M_f(- (\rho-\tfrac12))=0$. In the modeled trace take $\beta=2\alpha$;
the construction itself does not require that relation.

The bounded-height locations are finite. Take a real polynomial with
both polar roots and a conjugate-pair factor for each of those locations,
centered at $\rho-\tfrac12$. The polynomial filter evaluates $P(-z)$;
its evaluation at $5/2-\beta$ is nonzero because every centered root
has real part of absolute value less than $1/2$. The high tail enters
at the reflected frequencies by an injective embedding into $\mathbb N$.
Fill unused positions with dummy imaginary frequencies of small total
reciprocal-height cost, retaining the support slack. This handles all
tail cardinalities, including the empty tail. Neither multiplicity
nor a small-but-nonzero spectral residual enters the budget.

The independent review `witness-review` (`IPgWAzB`) checked the fixed
endpoint, tail and polynomial signs, and source dependencies in Yah
`01a20665-8398-7aef-960a-b6623a4acd80`. In particular, the interior
orders of (12.5.1.3–4), pp. 519–520, agree with the cited
Theorem 10.4.2.8, p. 463, via (10.3.2.3–4), p. 454; the latter's capped
edge terms are immaterial on this specific test. These readings are
provisional, based on pinned Markdown and numbered layout. The proof is
an original construction, not a result furnished by those passages.
The writer check at output `8043871f9cd61d47199bf358575d65ac5f133f38`
and the owning checks of accepted revision
`c1d9906c831ff0c9380c9bacd83d5b66bcd67c51` are recorded in the same
session and summarized in the [experiment ledger](../experiments/matched-improvement-recovery/#live-follow-up-budget-the-actual-omitted-divisor).
The power-saving count remains unproved in pinned Lean.

### Checked scalar transfer on a test killing the omitted divisor

[`Masullo.rationalIdeleRadialMellin_reflect`](../../Proofs/Theorems/RationalIdeleRadialExplicitFormula.lean)
transports a profile $F(x)=f(-x)$ along normalized rational class log Haar.
It gives the class sample $M_f(-(s-1/2))$, so the two pole arguments are
$1/2$ and $-1/2$. This applies the log convention in (B.2.1.29), p. 599,
to the reflected coordinate; it does not change the Haar normalization.

[`Masullo.rationalRadial_stripTrace_of_omitted_mellin_zero`](../../Proofs/Theorems/RationalRadialStripTrace.lean)
starts from the checked full scalar balance and replaces the summand by
its interior-strip indicator. The entire omitted term is zero because
the sample, not merely an estimate of the weighted term, is zero. It
produces a `HasSum` over the open-strip index with full orders, with
unchanged normalized local terms, actual real cutoff convergence, and
finite support in the finite places. This is the one-test scalar transfer
from (B.4.2.2), p. 614, to the truncation in (12.5.1.3–4), pp. 519–520.
The manuscript does not supply the termwise vanishing premise. Boundary
order conventions do not affect the comparison on this test; capping
positive orders in the interior would still change the obligation.

Owning check session: Yah `01a20665-8398-7aef-960a-b6623a4acd80`.
Independent fixed-statement review: `radial-bridge-review` (`CJtGPsL`)
in that session. The pinned Markdown and layout readings remain
provisional pending rendered-page inspection. These lemmas neither remove
the witness's density premise nor evaluate a common global diagonal.
For the actual below-one profile, the real and finite-place evaluations
are checked together in
[`Masullo.exists_rationalShortWindow_stripTrace_separation`](../../Proofs/Theorems/RationalShortWindowStripTrace.lean).
On any $0\le L<U\le\log 2$, the conditional dyadic count at
$0<\alpha<1/2$ gives one compact smooth $f$ supported in $(L,U)$.
For $F(x)=f(-x)$, the normalized real cutoff tends to zero, **every**
finite-place term is zero, both polar samples vanish, and the full-order
open-strip series has sum zero. Yet the pairing with the modeled
projected density $U_{2\alpha}$ is nonzero.

Equation (B.4.4.22), p. 625, gives valuation shells. Equations
(B.4.2.10–11), p. 615, locate the forward and inverse samples, but we
use the checked normalized expansion, not the raw contour coefficients.
For every prime $p$ and $m\ge1$, $\log(p^m)\ge\log 2$, so neither signed
log sample can see $F$. For (12.5.1.1), p. 519, `RealLogHaarFold.fold`
folds the signed half-Haar integral to the positive ray, leaving exactly
$J(t)f(t)$ and no identity term. The proof selects a strictly positive
lower support bound, so the integral is unchanged for every sufficiently
small positive cutoff. The reflected Mellin formula and termwise
omitted-zero transfer give the `HasSum` conclusion, without taking a
zero-width limit or capping any interior order.

Owning check session: Yah `01a20671-21b5-7330-a3a4-696e13ff136f`.
Independent fixed-statement and manuscript review:
`scalar-statement-review` (`otZSpjz`, output
`ba016abdeae7de65f0cf2f9960d5da090077a59e`) in the same session, at base
`39ee9109595caf1749566ed304ac03846c564047`. Its readings of
(B.2.1.29), p. 599, (B.4.2.2), p. 614, (B.4.2.10–11), p. 615,
(B.4.4.16, 22), pp. 623, 625, and (12.5.1.1–4), pp. 519–520, are
provisional from the pinned Markdown and PDF text layout, not rendered
pages. The reviewer distinguishes the scalar balance from the claimed
identification of the local and orbital pieces with one global kernel.
The missing below-one orbital coverage of Theorem 11.3.2.1, p. 495, is
not needed for this scalar result.

With the actual omitted samples killed and the model’s strip trace
identified, the explicit formula gives $G(f)=\langle J,f\rangle=0$,
but $\langle U_\beta,f\rangle\ne0$. Both constant-weight pieces of the
rational model's global diagonal tend to zero, so this orbital shell cannot
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

The conditional witness, its normalized real and finite-place terms,
and the open-strip `HasSum` are checked above. The power-saving count,
the comparison with the common global trace, and the necessity of the
modeled projection for the manuscript remain separate. The obstruction
is not machine-checked end to end.

**Operator-side successor:** The [fixed-cutoff copy split below](#checked-constant-copy-split-before-either-limit)
now bounds both pieces by the absolute whole trace. Neither the ordered
trace limit nor the distinct omitted-location count is closed in Lean.

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

## Checked fixed-cutoff density in the global theta chart

[`Masullo.OperatorTrace.rationalThetaBand_traceDensity`](../../Proofs/Theorems/RationalThetaBandTraceDensity.lean)
constructs the fixed-cutoff operator on the weighted **global rational
theta** levels of `RationalThetaBandClosure`. In the Lebesgue $L^2$ chart
let $W$ be `symmetricStripWeightRoot` at width $\alpha\ge0$ and index
$s\ge0$, and $Q_Y$ the orthogonal projector onto the weighted even rational
theta band. For continuous compactly supported $\rho$ and $C^2$ compactly
supported $\phi$, the constructed bounded operator is

$$ (Bz)(x)=\rho(x)W(x)\int\phi(x-y)(Q_Yz)(y)W(y)^{-1}\,dy. $$

There is an integrable $d$ with basis trace $\int d$, and for every
essentially bounded log multiplier $m$, the basis trace of $BM_m$ is
$\int m d$ in the same chart. The proof periodizes $\phi$ on a window
covering all relevant differences and uses the output $\rho W$ and the
compact input window $1_{[-2R,2R]}/W$. The reciprocal weight acts on
$Q_Yz$, while $M_m$ acts on $z$ **before** $Q_Y$. The rank-one series gives
the diagonal in $L^1$, not by restricting a product-a.e. kernel identity.
The reusable `annulus_kernel_ae_input_mul` retains the input factor;
`annulus_kernel_ae` keeps its previous statement.

**Source and repair:** Masullo specifies the cutoff and operator order
in (10.4.1.6–7), p. 457, and the global level projection in (11.2.1.8–10),
p. 489; compare his weighted kernel (10.4.3.48), p. 473. The latter level
convergence citation is for support at or above one and does not give a
density for our below-one test in the positive-width theta chart. The
Lean construction gives the chart form of $M_\rho A Q_Y$, not an assertion
that $PA=AP$ for the full geometric projector $P$. To compare to the
printed $M_\rho P A Q_Y$ at half twist and positive width, use
$\operatorname{ran}Q_Y\subseteq\operatorname{ran}P$ and prove that convolution
preserves the **full** geometric range in that norm; no finite-band
invariance is required. See the [reviewed order repair](trace-hardy-diagonal-q.md#removing-the-order-defect-in-the-weighted-rational-isotype).

The earlier `RealLogLevel.fixedAnnulus_traceDensity` has a different
right projection: Its range is built from individual two-moment
real profiles, not their lattice theta sums. For positive finite $Y$,
global band generators vanish on $e^{-x}>Y$ by
`rationalTheta_eq_zero_of_inv_gt_band`, and this property is preserved
by closure. Nonzero local band generators need not vanish there:
Their additive profiles are entire. Weight multiplication does not
remove this distinction.

**Evidence:** Independent `two-leg-review` (`HPXDyeI`, base
`854d3946e90b25209366cb6b22b9a5139ae0d462`, review output
`76e7e9c5049179ba19ff3906d91bf0ac377a27cc`) checked the fixed statement,
weights, mask order, and the source dependencies through pp. 489,
493–496, 508, and 517–520. Its pinned Markdown and layout readings are
provisional, not a rendered-page review. Owning Yah session
`01a20678-b664-799c-ba54-9d0337bef822` records the exact candidate diff,
build, joint-import signatures, axiom reports, and adoption decision.

## Checked constant-copy split before either limit

[`copyDiagonalWeight_eq_translate_sum` and `copyDiagonalWeight_split`](../../Proofs/Props/CopyDiagonalWeight.lean)
check the relative-input counting factor $c(h)$ for ordered output and
input labels $(i,j)$ with $i^{-1}j=h$. The translate formula is the sum
of $m_i m_{ih}$ with input weights extended by zero off the finite label
set. For nonnegative weights of total mass one, the total counting sum
is one, the identity has mass $b=\sum_i m_i^2$, and the remainder has
mass $1-b$.

[`rationalThetaBand_copyTrace_split`](../../Proofs/Theorems/RationalThetaBandCopyTrace.lean)
keeps the same fixed-cutoff global operator $B$ and $L^1$ density $d$ as
the preceding construction. For each $h$, the scaled operator $c(h)B$
has basis trace $\int c(h)d=c(h)T$ with $T=\int d$. Lean checks the
counting sum of these traces, the off-identity sum $(1-b)T$, the signed
decomposition $bT-(-(1-b)T)=T$, and both bounds by $|T|$. The statements
are pointwise in the cutoffs and require no limit of the weights.

**Source and repair:** The simultaneous two-leg pattern is (12.2.2.1–7),
p. 508. On the rational normalized window $D$, the labels $2^j$ specialize
the translate formula to $\sum_j m_j m_{j+\ell}$ for input in $2^\ell D$.
In these copies only, the first decreasing unit-test difference in
(11.3.1.4), p. 494, is minus the off-identity indicator. The outside-$2$
input mask preserves the chosen copies, unlike the later literal mask
in (11.3.2.3), p. 495. Choosing these probabilities and changing the mask
are repairs, not consequences of the printed indentation or cutoff. The
Lean result checks the counting and trace mathematics, not a geometric
kernel descent from (11.3.2.2), pointwise diagonal regularity, or an
orbital evaluation. In particular it does not use Theorem 11.3.2.1,
pp. 495–496, on a below-one test.

**Evidence:** Independent `copy-statement-review` (`DmJHSdg`, inspected base
`20c4d6d47825b7d8f7456ef0aa0e7358a49a689f`, source review
`2c1802a8a60dc33591560259c6f82c160e15a136`, final statement review
`b81a0d7a32bfb300319f1b14c1a619eaa93ffee1`) checked the counting orientation,
Haar normalization, signs, and scope. The review used the pinned Markdown
and numbered layout extraction, not rendered pages. Owning Yah session
`01a20681-c84c-7800-81e4-b5411773b697` records the candidate diff, build,
joint-import signatures, axiom reports, and stale adoption decisions.
Recovery session `01a2068e-dbb2-7b6d-9d57-092f0e571fa0` restored the
Lean sources unchanged from `657036487bf6bfb5d33e7d7a67785fda65111686`;
its transcript records the exact replacement candidate, independent
statement review, checks, and adoption decision.

**Next inference:** At fixed $\rho$ prove $T_Y\to T_\infty$, the trace
of the same convolution with the terminal full weighted geometric
projection. Use `tendsto_rationalThetaWeightedEvenBand_projection` on
one annulus rank-one expansion with Fourier coefficients and windows
independent of $Y$. Project each input vector, keep the coefficientwise
summable bound, and pass to the limit in the trace series. This addresses
the below-one fixed-position limit that (11.2.1.8–10), p. 489, does not
supply. It does not exhaust position or identify $T_\infty$ with a zero
sum. Separately, the required transport to the regular diagonal and the
orbital and raw-local identifications in (12.5.1.1–4), pp. 519–520,
remain open. The model does not impose these copy weights on other lifts.

## Fixed-position convergence of the same global band trace

[`rationalThetaBand_trace_tendsto`](../../Proofs/Theorems/RationalThetaBandTraceDensity.lean)
fixes $\rho\in C_c(\mathbb R)$ and $\phi\in C_c^2(\mathbb R)$, and takes
any monotone cofinal sequence of real additive Fourier bands in the global
weighted rational even theta chart ($a$ arbitrary, $\alpha,s\ge 0$). With
$Q_n$ the band projectors and $P$ the full weighted theta projector, it
constructs one localized weighted convolution $A_\rho$ on the ambient
$L^2(dx)$. The basis traces of $A_\rho Q_n$ converge to the basis trace
of $A_\rho P$. The $L^2$ kernel formula determines the localized operator
uniquely up to a.e. representatives, so this is the same whole trace as
in the fixed-band density and copy split, by uniqueness of `HasSum`.

**Source and repair:** (11.2.1.8–10), p. 489, state the exhaustion order
and a fixed-position trace limit in $W^{s,2}$ with support at norm at
least one. The band inclusion cited there is (7.3.2.20), with its zero-mode
version (7.3.2.21), p. 356. Corollary C.3.5.5, pp. 702–703, treats a
dense exhaustion of the identity in its Hilbert space; it does not delete
the terminal projection on the ambient space. Proposition C.3.6.5,
pp. 705–706, permits a proper self-adjoint strong limit for the right
factor when the initial operator is already nuclear. The Lean repair
uses `tendsto_rationalThetaWeightedEvenBand_projection` in the desired
weighted norm, `exists_weightedAnnulus_window` for a single Fourier window
before projection, and `tendsto_windowKernel_trace` to sum the strongly
converging scalar terms using the same summable majorant. No assumption
on the sign of the log support is required. This is the after-projection
chart model, compare (10.4.1.12), p. 458, and the weighted Hilbert-Schmidt
kernel (10.4.3.48), p. 473. It is not an assertion that $M_\rho PA$ in
(10.4.1.6–7), p. 457, equals $M_\rho AP$. Range invariance would identify
the printed band compositions, not justify dropping the right $P$ in
the ambient limit.

**Evidence:** Independent Yah `trace-limit-statement` (`Lfrixhx`) reviewed
the exact endpoint, the two supporting interfaces, and the cited
manuscript dependencies at `b3c013c0f661e3ed459db26e8f7a2cfeb4acbd29`.
The source reading is provisional: Pinned Markdown and PDF layout, not
rendered pages. Owning session `01a20693-fe94-72ee-9f9f-a523d5c0785d`
contains the exact candidate diff, warnings-as-errors build, fresh joint
import with signatures and axiom reports, and adoption decision.

**Next inference:** For the below-one witness, prove the ambient trace
identity $\operatorname{Tr}(A_\rho)=\phi(0)\int\rho=0$ in this *same*
chart and use $P+(1-P)=1$ to transfer the terminal geometric trace to
minus the complementary trace at fixed $\rho$. The window series at the
identity uses $\sum_k\widehat\phi_{\mathrm{per}}(k)=\phi(0)$ and cancellation
of $W$ against $W^{-1}$ on the output support. This prepares, but does
not provide, position exhaustion: It still needs a summable expansion
for the unlocalized convolution on the complementary projection in the
same norm, and an identification of that complement and its trace with the
full-order interior jet sum. See the [reviewed complementary trace
argument](trace-spectral-strip-q.md#convolution-after-projection). The
transport to the regular diagonal and necessity of the modeled local
identification in (12.5.1.1–4), pp. 519–520, remain separate obligations.

## Ambient and complementary traces at fixed position

[`rationalTheta_fixedPosition_trace_split`](../../Proofs/Theorems/RationalThetaBandTraceDensity.lean)
uses the very same weighted $L^2(dx)$ convolution $A_\rho$ and full theta
projector $P$ as `rationalThetaBand_trace_tendsto`. For any Hilbert basis,
its ambient basis trace is $C_\rho=\varphi(0)\int\rho(x)\,dx$. With the
terminal $\operatorname{Tr}(A_\rho P)=T_\infty$ supplied by the preceding
result, the complementary basis trace is
$\operatorname{Tr}(A_\rho(1-P))=C_\rho-T_\infty$. In particular the
below-one test gives $-T_\infty$. The operator is identified by its
integral formula a.e. for each input vector, not by choosing an a.e.
kernel representative on the diagonal.

**Source and repair:** Theorem 9.3.3.5(2), p. 429, uses a smooth compact
class test and a smooth position cutoff; (9.3.3.15–20), p. 431, give the
identity-value diagonal integral. Remark 10.4.1.4, p. 457, supplies the
complement relation; (10.4.2.2–3), pp. 458–459, split the trace with
projections to the left of convolution. Here the band limit needs the
right-projection order of (10.4.1.12–13), p. 458, in the normalized
rational log chart, with a continuous compact position cutoff and a
$C_c^2$ log test. `weightedAnnulus_ambient_trace` uses the same Fourier
window construction as the band limit: Each periodic mode has modulus
one, the input window covers the output support, and the two weights
cancel in the rank-one diagonal. Summing the Fourier coefficients at
zero gives $\varphi(0)$. Subtraction of convergent basis diagonals then
supplies the split, without claiming the two projection orders agree
at fixed position and without using a Hilbert-Schmidt kernel as a
trace formula.

**Evidence:** Independent Yah `ambient-trace-review` (`XewzjSE`, source
base `08fd2e8f3d0e183df048b670f49d5da031ab3675`) reviewed both fixed
statements and the sign, operator order, and manuscript dependencies
from pinned Markdown and PDF layout extraction. The source reading
remains provisional, not a rendered-page verification. Owning session
`01a2069a-2698-74fe-a635-b149f9331696` records the candidate provenance,
exact build, joint-import signature and axiom checks, and adoption.

**Next inference:** Position exhaustion here requires the *unlocalized*
$A(1-P)$ in the same norm to admit a summable rank-one expansion and have
trace equal to the full-order open-strip sum (compare (10.4.2.20), p. 463).
The [reviewed jet-model argument](trace-spectral-strip-q.md#convolution-after-projection)
constructs the trace for the complement of the common jet kernel, not
for an arbitrary projection. `rationalThetaWeightedLog_closure_subset_ker`
only supplies the forward inclusion. To work on the reverse inclusion
at $a=1/2$, $s=2r$, and the common full-measure set of $0<\alpha<1/2$, a
runnable independent substep is the [Gaussian-division moment repair](trace-theta-density-q.md#gaussian-division-and-compact-theta-approximation):
For fixed smooth compact $\beta$ normalized by $\int e^{x/2}\beta(x)dx=1$,
show $m e^{-L/2}\beta(\cdot-L)$ has moment $m$ and tends to zero in the
weighted derivative norm through order $2r$ (or any fixed finite order),
using the factor $e^{-(1/2-\alpha)L}$ times a polynomial. This allows
moment-zero approximants without asserting continuity of that moment
in the strip norm. The quotient bounds and their weighted Fourier
approximation, the complementary trace-class and zero-sum identification
in Lean, transport to the regular diagonal, and necessity of the modeled
geometric identification remain separate.
