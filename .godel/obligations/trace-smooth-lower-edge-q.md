# The lower edges of the real scalar cutoff

**Source qualification.** The exact joint-limit rates after
(12.4.1.28), p. 519, and parts of the cutoff wording below remain
provisional: The layout and manuscript text agree, but independent
pixel readings did not resolve the entire clauses. The comparison
uses those rates and distinguishes the two quoted shapes.

**Verdict on the repaired radial quotient, not on a trace.** Over
$F=\mathbb Q$, $S=\{\infty\}$, Step II's upper-indicator shapes leave
no lower edges. For bounded smoothenings that differ from those
indicators only in the specified-width upper bands, the two rate
conditions give the same scalar limit as (12.4.1.22), p. 518.
Using the unmodified annuli cited in the proof instead gives a nonzero
lower-edge correction, even with both cutoff parameters equal and
both stipulated $\varepsilon$ conditions. The independent-endpoint
proposal on p. 514 n. 2 changes the cutoff and does not by itself make
the lower edge negligible. These are distinct readings, not a
counterexample to the explicit upper-only scalar.

## Printed inputs and the test

- Step II, p. 516, calls each profile an $\varepsilon$-smoothening of
  an indicator of $|x|_{F,S}\le\lambda'$ (Fourier) or
  $|x|_{F,S}\le\lambda$ (position). The position weight
  $\rho_{\lambda,-}(x)$ is in (12.4.1.12), p. 517, and the Fourier
  weight $\rho_{\lambda',-}(u)$ in (12.4.1.15), also p. 517.
  In (12.4.1.22), p. 518, the position range in the stated equality
  is $(0,\lambda]$ and the Fourier range is $|u|_{F,S}\le\lambda'$.
- The opening of the proof on p. 514 cites Definition 9.3.3.1,
  p. 427. Its radiality is inherited from the [circle-compression
  note](trace-circle-compression-qi.md#chapter-12-interface).
  Clauses (4)–(6) require inversion symmetry, support over
  $[1/\Lambda,\Lambda]$, and value one over
  $[1/\Lambda+\varepsilon,\Lambda-\varepsilon]$. Such a cutoff is
  not an upper-indicator smoothing equal to one near zero.
  Definition 9.3.3.3, p. 428, separately defines the sharp one-sided
  factors: The minus label denotes the upper indicator. This last
  cross-reference is extraction-only and does not define the smooth
  upper-only factors.
- The limit after (12.4.1.28), p. 519, sends $\lambda,\lambda'$ to
  infinity with $\varepsilon\lambda=o(1)$ and
  $\varepsilon\lambda'=o(1)$. This states a joint limit, not an
  iterated one. Page 514 n. 2 asks to change the definition and smooth
  $\mathbf 1_{[1/\lambda'',\lambda]}$ with $\lambda''$ not tied to
  $\lambda$, then study (12.4.1.23) as $\lambda',\lambda''\to\infty$.
  The footnote's max has arguments $|w|_{F,S}/\lambda'$ and
  $1/\lambda''$; it prescribes no relative rate and does not assert
  that the limit is unchanged. For a position annulus with a
  one-sided Fourier cutoff, the corrected volume bracket is
  $\log\lambda-\log\max\{|w|/\lambda',1/\lambda''\}$ on the old band,
  not a replacement of just one term in the old bracket.

The [real coefficient audit](trace-real-prime-q.md#the-chapter-12-real-coefficient)
maps the hypotheses of Theorem 12.4.1.1, p. 514, and supplies the
rendered measures and two-sign interface in (12.4.1.17)–(21) and
(12.4.1.24), p. 518. The theorem hypotheses apply to any nonzero
$0\le h\in C_c^\infty((2,3))$ as a profile of the norm on
$C_{\mathbb Q}$. The $S$-integer ring is
$\mathbb Z$, no finite place ramifies, and a norm profile is invariant
under the required finite units. It is a compactly supported smooth
test and vanishes at norm one. There is no Mellin-moment hypothesis in
Theorem 12.4.1.1. On the project domain $E^*=\mathbb R_{>0}$, the
quotient Haar is $ds/s$ with norm-one volume one. The positive-ray
lift periodizes by counting both signs to $h(|y|)$; hence the sum of
the two additive tests is

$$
U(z)=|1+z|^{-1/2}h(|1+z|^{-1}).
$$

Extend by zero at $-1$. This is smooth, nonnegative, nonzero, and
supported in $1/3<|1+z|<1/2$, in particular away from $0$.

## The full signed scalar comparison

Use the [radial change of variables and endpoint averaging](trace-geometric.md#smooth-radial-bands-on-the-extended-domain).
For $K>0$ let $L_K(r)=\log_+(K/r)$ for $r>0$, let $L_0=0$, and put
$J(K)=\int_{\mathbb R} L_K(|w|)\widehat U(w)\,dw$. The value at
$w=0$ is immaterial. For sharp position $[A,B]$ and frequency
$[C,D]$ the full band gives

$$
J(BD)-J(AD)-J(BC)+J(AC).
$$

In fact, integrate $ds/s$ over $[A,B]\cap[|w|/D,|w|/C]$, or
subtract the two one-sided frequency ranges first. Use $A=0$ or
$C=0$ for an absent edge. For the smooth monotone edges below,
average the whole expression with endpoints between the ends of
their transitions. This involves an absolutely integrable scalar at
each cutoff, since the transform is Schwartz and $L_K$ is integrable
on the real line. There is no infinite unit sum. For $0\le K\le K'$,
$L_{K'}-L_K\ge0$ and $\int_{\mathbb R} L_K(|w|)\,dw=2K$, so

$$
|J(K')-J(K)|\le 2\|\widehat U\|_\infty(K'-K).
$$

In particular $J(0)=0$ and endpoint convergence at bounded scale
suffices. For strict positivity at fixed $K>0$, use Fubini and evenness
of $L_K$. The real spatial kernel for $z\ne0$ is

$$
2\int_0^K \log(K/w)\cos(2\pi wz)\,dw
=\frac{\operatorname{Si}(2\pi K|z|)}{\pi |z|},\qquad
\operatorname{Si}(t)=\int_0^t\frac{\sin v}{v}\,dv.
$$

Integration by parts gives this identity, with the endpoint at zero
vanishing as $w\log(K/w)\to0$. Each positive full sine lobe outweighs
the following negative full lobe, by translating the latter by $-\pi$
and using the strictly decreasing $1/v$. A partial negative lobe
cannot cost more than its full lobe. Hence $\operatorname{Si}(t)>0$
for $t>0$, and the kernel is positive also at zero, where it is $2K$.
Fubini applies by $\|U\|_1\int L_K<\infty$, so $J(K)$ is real and
strictly positive. The [accepted Lean limit](trace-real-prime-q.md#lean-checked-sharp-limit-without-a-support-gap)
gives $J(K)\to \tfrac12\int U(z)/|z|\,dz$ at infinity, not the
finite-scale positivity or cutoff averaging.

**Upper-only reading.** For bounded smoothings in $[0,1]$ which
agree with the upper indicators outside the bands of width
$\varepsilon$ on either side of the upper endpoints $B=\lambda$,
$D=\lambda'$ (the quantitative upper-only interpretation used here),
the smoothed radial weight is sandwiched between
$L_{(B-\varepsilon)(D-\varepsilon)}$ and
$L_{(B+\varepsilon)(D+\varepsilon)}$. The difference from $J(BD)$ is
bounded by $4\|\widehat U\|_\infty\varepsilon(B+D)$, hence is $o(1)$
under the printed conditions. Monotonicity is not needed here. This
supports an asymptotic replacement, not an equality at finite cutoffs.
It does not show that the upper-only position multiplier maps to
$\mathcal S_{00}$ as asserted in Step II; see the [range obstruction](trace-polar-free-q.md#the-literal-upper-position-cutoff-does-not-supply-the-range).

**Unmodified Definition 9.3.3.1.** Set $\lambda=\lambda'=T\to\infty$,
$\varepsilon=T^{-3}$, $\delta=\varepsilon/2$, and use the same radial
profile in both slots:

$$
p_T(s)=\chi((T-s)/\delta)\chi((T-s^{-1})/\delta),\qquad s>0,
$$

where $\chi$ is smooth and nondecreasing, zero on $(-\infty,0]$ and
one on $[1,\infty)$. It extends evenly by zero near the real origin.
This is real, nonnegative, bounded with supremum one, radial, smooth,
and invariant under inversion. It has support in $[1/T,T]$ and its
plateau $[(T-\delta)^{-1},T-\delta]$ contains
$[1/T+\varepsilon,T-\varepsilon]$ for large $T$. The definition's
strict inequalities and both little-$o$ conditions hold. The lower
and upper transitions of this profile are disjoint and monotone, so
one can average sharp endpoints $A,C$ in $[1/T,(T-\delta)^{-1}]$ and
$B,D$ in $[T-\delta,T]$. Uniformly over these intervals,
$BD-T^2\to0$, $AD,BC\to1$, and $AC\to0$. The smoothed scalar minus
(12.4.1.22) therefore tends to $-2J(1)<0$, **including** the mixed
lower-edge term $+J(AC)$. Thus the rates printed after (12.4.1.28) do
not suffice if the cited symmetric annular definition is enforced.
This family does not obey Step II's explicit upper-only shapes. In
particular, using the original annular definition for both weights is
not evidence that the printed Step II weights have lower edges.

**Changed position cutoff of p. 514 n. 2.** Leave the Fourier shape
upper-only and choose $\lambda''=T$, $\lambda=T^2$,
$\lambda'=kT$ with any fixed $k>0$, and $\varepsilon=T^{-3}$.
Use smooth monotone transitions of width $\varepsilon/2$ wholly
inside the corresponding nominal band: Lower position begins at
$1/\lambda''$, upper position ends at $\lambda$, and upper Fourier
ends at $\lambda'$. This choice is a project realization of the
proposed change, not an instance of the original symmetric definition.
All parameters tend to their stipulated limits, $BD-\lambda\lambda'\to0$,
and $AD\to k$ uniformly. The difference from (12.4.1.22) tends to
$-J(k)<0$. Thus the proposed joint exhaustion without a relative rate
does not recover the upper-only limit. Requiring
$\lambda'/\lambda''\to0$ together with $\varepsilon\lambda'=o(1)$
suffices for this single lower edge with transition width at most
$\varepsilon$, by $A_+D_+\to0$. If a Fourier lower edge is retained,
its cross-product needs separate control.

## Review and continuation

**Source evidence, by clause.** Read the [pinned edition](../sources/masullo/README.md).
In Yah `01a205fe-b46d-789a-bf49-2a6520b4e0cc`, independent pixel
reader `aieDEPK` resolved the two upper-bound inequalities of Step II,
p. 516, and `NybGmDI` separately resolved the primed first endpoint and
unprimed second endpoint. The exact smoothening qualifier and the
$\mathcal S_{00}$ codomain are supported by extraction, not independently
resolved from the pixels. In (12.4.1.12) and (12.4.1.15), p. 517,
`aieDEPK` saw a factor evaluated at the position argument and a
factor evaluated at $u$, each with a minus in its subscript; the
exact symbol names and parameter subscripts use the extraction.
For (12.4.1.22), p. 518, `aieDEPK` saw the position interval beginning
at zero and `NybGmDI` saw the upper frequency inequality with a prime.
The exact preceding equality clause remains extraction-supported.

For Definition 9.3.3.1, p. 427, the radiality clause (2) is inherited
rendered evidence, not a new check. `aieDEPK` independently read the
inversion exponent in (4), the reciprocal interval in (5), and the
inward plus and minus in (6); the exact plateau symbols and the other
bounds and smoothness conditions are supported by extraction. For
p. 519 after (12.4.1.28), the exact products and joint-limit clause
remain provisional notwithstanding readable fragments. For p. 514
n. 2, `aieDEPK` saw the contrast of one-sided and reciprocal ranges
and `NybGmDI` saw the double prime. The exact logarithm, convergence
request, and lack of a relative-rate condition are based on the
full extracted footnote, not certified by that pixel review.

**Mathematical review.** `bcczHXU` in the same Yah session checked the
upper-only error bound, the annular signed correction including its
mixed term, the single lower-edge mechanism in the proposed change,
and the positivity argument on the two-sign test. This is independent
mathematical review under the quoted source readings, not independent
verification of their exact wording. The nominal upper product in the
changed family is $\lambda\lambda'=kT^3$: The absolute error bound
there is $O(\varepsilon(\lambda+\lambda'))=o(1)$, not an approximation
to $T^2$.

That comparison is informal. It controls the
scalar **after** extending the radial domain. The use of the literal
$E_{S,0}$ in (12.4.1.23), the identification of the geometrical operator
and the global $S$-piece, and the two Mellin corrections are separate
premises. In particular a replacement giving the correct scalar limit
need not give the trace of the actual local projection. The
[existing projection comparison](trace-joint-local-q.md) already
exhibits a defect even for position lower edges tending to zero in
bandwidth units and upper-only Fourier multipliers.

**Lean-checked finite-band sign.** [RealLogBandPositive](../../Proofs/Lemmas/RealLogBandPositive.lean)
proves `Masullo.real_log_band_cos_pos` for every real cosine argument
and `Masullo.real_log_fourier_sharp_pos` for every $K>0$ and real
$v\in L^1(\mathbb R)$ with $v\ge0$ almost everywhere and $\int v>0$:

$$
\operatorname{Re}\int_{|w|\le K}(\log K-\log|w|)\widehat v(w)\,dw>0.
$$

Lean takes the Fourier transform of the complex coercion of $v$.
Unlike `real_log_fourier_sharp_tendsto`, this needs neither continuity,
vanishing at zero, a support gap, nor integrability of $\widehat v$
over the whole line. The proof uses the positive integral of the
continuous nonnegative kernel $\tfrac12\operatorname{sinc}^2(aw/2)$
in the cosine primitive, then exchanges the two $L^1$ inputs to the
Fourier pairing. For the two-sign test $U$ above, smooth compact support
and nonzero nonnegativity give the hypotheses. The joint-import check
also identifies the band with `realSharpCutScalar` in the accepted
[sharp lower-edge calculation](trace-real-prime-q.md#lean-checked-path-dependence-of-the-retained-position-edge)
and checks the negative real part of $-2J(1)$. This checks the sign of
the correction, not the smoothing estimate that produces it.

The rendered symmetric band (12.4.1.24), p. 518, and the two-sign
counting and quotient normalization of (12.4.1.17)–(21) are inherited
from the [real coefficient audit](trace-real-prime-q.md#the-chapter-12-real-coefficient),
not reread. No smoothing wording or joint-limit rate is a hypothesis
of the Lean result. The exact qualifiers of the smoothing comparison
above keep their separate source status. Yah
`01a20611-2118-7d6d-b406-1e305f20e5ea` houses the independent statement
and applicability review (`juHIOEc`, reviewed base
`0ae6cd4b47baded506e8c8449a7ce74ce28485e9`) and the owning build,
joint-import signatures, axiom report, and candidate disposition.

### Lean-checked finite two-annulus scalar

On the repaired positive radial quotient, for $0<A\le B$, $0<C\le D$,
and $u\in L^1(\mathbb R;\mathbb C)$,
[RealSharpLowerEdges](../../Proofs/Props/RealSharpLowerEdges.lean)
defines `realTwoAnnuliScalar` and proves `real_two_annuli_scalar_eq`:

$$
\int_{\mathbb R}\left(\int_{[A,B]\cap[|w|/D,|w|/C]}\frac{ds}{s}\right)
  \widehat u(w)\,dw
= J(BD)-J(AD)-J(BC)+J(AC),\qquad J(K)=\texttt{realSharpCutScalar}\ u\ K.
$$

Subtract the two nested upper-band volumes, dropping just the radial
boundary $s=|w|/C$, and use `real_position_band_radial_volume` at $D$
and $C$ off the null frequency $w=0$. The four truncated log weights
are integrable and $\widehat u$ is bounded, so the subtraction is of
absolutely integrable pairings. Unlike `real_position_band_scalar_eq`,
this does not require global integrability of $\widehat u$ or
$\log|\cdot|\,\widehat u$. Both degenerate bands are allowed. In a
joint import, the existing `real_log_profile_two_annuli_erase` transfers
to the actual integral by eventual equality: Use eventual endpoint
positivity and order, a smooth compactly supported log profile with
$f(0)=0$, and the four product limits of that theorem. The finite
identity itself needs none of the profile or limit assumptions.

**Source and review.** This closes the finite integral identification
in the informal comparison above. It inherits the rendered scalar
band (12.4.1.24), p. 518, and the both-sign sum and counting-quotient
normalization of (12.4.1.17)–(21) from the
[real coefficient audit](trace-real-prime-q.md#the-chapter-12-real-coefficient).
It does not reread the footnote, verify any of the smoothing wording
or rates, or identify the radial extension with the literal norm-one
domain. The independent exact-statement and applicability review at
`fa6d75e6321d814e967cf00c03887c32fffa7765` (`WZdYcsm`) and the owning
build, joint-import signatures, axiom report, and adoption against
the full candidate ID are recorded in Yah
`01a2061d-6bc7-725a-b079-14f4d6c12d36`.

### Lean-checked perturbation of the sharp scalar endpoints

For $u\in L^1(\mathbb R;\mathbb C)$ and $0<K\le K'$, the theorem
`norm_realSharpCutScalar_sub_le` in
[RealSharpLowerEdges](../../Proofs/Props/RealSharpLowerEdges.lean) proves

$$
|J(K')-J(K)|\le 2(K'-K)\int_{\mathbb R}|u(x)|\,dx.
$$

Each cutoff weight has integral $2K$ by integrating the real logarithm
on $[-K,K]$. At $D=1$, `real_position_band_radial_volume` identifies
the difference of the weights off $w=0$ with a nonnegative radial
integral. The difference therefore has mass $2(K'-K)$. Finite pairing
integrability and the pointwise Fourier bound then give the estimate,
including $K'=K$, without global integrability of $\widehat u$ or
$\log|\cdot|\widehat u$. Reversing the endpoints when necessary, the
triangle inequality controls the four-term scalar above by twice the
$L^1$ norm times the sum of the four absolute product changes. That
last corollary is not a separate Lean declaration.

**Source and review.** This is an estimate on the repaired positive
radial quotient, not a printed claim. The band (12.4.1.24), p. 518,
and the two-sign sum and counting-quotient normalization of
(12.4.1.17)–(21) are inherited rendered evidence from the
[real coefficient audit](trace-real-prime-q.md#the-chapter-12-real-coefficient),
not reread. Independent exact-statement review (`QkhXDEC`, reviewed
base `0c66aa8549fbe74761d9ddd15b019e4d1a704048`) checked applicability
and the mathematical reduction. Its transcript and the owning build,
fresh joint-import signatures, axiom report, and candidate disposition
are in Yah `01a20628-35f8-7cc3-84eb-2ea8c1169911`.

### Lean-checked pointwise radial weight sandwich

[RealRadialWeightSandwich](../../Proofs/Props/RealRadialWeightSandwich.lean)
proves `real_radial_weight_sandwich` for real profiles $p,q$ measurable
on $s>0$ (their zero extensions are measurable). At every $s>0$,
bracket $p$ by the upper indicators with positive endpoints $B_-\le B_+$,
and $q$ by those with positive endpoints $D_-\le D_+$. For every $r>0$,
the weighted product is absolutely integrable and its integral satisfies

$$
L_{B_-D_-}(r)\ \le\ W(r)=\int_0^\infty p(s)q(r/s)\,\frac{ds}{s}
\ \le\ L_{B_+D_+}(r),\qquad L_K(r)=\max(0,\log(K/r)).
$$

The lower indicators force nonnegativity on the entire positive ray.
On that ray the product of the two sharp indicators is the indicator
of $[r/D,B]$. The upper band is bounded away from zero when nonempty,
and gives the zero majorant when empty. The sharp integral follows
from `real_position_band_radial_volume` with $A=r/D$ when $r\le BD$:
The lower-product log term is zero. When $r>BD$ the band is empty.
This compares the actual profile product, not just two sharp pairings,
and needs no smoothness, monotonicity, or Fourier integrability.

**Source and review.** The theorem takes the brackets as project
hypotheses on the repaired positive radial quotient. It does not use
the norm-one slice of (A.2.4.5), p. 554, alone. The
[clause-specific review](#review-and-continuation) supplies inherited
rendered evidence for the two upper bounds of Step II, p. 516, and
the sharp ranges in (12.4.1.22), p. 518; the exact smoothening qualifier
and preceding equality remain extraction-supported. For (12.4.1.12)
and (12.4.1.15), p. 517, the arguments and minus subscripts have
rendered evidence, while exact factor names and parameter subscripts
are extraction-supported. The [real coefficient audit](trace-real-prime-q.md#the-chapter-12-real-coefficient)
supplies the rendered band in (12.4.1.24), p. 518, and the rational
quotient normalization. The cited Definition 9.3.3.1, p. 427, gives an
annular rather than an upper-only cutoff; see the clause-specific
review for the evidence by clause. None of these clauses supplies the
project brackets. No new manuscript reading is used. Independent
exact-source review (`jEvVJoN`, Yah `01a20647-5156-773b-84a4-9ab7a31e49fd`,
base `a388a0824177684ea01ff4dddc2d6f085d74e33f`) checked the hypotheses
and the sharp-band reduction. The same Yah records the owning build,
fresh joint-import signature and axioms, and candidate disposition.

### Lean-checked measurability of the outer radial weight

`Masullo.measurable_real_radial_weight` in
[RealRadialWeightSandwich](../../Proofs/Props/RealRadialWeightSandwich.lean)
assumes only that the zero extensions of $p,q:\mathbb R\to\mathbb R$
from $(0,\infty)$ are Borel measurable. The function equal to $W(|w|)$
for $w\ne0$ and to zero at $w=0$ is Borel measurable. On $(w,s)$,
the product of the two extended profiles at $s$ and $|w|/s$, times
$s^{-1}$, is jointly measurable. Mathlib's
`StronglyMeasurable.integral_prod_right'` integrates in $s$ against
Lebesgue measure restricted to $(0,\infty)$. Off zero the integrand
agrees on that ray with the one in the sandwich at $r=|w|$; at zero
the extended second profile vanishes. No brackets, smoothness, or
slice integrability enter this proof. The conclusion concerns the total
Bochner integral and does not give absolute convergence without the
separate hypotheses of the sandwich.

**Source and review.** This is a project interface on the repaired
positive radial domain, not a deduction of the printed smooth-to-sharp
step. The [clause-specific review](#review-and-continuation) supplies
the inherited rendered sharp ranges in (12.4.1.22), p. 518; the exact
preceding equality is extraction-supported and unused. The
[real coefficient audit](trace-real-prime-q.md#the-chapter-12-real-coefficient)
supplies the inherited rendered band in (12.4.1.24), p. 518. No new
manuscript reading was needed. Independent exact-source statement
review (Yah `01a20652-75ff-7c4f-8017-0a6f9bb3a358`, agent `XfYfowB`,
reviewed revision `b5269d20c97d233c924b199d6670244f012036f7`)
checked this scope and the product integration reduction. The same Yah
records the owning build, fresh joint-import signatures and axioms,
and candidate disposition.

### Lean-checked finite outer pairing

[RealRadialWeightSandwich](../../Proofs/Props/RealRadialWeightSandwich.lean)
proves `Masullo.integrable_real_radial_pairing_and_norm_sub_le` under
`real_radial_weight_sandwich`'s positive upper-indicator brackets and
measurability hypotheses. Write $K_-=B_-D_-$, $K_+=B_+D_+$, and let
$W(w)$ be the zero extension at $w=0$ of the paired profile weight at
$r=|w|$. For $u\in L^1(\mathbb R;\mathbb C)$ and $K_-\le K\le K_+$,
the integrand $W(w)\widehat u(w)$ is absolutely integrable, and

$$
\left|\int_{\mathbb R} W(w)\widehat u(w)\,dw-J(K)\right|
\le 2(K_+-K_-)\|u\|_1,
\qquad J(K)=\texttt{realSharpCutScalar}\ u\ K.
$$

The reusable endpoint
`Masullo.integrable_mul_fourier_and_norm_sub_le_of_sharp_cut_brackets`
in [RealSharpLowerEdges](../../Proofs/Props/RealSharpLowerEdges.lean)
needs only that the real weight $W$ is a.e. strongly measurable and
lies a.e. between the sharp log weights at positive ordered endpoints.
The upper weight controls absolute integrability. Off the null
origin the sharp weight at $K$ is also in this interval, so the
absolute weight error is bounded by the difference of the two sharp
weights in the same $w$ coordinate. The proof reuses their private
integrability and mass calculations, giving envelope mass
$2(K_+-K_-)$, and multiplies by $\|\widehat u\|_\infty\le\|u\|_1$.
The original sharp Lipschitz estimate is now its endpoint
specialization, with unchanged hypotheses. No global $L^1$ assumption
on $\widehat u$, profile smoothness, or profile monotonicity is needed.

**Source and review.** This is a finite pairing on the repaired
positive radial domain. The [clause-specific review](#review-and-continuation)
supplies inherited rendered evidence for the sharp ranges in
(12.4.1.22), p. 518; the preceding smooth-to-sharp equality is
extraction-supported and unused. The
[real coefficient audit](trace-real-prime-q.md#the-chapter-12-real-coefficient)
supplies inherited rendered evidence for the band in (12.4.1.24),
p. 518. Neither supplies the project brackets. No manuscript passage
was reread. Independent exact-source review in Yah
`01a2065a-ccba-7885-83d7-d3e838c1ab62`, agent `bXKcOxk`, checked
both statements and the use of the accepted definitions and source
notes at `61dce3be3e3f28c1c140e6454fd2a630cb6895fc`. The a.e.
bracket and same-coordinate envelope were checked mathematically;
elaboration was the owner's check, not the reader's. The same Yah
records the candidate, owning builds, fresh joint-import signatures,
axioms, and disposition.

### Lean-checked conditional radial cutoff limit

`Masullo.tendsto_integral_mul_fourier_of_sharp_cut_brackets` in
[RealSharpLowerEdges](../../Proofs/Props/RealSharpLowerEdges.lean)
fixes an additive $u\in L^1(\mathbb R;\mathbb C)$ along an arbitrary
filter. Assume eventual a.e. strong measurability of the real $W_i$,
a.e. sharp log brackets, and $0<K_{-,i}\le K_i\le K_{+,i}$. If
$K_{+,i}-K_{-,i}\to0$ and $J(K_i)\to L$, then
$\int W_i(w)\widehat u(w)\,dw\to L$. The finite bound above squeezes
the difference to zero, with no hypothesis that $K_i$ diverges or
that $\widehat u$ is globally integrable. The same finite lemma gives
absolute integrability eventually.

`Masullo.real_log_profile_radial_pairing_tendsto` in
[RealRadialWeightSandwich](../../Proofs/Props/RealRadialWeightSandwich.lean)
applies this to the actual profile integral at $r=|w|$, extended by
zero at $w=0$. Its hypotheses are eventual measurable positive-ray
extensions by zero, positive ordered upper-indicator brackets for
both profiles, and $B_-D_-\le K_i\le B_+D_+$, together with
$B_+D_+-B_-D_-\to0$ and $K_i\to+\infty$. The positive-ray profiles
need neither smoothness nor monotonicity. For smooth compactly
supported log $f$ with $f(0)=0$, the accepted additive test theorem
gives integrability of $u=\texttt{realLogProfileAdditive}(t\mapsto f(-t))$,
and the accepted sharp theorem gives $L=\tfrac12\int u(z)/|z|\,dz$.
No support gap at norm one or Mellin moment is assumed.

**Source and review.** This is a conditional transfer on the repaired
positive radial quotient. The [clause-specific review](#review-and-continuation)
supplies inherited rendered evidence for the sharp ranges in
(12.4.1.22), p. 518; the smooth-to-sharp equality is extraction-only
and unused. For (12.4.1.12) and (12.4.1.15), p. 517, that review saw
the retained arguments and minus subscripts, not the exact names or
parameter subscripts. The [real coefficient audit](trace-real-prime-q.md#the-chapter-12-real-coefficient)
supplies the rendered band in (12.4.1.24), p. 518, and the both-sign
and counting normalization from (12.4.1.17)–(21). None supplies the
assumed brackets or width convergence. The rate clause after
(12.4.1.28), p. 519, remains provisional and is not a premise. No
passages were reread. The projected trace, literal norm-one domain,
and Mellin identification are not conclusions. Independent exact-source
review in Yah `01a2066f-054b-7e28-a138-ed80909bf1ff`, agent `puwWIxv`,
checked the statements, finite estimate, profile reduction, and sharp
real normalization at `17d3317e0ad178b1de22eac1ef5e591e93649223`.
The same Yah records the owning build, fresh joint-import signatures,
axiom reports, and disposition.

**Next bounded check, formalization only.** For project annular
profiles written as differences of two upper-bracketed profiles in
each slot, distribute the product under the same $ds/s$ integral and
then the outer Fourier pairing. The transfer above (general $u$)
already gives the four constituent limits when each product width
vanishes and the corresponding sharp limit is known. The missing
step is the signed sum for the *actual smoothed annular pairing*,
with both integral linearity obligations discharged by the accepted
sandwich and finite pairing. `real_two_annuli_scalar_eq` already
gives the signed sum for the *sharp* bands, not this splitting. This
would formalize the smoothing component of the annular correction
above, without requiring that the printed profiles admit the
decomposition. For Definition 9.3.3.1, p. 427, inherit the rendered
radiality, inversion exponent, reciprocal interval, and inward edge
signs from the [clause-specific review](#review-and-continuation);
the exact plateau symbols and remaining bounds are extraction-only.
The sharp ranges and band have the separate inherited evidence cited
above. Choosing or identifying the actual manuscript profiles and
checking their cross-product limits remain separate premises.
