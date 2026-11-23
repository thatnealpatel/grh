# ATTEMPTED: Full Masullo GRH, tested horizontal contour edges

**Original accepted evidence:** `7f6a93dc8c9307b575d9755d4a5360adc9288115`.
**Target:** Every nontrivial Hecke zero of every continuous unitary
idele-class character over every number field, including ramified
characters, has real part $1/2$. The preserved opening note gives the
inherited rendered scope review and keeps the separate multiplicity and
higher-rank claims out of scope. Classical RH for `riemannZeta` was not
attempted.

**Close:** Synthesis ended the attempt after pass 1. Pass 1 met the
opening stopping condition for the horizontal prerequisite. Full
Masullo GRH is neither proved nor refuted, and no further pass was run.

## Admission at the evidence pin

**Classical RH was declined.** `Proofs/Theorems/RationalIdeleRadialExplicitFormula.lean:61–75`
gives the normalized rational quotient-Haar formula with the full-order
zero sum and both polar Mellin moments. It supplies only one side of the
same-test comparison: `Proofs/Props/ZetaTestSumComparison.lean:25–39,78–110`
needs one order-dominated, closed-strip-supported weight family per
width, agreeing on every smooth compact positive-log mass-zero test,
at arbitrarily small positive widths. The fixed-width open-strip
identity already requires that no zero be omitted, including on the
boundary (`Proofs/Theorems/RationalRadialStripTrace.lean:102–160`). The
prime-two results exclude specific lifts, not every lift; the lower-edge
scalar cutoff comparison does not identify a global diagonal. No
specified independent Haar comparison retains the terminal right
projection, orbital term, and both Mellin subtractions.

**Full GRH was selected for a bounded Lean prerequisite.** The accepted
`Proofs/Theorems/IdeleClassGaussianHorizontalCount.lean:41–63` supplies
the same continuation's entire cleared numerator with a quadratic strip
bound, exponential center lower bound, full-order count on the closed
radius-five disk, and common separation at both edges. The moving-disk
estimate in `Proofs/Lemmas/AnalyticGoodHeightDisk.lean:241–247` and the
compact-log Mellin decay lemma make a distinct runnable check possible:
Transfer the bound from the numerator to the completed function itself
before applying the tested horizontal limit. The prior separation
landing `8f59df9e67ff4d6420e26df0c98b0c3f8fa01109` did not do this transfer.
Neither the mod-3 exhaustion nor the all-field, globally trivial-character
explicit formula answers it at arbitrary-character scope. The Main and
Companion records reviewed at intake did not report this check.

## Pass 1 (LEAN): Common quadratic bounds and both signed limits

`Masullo.exists_completedHeckeEulerProduct_gaussianContinuation_tested_horizontal`
(`Proofs/Theorems/IdeleClassGaussianTestedHorizontal.lean:45–67`) concerns
the same meromorphic Gaussian continuation $L$ that agrees with the
actual completed Hecke Euler product on $\Re s>1$. It retains the
continuation's measurable and Borel instances, a norm-one idele
representative for each ideal class satisfying the required class
identity, and unitarity of the continuous character. It imposes no
unramified restriction and assumes neither a functional equation nor
zero location. There are a single $D>0$ and sequence $T_n>\max(n,|\lambda|+1)$,
where $\lambda$ is the norm frequency, independent of the test. On both
closed horizontal edges $z=\sigma\pm iT_n$, $-1\leq\sigma\leq2$, it proves
$L(z)\ne0$ and $|L'(z)/L(z)|\leq D(1+T_n)^2$. It uses this bound and
inverse-cubic Mellin decay to prove that, for every smooth compactly
supported log profile $g$, both complex integrals
$\int_{-1}^2 (\operatorname{compactLogMellin}g)(\sigma\pm iT_n)
(L'/L)(\sigma\pm iT_n)\,d\sigma$ tend to zero. Reversing either orientation
negates its integral and does not change the limit.

**Contributions and failures.** `ImKojqa` supplied
`Masullo.exists_completedHeckeEulerProduct_gaussianContinuation_horizontal_logDeriv`
(`Proofs/Theorems/IdeleClassGaussianHorizontalLogDeriv.lean:90–107`,
output `835e4abb67e4d2d79630731009fd992535e232e8`). It applies the
moving-disk estimate to the same entire $H$, uses separation to exclude
$H(z)=0$, and transfers the bound and nonvanishing to $L$ using
$H(z)=(z-1+i\lambda)(z+i\lambda)L(z)$. The proof subtracts both
$1/(z+i\lambda)$ and $1/(z-1+i\lambda)$ from $H'/H$ away from the two
translated points. `YIutGbN` reviewed the edge statement and clearing
semantics (output `fea3fd0080d5c6d9398e977a4315d4c97b4170fd`). `lojxzuB`
independently elaborated the abstract limit at both signs, using
`compactLogMellin_vertical_decay` and `tendsto_tested_logDeriv_horizontal`
(output `e1ebd32145424ddc1e1b0ecc30d2bd5a4795cc61`; no tracked proof edit).
An untyped height binder inferred a real index; the checked statements
use an explicit natural index. The owner assembled the abstract limit
for the actual $L$ (output `7133e0afccca4e281c858028c20e4d7a3b2052c9`).
An earlier assembly-only integration `92aa6125fbe999493dcff357a20f449aba4e6c41`
was marked stale. The first checked two-file candidate
`23f5511614077a434c4307772f2685e7d9b679de` also went stale and did not
land. The unchanged two-file patch was restacked and rechecked.

**Review, checks, and adoption.** `CciByLX` independently reviewed both
revised statements against the original pin (output
`c58c75bae3d454b2fd83784647a985b6a43fe894`). The owning check session
`01a2060f-b72b-7614-a38b-57deecb33489` records exact patch and source
provenance inspection, successful `lake build --wfail` of both defining
modules (8693 jobs), a fresh joint import, matching built signatures,
and both axiom reports on the exact adopted revision
`4c20e0eebd4eca9c43090da318957c4bc0e2aef9` on base
`ca901a309a80c97e6e37166dae9a7589fb143c4c`. Both declarations depend only
on `propext`, `Classical.choice`, and `Quot.sound`. Adoption returned
that exact ID with `stale: false`. Closing checked the landing and its
ancestry, confirmed that the patch adds only the two defining modules,
inspected the exact declarations and assembly, and read the owning
check transcript. Closing did not rebuild or rerun the axiom checks.

**Manuscript correspondence and limits.** Independent reviewer `CciByLX`
inspected rendered pages of the pinned PDF. PDF pp. 604–605, Lemma
B.3.1.2 and (B.3.1.2), states absolute-integrand limits in a larger-strip
holomorphy and uniform Schwartz setting. PDF p. 614, §B.4.2.1 and
(B.4.2.2), states a residue identity with vertical integrals, a zero sum,
and an unshifted displayed pole subtraction. The Lean theorem replaces
only the signed horizontal input for compact-log Mellin tests on the
specified strip. It does not verify the manuscript's broader absolute
limits, its residue identity or pole normalization, the finite-product
reciprocal bounds, or its trace argument. The chapter 3 product
normalization was not freshly rendered in this review; any exact
correspondence to that normalization remains provisional. Closing
verified the PDF digest but did not independently inspect rendered
pages. The scope review is separately inherited as noted below.

## Remaining premises and reopening condition

Reopen the general-character analytic route only as a separate bounded
follow-up: Establish the normalized dual-character functional equation
for this exact completion, including its normalization factor, and
check that its logarithmic derivative transfers right-line nonvanishing
and growth to $\Re s=-1$. The right-line theorem is already available
for the same $L$ from its Euler-product agreement
(`Proofs/Theorems/CompletedHeckeRightLineGrowth.lean:30–35`). After
reflection and left-line control, the same continuation still needs a
signed full-order residue exhaustion and convergence argument with the
actual polar contributions at the possible poles $-i\lambda$ and
$1-i\lambda$. Even a general checked explicit formula would not locate
zeros. A trace-based location argument still needs both evaluations of
the same geometric diagonal and a justified common-test, full-divisor
comparison including the polar terms. The audited final trace algebra
alone does not establish those evaluations (PDF pp. 519–520, Theorem
12.5.1.1). Nor does the capped, different-test comparison supply them
(PDF p. 522, Theorem 13.3.1.1). The separate rendered-reading provenance
is in `.godel/obligations/trace-assembly.json` and
`.godel/obligations/divisor-heading.json` at the pin. A one-sided route
instead needs holomorphy of the same shifted finite logarithmic
derivative for both dual characters, with the exceptional point handled
separately; this pass supplies no such half-plane input.

For classical RH, reopen the short positive-log derivative-bump test
only with a specified shell-preserving Haar lift that compares the
actual orbital and S contributions with the terminal right projection,
both Mellin moments, and level exhaustion before position exhaustion.
The existing bump kills finite linear samples, not the actual orbital
trace, and the specified local projection misses the $+1/2$ moment.
The transfer from PDF p. 494, (11.3.1.4), to pp. 517–519, Theorem
12.4.1.1, remains provisional. See
`.godel/obligations/trace-to-zeros.md` at the evidence pin.

## Preserved opening note and plan

# Blitz opening: Full Masullo GRH

- Evidence revision: `7f6a93dc8c9307b575d9755d4a5360adc9288115`. This is the selected accepted evidence pin, verified as an ancestor of the campaign tip at opening (`685b387dfadda2f558469ad556017ee01d8efef6`). Do not substitute the tip, a prior attempt's pin, or a later revision for it. Distinguish new implementation and adoption revisions from the evidence pin. Lean is `v4.36.0`; Mathlib is `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`.
- Target and scope: Full Masullo GRH. Every nontrivial Hecke zero of every continuous unitary idele-class character over every number field, including ramified characters, has real part $1/2$. This scope follows the inherited rendered review in `.godel/blitz/decision-01a202cd-7acf-7edb-97ce-044d9614d43e.md:78–87` of PDF p. 6, Acknowledgements, and pp. 528–529, §14.1.2. It excludes the separate multiplicity claim and higher-rank conjecture. The opening did not independently inspect rendered pages. Classical RH is not this attempt's target.
- First mode: `LEAN`. The intermediate check is the two horizontal edges of the same Gaussian continuation of the actual completed Hecke product. This is a new attempt, not a reopening of prior stdin, a rerun of closed horizontal separation, or a claim to verify the printed trace argument. Do not launch, edit, schedule, or steer the manuscript or companion loops.

## Pass 1

Use isolated campaign workspaces per `cmd/godel/README.md`. Give two independent Lean contributors disjoint ownership:

1. **Same-continuation bound.** Start from `exists_completedHeckeEulerProduct_gaussianContinuation_horizontal` in `Proofs/Theorems/IdeleClassGaussianHorizontalCount.lean`, preserving the Euler-product identity and all continuation data for the same $L,H,\lambda$. Choose a fixed natural index offset at least $1$ and at least $|\lambda|+1$. Choose a common $T\in(m,m+1)$ for both edges at each offset index $m$. For $z$ on either closed edge, center the disk at $2+i\operatorname{Im}z$. Use `norm_logDeriv_le_of_moving_disk_bounds` in `Proofs/Lemmas/AnalyticGoodHeightDisk.lean` with the quadratic strip envelope on $[-4,8]$ on the radius-six sphere, the exponential center lower bound for the linear logarithmic loss, and the full-order closed radius-five count and supplied separation on the closed radius-three disk. For example, the sphere bound can be majorized by a positive constant times $(1+|\operatorname{Im}z|)^2$ since $1+|\operatorname{Im}w|\le 7+|\operatorname{Im}z|$ there. The inverse separation is $O(1+m)$ and $m<T$. Separation excludes $H(z)=0$. Differentiate the local identity $H=(s-1+i\lambda)(s+i\lambda)L$ away from the two exceptions, and subtract $1/(s+i\lambda)$ and $1/(s-1+i\lambda)$ from $H'/H$. The imaginary displacement on both edges is at least $T-|\lambda|>1$, so each reciprocal is uniformly bounded. Obtain nonvanishing and a uniform quadratic bound for $L'/L$ on both closed edges, with the same constant and heights for both signs and no dependence on the test.
2. **Horizontal-limit interface.** Work independently of the Hecke construction. From abstract common heights tending to infinity and uniform quadratic bounds at both signs on $[-1,2]$, use `compactLogMellin_vertical_decay` in `Proofs/Props/CompactLogMellin.lean` with $A=2$ and $N=3$, and apply `tendsto_tested_logDeriv_horizontal` in `Proofs/Lemmas/TestedRectangleEdges.lean` to both signed height sequences. Verify that the two interval integrals vanish for every smooth compactly supported log profile, with the reversal of orientation immaterial to vanishing. Use the existing lemmas directly if no separate helper is needed.

Assemble these for the actual $L$, then request a fresh independent statement review: Check quantifiers, same-continuation identity, the common heights and constant, the closed endpoints, both signs, the two clearing terms, and the absence of an unramified restriction. Use the pinned 940-page PDF at `/home/exedev/d/masullo/the-music-of-the-primes.pdf`, SHA-256 `e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5`, as specified by `.godel/sources/masullo/README.md` at the pin. Ask the reviewer to inspect the rendered PDF pp. 604–605, Lem. B.3.1.2 and (B.3.1.2), and p. 614, §B.4.2.1 and (B.4.2.2). The identification of these passages with the horizontal input and any exact correspondence of hypotheses, integrands, and bounds are provisional until rendered review. The Lean construction is a replacement for that input, not verification of the printed argument or of the finite Euler-product reciprocal bounds.

Stay in `LEAN` for elaboration or integration issues. Switch to `INFORMAL` only upon identifying a specific mathematical gap with a bounded repair to test within the remaining passes. Return to `LEAN` once that repair has precise hypotheses matched to the pinned evidence. Preserve the target, scope, stopping condition, evidence pin, and this opening note across passes.

## Stopping condition

Stop successfully when an independently reviewed Lean theorem is built, jointly imported, axiom-checked, and adopted at the exact checked revision. It must show that the same Gaussian continuation $L$ of the actual completed Hecke product is nonvanishing and has a uniform quadratic logarithmic-derivative bound on both closed horizontal edges at one common sequence of heights above $|\lambda|$, and actually use that bound to prove that both tested horizontal integrals tend to zero for every smooth compactly supported log profile. Preserve the continuation's Borel, norm-one class-representative, and unitarity hypotheses without adding an unramified restriction. Stop without success at a precise mathematical, tooling, or adoption blocker with no viable bounded repair, or after three total passes.

The endpoint is a contour prerequisite only, not a proof or refutation of full GRH. The normalized dual-character reflection for the same continuation, left vertical control, signed full-order residue exhaustion with translated polar contributions, and a separate zero-location argument remain outside this check. Only the closing role writes finalized outcomes to `.godel/blitz/`.
