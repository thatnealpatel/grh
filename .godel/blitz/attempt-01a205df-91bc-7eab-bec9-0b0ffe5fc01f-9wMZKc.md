# ATTEMPTED: Full Masullo GRH, general-character horizontal separation

**Original accepted evidence:** `dffe6e3491d1d3899b6e4b1ff8b582ad81eabe1c`.
**Target:** Every nontrivial Hecke zero of every continuous unitary
idele-class character of every number field, including ramified
characters, has real part $1/2$. The scope is inherited from the
rendered review cited in the preserved opening plan, not independently
verified here. Classical RH for `riemannZeta` was not attempted.

**Close:** Attempted; synthesis ended the attempt after pass 1, in
accordance with the opening stopping condition. The independently
reviewed, built, axiom-checked horizontal-separation prerequisite
landed. Full GRH remains unresolved. No zero-location theorem, general
contour identity, or repair of the printed trace proof resulted. No
further pass was run.

## Pass 1 (LEAN): The same numerator has a full-order count and good heights

The theorem `Masullo.exists_completedHeckeEulerProduct_gaussianContinuation_horizontal`
in `Proofs/Theorems/IdeleClassGaussianHorizontalCount.lean:41–63` at
`8f59df9e67ff4d6420e26df0c98b0c3f8fa01109` gives the following on the
Gaussian continuation's own entire pole-cleared numerator $H$:

- $|H(2+it)|\geq\exp(-A(1+|t|))$ with a positive constant $A$.
- At most $C_0(1+|t|)$ zeros counted with full orders on the **closed**
  radius-five disk centered at $2+it$. This includes boundary zeros and
  any extra zeros introduced by pole clearing.
- For each integer $n\geq1$, one $T\in(n,n+1)$ works on both edges
  $-1\leq\Re z\leq2$, $\Im z=\pm T$: Every point of either edge is
  at distance at least $1/(16(C_0+1)(1+n))$ from every zero of $H$.
  The constant $C_0>0$ is uniform in $t$ and $n$.

The endpoint retains the continuation's measurable and Borel structures,
its choice of a norm-one idele representative for each ideal class with
the required class identity, and character unitarity. It has no
unramified restriction and assumes neither a functional equation nor
zero location. It uses the same $L$ that agrees with the completed
Euler product on $\Re s>1$, and the same $H$ with
$H(s)=(s-z_1)(s-z_0)L(s)$ away from $z_0=-i\lambda$ and $z_1=1-i\lambda$,
where $\lambda$ is the norm frequency.

**Contributions.** `gamma` (`vldPbFS`, output
`147c046e9b0168b2af3e10263a0148dc468403c9`) supplied the lower bound on
the actual shifted and normalized Gamma factors in
`Proofs/Theorems/CompletedHeckeEulerProductGammaLowerBound.lean:23–35`.
The half-integer reflection and recurrence lemmas in
`Proofs/Lemmas/GammaRightLineLowerBound.lean` complement the integer-line
bound so both real parities and all complex angular weights are covered,
including at zero shifted imaginary argument. `count` (`gFDGgmS`, output
`f3ac41fbb54685b6afd39ee127af6d7627da62a7`) used these bounds as an
interface. It combined the finite Euler-product lower bound with the
translated clearing factors, whose norms are at least one on the center
line. The continuation's quadratic strip bound controls the radius-six
sphere, so the log ratio in Jensen's inequality gives the linear count
on the closed radius-five disk. It then applies the existing symmetric
horizontal-separation theorem. See
`Proofs/Theorems/IdeleClassGaussianHorizontalUnitary.lean:155–209` and
its count lemma. The owner wrapper (output
`f9a71e59160078e4f2506a829bbc3a490288db49`) discharges the local-bound
interface without replacing the continuation. Both contributors completed.

**Review and checks.** The exact proof candidate above was integrated on
`7b1cd58ee10636e87883a82168945cabd56d8c72` and adopted without restacking.
This integration base is not the original evidence pin. The closing
session checked the accepted head, the candidate's parent and four-file
patch scope, the exact endpoint and same-continuation assembly, and the
owning check transcript. Independent reviewer `wbTAXYh` (output
`04eab642ca6759bfcacf12a4bdfdf3feb9f9f42f`) checked the fixed statements
against the analytic obligation; the four reviewed files matched the
integration candidate. This was a statement review, not a second build.

The owning check session `01a205e0-3602-798e-bd35-abc4a6037af2` records the
exact candidate diff, source-provenance and toolchain checks, and
successful integration-workspace `lake build --wfail` for 11 changed
and affected targets (8765 jobs) under Lean 4.36.0 and Mathlib
`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. A fresh joint import checked
`Masullo.exists_archimedeanGammaFactor_real_rightLine_lower_bound`,
`Masullo.exists_archimedeanGammaFactor_complex_rightLine_lower_bound`,
`Masullo.exists_localHeckeGammaFactor_rightLine_lower_bound`,
`Masullo.exists_completedHeckeEulerProduct_gaussianContinuation_horizontal_of_local`,
and the endpoint. The built signatures matched the reviewed statements;
each transitive axiom report contained only `propext`, `Classical.choice`,
and `Quot.sound`. No new build or axiom replay was done in closing.

**Limits of the pass.** The theorem separates zeros of $H$, not poles
of $L$. It does not yet bound $L'/L$ on a contour or prove a residue
identity. The correspondence with Masullo's PDF p. 123, (3.2.1.3–5),
pp. 604–605, Definition B.3.1.1 and Lemma B.3.1.2, and p. 614,
§B.4.2.1, is provisional: Neither the pass owner nor its reviewer
confirmed it by direct rendered-page inspection. This analytic
prerequisite is not a repair of the printed positive-width trace
comparison. The earlier $\mathbb Q(i)$ weight-four obstruction to the
literal boxes in PDF pp. 519–520, Theorem 12.5.1.1, is separate,
ordinary-mathematics evidence with a rendered dependency review
inherited from `.godel/blitz/attempt-01a205aa-7864-75c9-a01b-d5b7fc738940.md`
at `6552bac21a017dee269ec4f6307c19597bded334`. It rejects that comparison,
not GRH. Neither the trivial-character contour nor its scalar explicit
formula provides the general-character contour or locates zeros.

## Remaining premises and reopening condition

Reopen the general-character analytic route for a bounded same-continuation
edge estimate: Apply the moving-disk logarithmic-derivative estimate
(`Proofs/Lemmas/AnalyticGoodHeightDisk.lean:241–247`) to the landed $H$
on the selected edges, take $n$ at least one above $|\lambda|$ so the
edges avoid both translated points with a uniform gap, and subtract the
two clearing-factor terms $1/(s-z_j)$ to bound $L'/L$ there. This is a
proposed next check, not a result of this cycle. Even after it, a contour
needs controlled vertical sides, absolute convergence and the signed
full-order residue limit with the actual translated polar terms. To
reflect the left integral, prove the normalized dual-character functional
equation for this same continuation. Neither the prerequisites nor a
full-order explicit formula gives critical-line location.

For the printed trace route, a full-divisor conclusion still needs a
justified all-field, all-character comparison on common tests, including
full rather than capped orders and the correct polar terms. No such
comparison was shown. Reopen the failed literal-box route only with a
checkable formal endpoint for that exact obstruction, or with a specified
angular-shrinking replacement whose global, S-local, and orbital
diagonals can be compared using matching Haar measures, weights,
cutoffs, and order of limits. Classical RH was declined at admission:
The normalized rational full-order scalar formula does not give the
strip-supported same-test comparison. Reopen the rational short-bump
route only with a specific Haar-compatible global lift retaining the
terminal right projection and shell, with level exhaustion before
position exhaustion, so both Mellin subtractions and the local and
orbital terms can be compared on the same test.

## Preserved opening note and plan

# Opening plan: Full Masullo GRH, general-character horizontal separation

- **Accepted evidence revision (fixed):** `dffe6e3491d1d3899b6e4b1ff8b582ad81eabe1c`. Verified that the pin is an ancestor of the currently accepted campaign head. Later accepted changes do not replace this evidence pin. Use Lean v4.36.0 and Mathlib `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`.
- **Target:** Full Masullo GRH: Every nontrivial Hecke zero of every continuous unitary idele-class character of every number field, including ramified characters, has real part $1/2$.
- **Scope:** The target follows the inherited rendered review in `.godel/blitz/decision-01a202cd-7acf-7edb-97ce-044d9614d43e.md:78–87` (PDF p. 6, Acknowledgements, and pp. 528–529, §14.1.2). The multiplicity and higher-rank claims, including Conj. 14.1.2.1, are separate. Classical RH is not attempted. Use the 940-page edition pinned in `.godel/sources/masullo/README.md` at the evidence revision, SHA-256 `e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5`. This opening does not independently verify the rendered scope. The prior Q(i) obstruction is inherited evidence against the literal proof at PDF pp. 519–520, Thm. 12.5.1.1, not against GRH. Do not reopen that comparison or steer the manuscript and companion loops.
- **First mode:** `LEAN`.
- **Stopping condition:** At most three passes total. Stop early when an independently reviewed, built, axiom-checked, and adopted Lean endpoint gives an $O(1+|t|)$ full-order zero count on the closed radius-five disk centered at $2+it$ and common horizontal separation for the same Gaussian continuation numerator for arbitrary unitary characters, or when a precise blocker leaves no bounded next check. Stop at pass three regardless. This endpoint is a contour prerequisite under the continuation's stated hypotheses, not closure. Report full GRH unresolved unless a complete proof of the exact target passes a separate rigorous audit.

## First pass

Give two disjoint Lean assignments in isolated campaign workspaces:

1. **Archimedean lower bounds.** Check pinned Mathlib's reflection and conjugation at $1/2+iu$ for real $u$. Derive a lower bound from $|\Gamma(1/2+iu)|^2=\pi/\cosh(\pi u)$, and use recurrence together with the existing integer-line bound. Cover both real parities, every complex angular weight, and the exact frequency shifts and prefactors in `CompletedHeckeEulerProduct.lean:48–73`. Export bounds of the form $\exp(-A(1+|t|))$, with constants allowed to depend on the field and character. Handle $u=0$ as well as both signs of $u$.
2. **Continuation, counting, and heights.** Take the local exponential bounds as an explicit interface. Combine them with `FiniteHeckeEulerProductLowerBound.lean:36–76` and the translated pole-clearing factors to bound the continuation's own $|H(2+it)|$ below by $\exp(-A(1+|t|))$, using the agreement on the Euler-product half-plane in `IdeleClassGaussianContinuation.lean:65–106` and retaining its Borel, class-representative, and unitarity hypotheses. Apply its strip-growth bound on the radius-six sphere and justify the radius-five count with orders, including the radius-five boundary. Use that count and center nonvanishing to test `exists_symmetric_horizontal_separation` in `AnalyticHorizontalHeights.lean:83–90`. Reuse the trivial-character Jensen route where it applies without importing a trivial-character specialization into the statement.

Integrate the two interfaces only after checking the exact shifts, the common numerator, the center and boundary conditions, and the divisor orders. Neither assignment may assume a functional equation or zero location. The comparison with PDF p. 614, §B.4.2.1, is provisional pending independent inspection of the rendered page. The proposed argument is an analytic prerequisite, not a repair of the printed trace proof.

In later passes, stay in Lean for implementation gaps with a clear mathematical argument. Switch to `INFORMAL` only if a specific mathematical premise or same-continuation identification fails and admits a bounded proof or counterexample check. Preserve the pin, target, scope, stopping condition, and this opening note across passes. Report any capability, check, or adoption blocker rather than treating an unfinished draft as a result.
