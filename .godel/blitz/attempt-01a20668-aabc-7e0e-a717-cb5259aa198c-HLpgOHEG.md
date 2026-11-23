# Blitz outcome: Same-continuation Hecke reflection

**ATTEMPTED.** Pass 1 (INFORMAL) met the stopping condition for the
intermediate reflection check. Synthesis ended the attempt. No further
pass or Lean landing was made. Full Masullo GRH is not proved.

## Evidence, scope, and admission

- **Original accepted evidence:** `cf0ac6bcbaae42159e6cd57881d61b0175074c0a`.
  Campaign status at opening established the pin, not its coincidence with
  the executable archive. Use Lean `v4.36.0`, Mathlib
  `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`, and the 940-page PDF pinned in
  `.godel/sources/masullo/README.md`, SHA-256
  `e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5`.
  Neither the later pass tip `fd9b420ec415046d03028c1929d0b349ac0f7426`
  nor the closing workspace base was substituted for the evidence pin.
- **Target:** Every nontrivial Hecke zero of every continuous unitary
  idele-class character of every number field, including ramified
  characters, has real part $1/2$. The scope is inherited from the
  rendered review in
  `.godel/blitz/decision-01a202cd-7acf-7edb-97ce-044d9614d43e.md:78–87`
  (PDF p. 6, Acknowledgements, and p. 528, §14.1.2). The noncentral
  multiplicity claim and higher-rank conjecture are separate.
- **GRH assessment:** Admit a bounded check of the actual Fourier tensor
  and corrected Mellin comparison for the same completed Euler-product
  continuations. The accepted continuation and theta inversion supply the
  exact tests and zero modes, but theta inversion by itself does not
  identify the dual Gaussian. The prior ramified-factor report landed at
  `a388a0824177684ea01ff4dddc2d6f085d74e33f` and supplies the independently
  reviewed local calculation, not a Lean endpoint. This assembly is
  distinct from the prior local calculation, the trivial-character and
  modulus-three specializations, and the tested horizontal limits.
- **Classical RH assessment:** Not attempted. At the pin, the unconditional
  rational explicit formula includes the full-order zeta-zero sum and
  both polar moments (`Proofs/Theorems/RationalIdeleRadialExplicitFormula.lean:61–75`).
  `Proofs/Props/ZetaTestSumComparison.lean:30–39,78–110` still requires
  agreement for all admissible tests at arbitrarily small widths. The
  scalar width limit is not a geometric limit. Applying the conditional
  below-one separator to the actual trace still requires the omitted-zero
  tail budget, support fit, and identification with the same projected
  diagonal. The finite radial
  pairing bound does not identify that diagonal, and the prime-two
  obstruction rules out only the literal lift. Reconsider RH on a
  concrete, shell-preserving same-diagonal comparison with both polar
  subtractions for an admissible short test, distinct from loop work.

## Pass 1 (INFORMAL)

**Result reported by the pass.** For the exact paired Gaussian
continuations of `Proofs/Theorems/IdeleClassGaussianContinuation.lean:53–106`,
under their Borel and norm-one class-representative hypotheses, put
$d_v$ and $n_v$ for the finite different and conductor exponents. Let
$c_v=\pi_v^{-d_v-n_v}$ at finite places, $c_v=1$ at infinite places, and
$B=|c|=|D_K|N(\mathfrak f_\chi)$. The calculation gives

$$
\widehat f_\chi(z)=A f_{\bar\chi}(c^{-1}z),\qquad |A|=B^{-1/2},
\qquad L_{\bar\chi}(1-s)=A^{-1}\chi(c) B^{s-1}L_\chi(s).
$$

The last identity is meromorphic, not an equality of totalized values
at poles. At ordinary points it gives the neighborhood equality used by
`Proofs/Props/HeckeContourReflection.lean:28–32`, with $\kappa=\log B$
and $C=A^{-1}\chi(c)B^{-1/2}$ of modulus one. This is an independently
reviewed ordinary-mathematics result under the stated hypotheses, not a
new verified Lean declaration. The opening note below called the module
`Theorems/HeckeContourReflection.lean`; the path at the pin is
`Proofs/Props/HeckeContourReflection.lean`.

**Fourier assembly.** The Fourier contributor (`nJwDUHr`, output
`166d3d0e3a1f88ede87c9dc7dbeb9c453accbfe7`) checked the actual trace
kernels and the full tensor, rechecked the ramified finite sum, and
separately checked the translated polar terms. With $2\,dx\,dy$ and the
negative trace kernel at complex places, the index-one Gaussian maps to
$-i$ times the Gaussian of index $-1$ with unchanged radial scale.
Differentiation gives $(-i)^{|n|}$ for complex angular index $n$ and
reverses the index; real parity $b$ contributes $(-i)^b$. The actual
selected indices are forced by sign or rotation invariance and the
nonzero Gamma Mellin evaluation, not by an assumed property of `.choose`.
See `Proofs/Lemmas/ArchimedeanTracePairing.lean:30–37` and
`Proofs/Theorems/ArchimedeanTracePoisson.lean:33–48` and
`Proofs/Theorems/ArchimedeanCompletionGaussian.lean:30–37,64–71`.

At an unramified finite place the transform is the codifferent indicator
with mass $q_v^{-d_v/2}$. At a ramified place the positive trace transform
of the inverse-character unit test is supported exactly on
$c_v\mathcal O_v^\times$. There it equals $A_v\chi_v(u)$ at $c_vu$ with
$|A_v|=q_v^{-(d_v+n_v)/2}$. This uses the local calculation in
`.godel/blitz/attempt-01a2063c-9479-72e6-9cf8-4541c9cac0cf.md:63–195`,
not the printed Gauss sum. Finite-stage Fubini on a stage containing all
exceptional places and nonintegral frequency coordinates leaves omitted
factors equal to one. The product gives the first identity including at
additive zero, and retains $\chi(c)=\prod_v\chi_v(\pi_v)^{-d_v-n_v}$.
The relevant Lean inputs are `Proofs/Theorems/FiniteCompletionIntegersFourier.lean:31–55`,
`Proofs/Theorems/FiniteCompletionDifferentExtension.lean:61–82`,
`Proofs/Theorems/AdeleHeckeTest.lean:42–107`,
`Proofs/Theorems/AdeleFiniteStageHaar.lean:30–43`, and
`Proofs/Theorems/AdeleBoxFourier.lean:46–104`.

**Corrected Mellin comparison.** The corrected-Mellin contributor
(`MpAnaRy`, output `ba12dbc3015d6fc779dffabce730c0cdab1afde4`) independently
checked the complex transform and actual test indices, then combined the
cofinal-stage tensor and the previously reviewed ramified factor with
the corrected Mellin comparison. The pass owner compared both
calculations with the pinned theta and continuation statements. Cofinal
comaps identify the additive Haar measures, and equality of positive
finite total masses identifies the compact norm-one Haar measures.
With $t=-\log B$, $\rho=A\chi(c)^{-1}$, and the character-weighted raw
profile $U$, theta inversion and Haar-preserving inversion and translation
on the norm-one group give

$$
U_\chi(x)=\rho e^{-x}U_{\bar\chi}(t-x)+Z_\chi(x),\qquad
Z_\chi(x)=e^{i\lambda x}(a_1e^{-x}-a_0).
$$

Here $\lambda$ is the section phase parameter, and primes on the
coefficients denote the dual continuation with parameter $-\lambda$.
If the norm-one restriction is nontrivial, both sets of modes vanish.
For a pure norm twist the zero values give $a_1=Aa'_0$ and
$a'_1=e^t a_0/A$; the corrected-Mellin review independently recovered
these relations from the tail bounds. Consequently
$Z_\chi(x)=-\rho e^{-x}Z_{\bar\chi}(t-x)$. Writing the corrected profile
as $U_\chi(x)-\mathbf{1}_{x<0}Z_\chi(x)$, the change from the original
cutoff to the dual one contributes the oriented integral from $0$ to
$t$ of $Z_\chi(x)e^{sx}$. Adding it to the original rational terms,
with $z_0=-i\lambda$ and $z_1=1-i\lambda$, gives

$$
\frac{a_1e^{t(s-z_1)}}{s-z_1}-\frac{a_0e^{t(s-z_0)}}{s-z_0}.
$$

These are the reflected dual terms with exchanged poles and signs,
after including the same scalar $\rho e^{t(s-1)}$ as for the corrected
integral. The common discriminant multiplier cancels. The argument
uses absolutely convergent corrected integrals, not an overlap of
convergence regions for two raw integrals. See
`Proofs/Theorems/AdeleHeckeGaussianTheta.lean:77–90`,
`Proofs/Theorems/AdeleRestrictedProductHaar.lean:65–73`,
`Proofs/Theorems/IdeleClassGaussianCorrectedMellin.lean:52–88,114–126`, and
`Proofs/Theorems/IdeleClassGaussianContinuation.lean:74–106`.

**Failure and check.** An unshifted-cutoff argument loses the oriented
interval and fails already over $\mathbb Q(i)$. The reported check with
the pure norm twist $\lambda=\pi/(2\log 4)$ gives factor $i4^{s-1/2}$
and residue ratios $2$ and $1/2$ at the paired possible poles, rejecting
an inverted conductor power and omission of the character phase.
Translating the cutoff and keeping both polar terms repairs the
comparison. Synthesis reports a fresh adversarial check with no sign,
phase, or cutoff mismatch; this was not a source or kernel audit. The
closing session verified that both contributor output revisions exist
and are empty of tracked changes. Their calculations and synthesis
checks are attributed to those roles. There was no new Lean
elaboration, build, or axiom audit.

**PDF provenance.** This is a repair related to PDF p. 123, (3.2.1.6),
not verification of the printed functional equation, Gauss sum, or
trace proof. Rendered readings of the finite-place conventions at
PDF p. 136, (3.3.1.30), p. 141, (3.3.2.24), and p. 152, (3.4.3.7–9)
are inherited from the ramified-factor report cited above. The
continuation correspondence at PDF pp. 124–127, Thm. 3.2.2.1, remains
provisional. No new rendered inspection is claimed, and no decisive
premise of the repair uses that provisional correspondence.

## Final outcome and reopening condition

Pass 1 discharged the bounded reflection check in ordinary mathematics.
There were no passes 2 or 3. No Lean reflection theorem was added or
adopted. Reopen this route in a new bounded attempt when ready to
formalize the exact tensor and translated-cutoff Mellin identity under
the pinned continuation hypotheses, or to use the reviewed reflection
for an exact general-character left-line transfer. The latter needs the
dual right-line nonvanishing and log-derivative control with the correct
conductor contact. A signed full-order residue exhaustion still needs
convergence and both possible polar contributions for that same
continuation. None of these analytic steps is a zero-location deduction.
For the trace route, a common-test full-divisor comparison on the same
projected diagonal also remains outstanding. Full GRH requires a
separate unconditional zero-location deduction covering the entire
target and a rigorous audit. Classical RH was not attempted. This
finalized report is the only closing change.

## Preserved opening note (historical)

# Blitz opening plan: Same-continuation Hecke reflection

## Fixed evidence, target, and scope

- Accepted evidence revision: `cf0ac6bcbaae42159e6cd57881d61b0175074c0a`. Use this pin across all passes, not the preceding closing revision or its older evidence pin. Use Mathlib `fc4f59e577feb1a4956671bc04ac18aaaf8cd842` and the Masullo edition pinned by `.godel/sources/masullo/README.md` at this evidence revision.
- Target: Full Masullo GRH. Every nontrivial Hecke zero of every continuous unitary idele-class character of every number field, including ramified characters, has real part $1/2$. This scope is inherited from the rendered review in `.godel/blitz/decision-01a202cd-7acf-7edb-97ce-044d9614d43e.md` of PDF p. 6, Acknowledgements, and p. 528, §14.1.2. Classical RH is not a second target. The separate noncentral multiplicity claim and higher-rank conjecture are out of scope.
- Intermediate obligation: Determine whether the actual Gaussian Fourier tensor yields a dual-character reflection for the very same completed Euler-product continuations constructed in `Proofs/Theorems/IdeleClassGaussianContinuation.lean:70–106`, under its stated Borel and norm-one class-representative hypotheses. Compare with the germ required by `Proofs/Theorems/HeckeContourReflection.lean:26–38`, namely $L_{\bar\chi}(1-s)=C\exp(\kappa(s-1/2))L_\chi(s)$ with $C\ne0$. This is a proposed repair related to PDF p. 123, (3.2.1.6), not verification of the printed trace proof. Left-line transfer, signed full-order residue exhaustion, and zero location are not part of this intermediate check. A reflection, a conditional result, or a specialization does not discharge the target, and a mismatch would defeat only the proposed assembly.

## First mode: INFORMAL

1. Start from the actual test and trace kernels pinned in the evidence. First check whether the complex angular Gaussian of index 1 is sent to the dual index at unchanged radial scale with a nonzero constant. Use two contributors in parallel, with distinct assignments:
   - Fourier assembly: Check the real and complex transforms for all indices, then assemble them with the unramified codifferent transform and the previously reviewed ramified local factors. Track scaling, phases, the resulting scalar and idelic dilation, and every uniformizer character value. Use the ramified closing report as independently reviewed ordinary mathematics, not as a Lean theorem or verification of the printed Gauss sum. Do not assume the separate unramified, self-inverse reflected Mellin theorem applies to general characters.
   - Corrected Mellin comparison: Independently derive what a symbolic scalar and dilation must satisfy in the two corrected Mellin expressions. Compare the common norm-one Haar, discriminant normalization, section phase, and both translated polar terms, including for pure norm twists. Keep the same test and continuation on each side; do not replace them with a differently normalized completion.
2. Compare the two results with `IdeleClassGaussianContinuation.lean` and the germ required by `HeckeContourReflection.lean`. Use `Proofs/Theorems/AdeleHeckeGaussianTheta.lean:70–90` only as reflection to the actual Fourier transform until the tensor is identified. Seek a fresh independent critique of the decisive identity or mismatch, including nonvanishing and the direction and coefficient of the exponential.
3. For manuscript navigation, begin in `/home/exedev/d/masullo` using the Markdown and layout extraction, and cite only the pinned PDF. Give reviewers PDF p. 123, (3.2.1.6); pp. 124–127, Thm. 3.2.2.1; p. 136, (3.3.1.30); p. 141, (3.3.2.24); and p. 152, (3.4.3.7–9). Inspect the rendered page where exact notation or wording is decisive or readings disagree; mark readings without direct inspection provisional, identify any decisive provisional premise, and attribute inherited rendered checks to their notes.
4. Switch to LEAN only if a precise, reviewed candidate with available pinned prerequisites leaves a specific integration question elaboration can settle within the remaining passes. Otherwise use a remaining INFORMAL pass only for a named disputed step. The three-pass cap is shared across modes. Preserve this opening plan, pin, target, scope, and stop across passes. Do not steer either loop; any later proof edits must use the isolated campaign workflow.

## Stopping condition

Stop at an independently reviewed exponential reflection for the exact paired Gaussian continuations, an independently reviewed mismatch that defeats the proposed assembly, a named prerequisite that cannot be checked or repaired within the remaining budget, or the end of pass three, whichever comes first. Reflection is an intermediate result, not GRH. Claim GRH only after a separate rigorous audit of an unconditional proof for the full target.
