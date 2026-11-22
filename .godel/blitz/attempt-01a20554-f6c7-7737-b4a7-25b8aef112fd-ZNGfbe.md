# Blitz outcome: Conductor-three idelic normalization

**ATTEMPTED.** Pass 1 verified the repaired conductor-three bridge in
ordinary mathematics, not in Lean. It transports an existing contour
identity and locates no zeros. Full Masullo GRH was not proved or
refuted. Finish reason: `attempted: synthesis ended the attempt`. The
opening early-stop condition was met: No common positive-width
diagonal was specified on the same Mellin tests. No further pass ran.

## Opening plan: Full Masullo GRH

- **Pinned accepted evidence:** `bf8d53cd4d39ac0ff7ea612f20161729e9786375`. Use the manuscript edition pinned by `.godel/sources/masullo/README.md` at this revision and the pinned Mathlib `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. Keep this evidence pin and opening note fixed through all passes.
- **Target and scope:** Unconditional full Masullo GRH: Every nontrivial Hecke zero for every continuous unitary idele-class character of every number field, including ramified characters, has real part $1/2$. The scope is inherited from the rendered-page readings recorded in `.godel/blitz/decision-01a202cd-7acf-7edb-97ce-044d9614d43e.md:78–87` (PDF p. 6, Acknowledgements, and p. 528, §14.1.2). The target excludes separate multiplicity and higher-rank claims. Neither the rational specialization nor a conditional result discharges it.
- **First mode:** INFORMAL.
- **Stopping condition:** At most three passes total. Claim success only after a separate rigorous audit of an unconditional proof at full scope. Stop without success if the conductor-three comparison is refuted or remains unresolved and there is no specific supported repair, or if the bridge is verified but no common positive-width diagonal is specified well enough to check on the same Mellin tests. A verified bridge is partial progress, not a zero-location result. A normalization mismatch rejects the proposed identification, not GRH.

### Pass 1 plan: Test the normalization bridge for the odd character modulo 3

This is a new intermediate obligation, not a reopening of the closed contour exhaustion. Use `global-mellin-sign-q.md` for the descended character, rational Haar calibration, the $s=2$ shell check, and the separately defined entire class pairing. Use `Masullo.padicRamifiedThree_completed_residue_exhaustion` and `completedDirichlet_reflect_left_integral` at the pin for the contour and reflection of Mathlib's completion without a conductor power.

1. In parallel with the contour audit, have one reader unfold the calibrated rational idelic pairing on $\operatorname{Re}s>1$ for the odd real Gaussian, the inverse character on the $3$-adic units, and integer-ball factors elsewhere. Check the Haar constant, odd Gamma factor, and all Euler factors, with the factor at $3$ omitted. Justify absolute convergence and the application of analytic uniqueness to the separately defined entire class pairing. Determine the exact factor, if any, relative to Mathlib's completion; equality of zero sets alone does not identify the tested logarithmic derivatives.
2. Have a second reader audit the upward right-minus-left contour on one smooth compact log profile with $g(0)=1$. Check the sign and normalization of the proposed $+\log 3$ contact for the unscaled completion when the upward left leg is subtracted. Track the logarithmic-derivative shift and its contribution on each leg separately if the completion is multiplied by $3^{s/2}$. Use the same Mellin tests and distinguish the reflection contact from the separate scaling contribution.
3. Start manuscript navigation in `/home/exedev/d/masullo/` and independently inspect the rendered PDF p. 152, Def. 3.4.3.2, and pp. 614–615, (B.4.2.2–4). The mappings remain provisional until those inspections. Distinguish the manuscript argument from a repaired idelic comparison. Do not take over Main's general Gaussian continuation or Companion's right-mask audit.

Switch to LEAN only if the exact function comparison, Haar normalization, and contour identities have been independently checked and the pinned definitions expose a concrete theorem to prove. Reserve any remaining pass for a specific supported repair, a check of an identified common positive-width diagonal on matching tests, or an independent audit. Further progress from a verified bridge would require separate conductor, identity, pole, and central-zero accounting on that diagonal, and an argument covering all fields and characters in the target scope.

## Assessed alternative and evidence provenance

The pin specifies Lean 4.36.0, the Mathlib revision above, and the
940-page edition of Alessandro Maria Masullo's *The Music of the
Primes* with SHA-256
`e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5`.
Later accepted revisions did not change the evidence pin.

Classical RH (Mathlib's `RiemannHypothesis` for $\zeta$) was assessed,
not attempted. `Proofs/Theorems/RationalIdeleRadialExplicitFormula.lean:61–75`
gives the full-order sum, both polar moments, and both normalized
local terms. `Proofs/Props/ZetaTestSumComparison.lean:30–39,78–110`
requires agreement with an order-dominated, strip-supported sum on
all smooth compact positive-log mass-zero tests for arbitrarily small
positive half-widths. The one-prime cut-range results at the pin are
at width zero, not a comparison of positive-width diagonals. The
zero-versus-$\log 2$ witness in
`Proofs/Theorems/RationalOrbitalObstruction.lean:25–35` rejects the
literal Haar lift, not RH or all lifts. Reopen that check when a
shell-preserving lift identifies the same fixed-cutoff Haar diagonal
on both sides with the terminal projection and limit order specified,
so that a derivative bump supported in $(0,\log 2)$ has two computable
values. The right-mask chain and limit in PDF pp. 495–496,
(11.3.2.3–4), were provisional in the intake and not audited here.

The new conductor-three obligation continued the local bridge left
open by `.godel/blitz/attempt-01a20519-22f7-70f5-8948-f1c5f67c2518-mzaanG.md`
(accepted at `71dbf2ff4f4f9c1b5344e894e5ebd964988da666`). Closure
confirmed that the finite rectangle identity at
`a3d7b9173f2baccf732d75f873b0a46d838c9ccb` and the full-order
exhaustion at `0ec16aa411ec0b6bda96791e666ded761640c801` are
ancestors of the pin and inspected the declarations at those exact
revisions. Build, signature, and axiom checks for those historical
landings are attributed to the owning sessions cited in that note,
not to this cycle. Companion's local $1$ versus $\sqrt 3$ ratio
comparison (PDF p. 136, (3.3.1.30–32)) did not compare the global
pairing. This pass did not take over the general Gaussian
continuation or the right-mask audit.

## Pass 1: INFORMAL, exact function and reflected contour

**Idelic comparison.** Reader `idelic-comparison` (`RBmeZmR`) took
$\eta$ to be the odd primitive quadratic Dirichlet character modulo
$3$. Its descended rational idele-class character has real component
$\operatorname{sgn}$, $3$-adic component $\eta$ on units and value $1$
on the uniformizer, and component $\eta(p)^n$ on $p^n\mathbb Z_p^\times$
for $p\ne3$. On a diagonal rational the real sign and the latter
values cancel the $3$-unit value by quadraticity. Use the tensor $h$
with real profile $x e^{-\pi x^2}$, the inverse character supported
on $\mathbb Z_3^\times$, and integer-ball indicators at $p\ne3$.
With $dt/|t|$ on both real rays and finite unit mass one, the right
half-plane computation is

$$
Z(h,\chi|\cdot|^s)=
\pi^{-(s+1)/2}\Gamma((s+1)/2)
\prod_{p\ne3}(1-\eta(p)p^{-s})^{-1}
\qquad (\operatorname{Re}s>1).
$$

The odd character and odd Gaussian give the positive two-ray integral
$2\int_0^\infty e^{-\pi t^2}t^s\,dt$. At $3$ the character cancels
its inverse on the unit shell, giving exactly $1$. The other shells
have mass one and sum to the Dirichlet series with $3$ omitted.
The absolute shell sum is bounded by the finite real absolute
integral times $\sum_{3\nmid n}n^{-\operatorname{Re}s}$. The separately
defined class integral pairs the nonzero-orbit theta sum with
$\chi(k)|k|^s$ against calibrated quotient Haar. Both zero modes
vanish, and repaired theta inversion and the two-sided log-norm
tails dominate the integral and its log moments uniformly on compact
$s$-sets. The entire class pairing unfolds absolutely on the right
half-plane via the positive-real finite-unit fundamental domain.
Analytic uniqueness gives equality on $\mathbb C$ with Mathlib's
unscaled completion $C_3=\Gamma_{\mathbb R}(s+1)L(s,\eta)$, with
**neither an extra scalar nor a conductor power**. Equality just at
$s=2$ would not suffice: Replacing the real profile $b(x)$ by
$b(3^{-1/2}x)/3$ preserves that value but multiplies the function by
$3^{(s-2)/2}$.

The pass checked this argument against
`.godel/obligations/global-mellin-sign-q.md:42–112`,
`Proofs/Theorems/RationalIdeleHaarComparison.lean:29–66`,
`Proofs/Theorems/RationalIdeleRestrictedProductHaar.lean:109–126`,
and the tails in `Proofs/Theorems/RationalAdeleThetaTails.lean`.
Reader `RBmeZmR` independently inspected rendered PDF p. 152,
Def. 3.4.3.2 and (3.4.3.4), (3.4.3.7–9), confirming the tensor and
unscaled pairing definition. The continuation above is a repair using
repaired theta inversion, not validation of the printed Fourier
argument.

**Contour contact.** Reader `contour-contact` (`dbHfHNi`) took
$g(x)=\exp(1-1/(1-x^2))$ on $|x|<1$ and zero elsewhere, so $g(0)=1$.
Write $M_g(s)=\int_{\mathbb R}g(x)e^{sx}\,dx$ and $D=C_3'/C_3$.
The reflection with the self-dual character gives
$D(z)=-D(1-z)-\log 3$. In the upward left leg at $-1/2$, the
substitution $s=1-z$ reverses the endpoints and contributes a minus
Jacobian, with no net orientation sign. The normalized upward
right-minus-left difference is therefore

$$
\frac{1}{2\pi i}\int_{3/2-i\infty}^{3/2+i\infty}
  (M_g(s)+M_g(1-s)) D(s)\,ds + \log 3.
$$

Mellin inversion at zero makes the contact $+\log 3\,g(0)$.
Multiplying $C_3$ by $3^{s/2}$ shifts $D$ by $(\log 3)/2$.
That adds the same normalized $(\log 3)/2$ to each original
upward leg for this test, so the difference is unchanged. In the
reflected expression the explicit contact disappears because each
of the two right-line terms now contributes half of it. Exact
function equality transports the tested logarithmic derivatives
and the full-order, no-pole exhaustion, not merely the zero sets.
The pass checked the orientation and inversion against
`Proofs/Theorems/DirichletContourReflection.lean:26–70` and
`Proofs/Lemmas/CompactLogMellinInversion.lean:95–147`; the existing
endpoint is `Proofs/Theorems/DirichletThreeResidueExhaustion.lean:88–102`.

Reader `dbHfHNi` independently inspected rendered PDF pp. 614–615,
(B.4.2.2–4). The literal (B.4.2.3) prints plus signs on both the
reflected derivative and the conductor term. Ordinary differentiation
requires both minus signs. The printed (B.4.2.4) has the corrected
integrated signs but does not follow from the literal (B.4.2.3).
These visual readings are attributed to the pass readers, not a
new inspection at closure.

**Checks and limits.** The reader outputs are
`13b1d0ed2c72c0cb9cf45e698e06ec899a2dbc98` and
`ec641661f0829fb196f0d7ae6de45742d749bbcb`, respectively. Closure
confirmed that both outputs are empty changes and their workspace
base agrees with the fixed pin on the cited comparison inputs.
Synthesis reports that a fresh independent informal critique found
no normalization, uniqueness, or orientation error under the
checked premises. It did not inspect the source or run Lean. No
build, axiom replay, or new proof landing occurred in this cycle.
The concrete descended character, weighted unfolding, and entire
function equality were not formalized. The generic factorization in
`Proofs/Theorems/IdeleZetaIntegral.lean:67–89` and odd Gamma evaluation
in `Proofs/Theorems/RealGaussianMellin.lean:52–56` are inputs to a
possible formalization, but the specialized Schwartz-Mellin route's
flatness at zero fails for $xe^{-\pi x^2}$, whose derivative at zero
is $1$.

## Outcome and reopening condition

The transported contour counts every zero of this one completion
with full analytic multiplicity and no pole terms. It does not give
a critical-line result even for this character. The local bridge
left by the prior attempt is resolved informally only. The trace
assembly check in `.godel/obligations/trace-assembly.json` verifies
algebra, not the analytic hypotheses. The unresolved premise in
`.godel/obligations/trace-to-zeros.md:95–142` is that both evaluations
compute the same Haar-relative global positive-width diagonal on
matching tests. The quotient-to-idele lift must preserve the shells;
the terminal projection, cutoff and limit order, and the orbital
terms must be fixed. The global $S$-piece must be identified with the
normalized local expression after the necessary Mellin subtractions,
not replaced by an $S$-local multiplier. Conductor, identity, pole,
and central-zero contributions must be accounted for separately.

Reopen this GRH route only with that common diagonal specified well
enough to compute both evaluations on the same Mellin tests. A
rational check, even if successful, would still leave the analogous
comparison and analytic inputs for all fields and all continuous
unitary characters, including weighted Gaussian continuation with
correct polar terms, a normalized functional equation, and contour
exhaustion. Full Masullo GRH was not established; success at that scope
would require a separate rigorous audit.
