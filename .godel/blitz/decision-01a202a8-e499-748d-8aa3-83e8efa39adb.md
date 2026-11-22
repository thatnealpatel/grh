# Blitz decision: Decline classical RH and full Masullo GRH

**Outcome: NOT_ATTEMPTED.** Neither target warrants a bounded blitz now.
No proof pass, fresh Lean audit, or intervention in either proof loop
occurred. Neither route has the inputs for its bounded comparison, and
neither exact comparison is confirmed to be unassigned.

**Pinned assessment evidence:** `2c9b7906b3d85c3a2dd116ccf80d302984346b5e`.
The preceding decline, `decision-01a20284-a30b-7c3c-beea-693f7b8f682b.md`,
was adopted at `97f291ff01f580d40d1a2e2be22aae67ed085769` on evidence
`8fa08a83fc7120f12fba0263b06ee73f44c4a812`. The rational route is
unchanged, but general-field norm splitting, algebraic ideal-class
maps, a local conductor endpoint, and the singleton-isotype results
below materially change the GRH inventory. This is a new decline, not
an attempt or a repeat of that note.

The pin uses Lean 4.36.0 and Mathlib
`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. The checked local PDF digest is
`e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5`,
the pinned 940-page edition of Alessandro Maria Masullo's *The Music
of the Primes*. Page citations are one-based PDF ordinals. Rendered
readings are attributed to the readers, not newly certified by closure.
Closure checked the pinned statements and the cited landings at their
exact revisions; it did not replay their mathematical audits.

## Classical RH

The target is Mathlib `RiemannHypothesis` for the Riemann zeta function.
`Masullo.rationalIdeleRadial_explicit_formula`
(`Proofs/Theorems/RationalIdeleRadialExplicitFormula.lean:34–49,66–75`)
is unconditional: For smooth compact log profiles it gives the
absolutely summable full-order zero sum as the two polar Mellin
moments at $s=0,1$ minus the real and finite local terms, on actual
normalized rational idele-class Haar. This is a scalar project repair,
not an operator trace. Its correspondence to PDF p. 614, (B.4.2.2),
and p. 623, (B.4.4.16), is provisional.

`Masullo.riemannHypothesis_of_strip_test_agreement`
(`Proofs/Props/ZetaTestSumComparison.lean:30–39,77–109`) is conditional.
It needs arbitrarily small positive half-widths with one family of
natural weights per width, bounded by full analytic orders and zero
outside the closed centered strip, giving agreement with the full sum
on **every** smooth compactly supported positive-log test of integral
zero. Agreement for that whole class at one width gives a strip bound,
not RH. A full-measure set of widths in the weighted rational spectral
model (`.godel/obligations/trace-spectral-strip-q.md`) does not establish
even one width common to the actual global spectral and geometric
evaluations.

The inherited rendered review in `.godel/obligations/trace-assembly.json`
verifies the algebra of equating two evaluations of one Haar diagonal
and transposing both Mellin terms (PDF pp. 519–520, Thm. 12.5.1.1,
(12.5.1.1–4)), not either analytic evaluation or their common domain.
`decision-01a20240-39f6-7778-8369-892e00fbbf16.md:42–60` attributes
rendered checks of the insertion marker (PDF p. 514, §12.3) and the
missing terminal right projection in the claimed limits (PDF
pp. 488–489, (11.2.1.4), (11.2.1.9)). The fixed-position project
repair retains that projection (`.godel/obligations/trace-hardy-diagonal-q.md:234–257`),
but does not identify the actual rational global $S$-piece, shell lift,
or right orbital cutoff. The geometric dependency reading is provisional
(PDF pp. 494–496, (11.3.1.4), (11.3.2.3); pp. 517–519, (12.4.1.8–12),
(12.4.1.23–28)); so are the source dependencies for the missing common
Sobolev and edge admissibility (PDF p. 454, (10.3.2.3–4), p. 463,
Thm. 10.4.2.8, p. 473, Def. 10.4.3.7).

The short-bump control is already recorded in
`.godel/obligations/trace-to-zeros.md:84–134`. For $f=b'$, where
$b$ is a nonzero nonnegative smooth bump supported in $(0,\log 2)$,
mass and prime samples vanish but the $+1/2$ Mellin moment is
$-\tfrac12\int e^{x/2}b(x)\,dx\ne 0$. The specified joint local
projection supplies the $-1/2$ subtraction and misses the $+1/2$
subtraction. Vanishing prime samples does not prove orbital vanishing.
The local limit thus cannot substitute for the level-first global test.

**Reopen RH** after confirming the diagnostic is unassigned,
identifying the actual rational global $S$-piece, shell lift, and right
orbital cutoff with the terminal right projection retained, and
establishing one common admissible half-width $0<\alpha<1/2$. In the
trivial compact isotype over $\mathbb Q$, compare the strip evaluation
against the actual orbital contribution and both Mellin subtractions
on $b'$, taking the level limit at fixed position support before
exhausting position. Test the orbital contribution separately from
prime sampling.

## Full Masullo GRH

The target is location on $\Re s=1/2$ of every nontrivial Hecke zero
for every number field and every continuous unitary idele-class
character. The cycle assessor inspected rendered crops of PDF p. 6,
Acknowledgements, and p. 528, §14.1.2, corroborating the inherited
scope review cited by the preceding decision. The noncentral
multiplicity bound and broader automorphic conjecture are separate
(PDF pp. 528–529, §14.1.2, Conj. 14.1.2.1). A rational specialization,
conditional implication, or singleton example does not discharge GRH.

- The different extension (`89b5f3ecde2f4a9c88eda26d36959f71f1a54eaa`)
  and `DiscriminantNormalizedIdeleHaar.lean:39–52`
  (`002582a9c417a34219ff7c000b722972067b021f`) give regular Haar on
  actual ideles with prescribed product stages and finite-unit factor
  $|\operatorname{disc}K|^{-1/2}$. This is upstairs calibration, not
  the norm-one quotient covolume. The combined comparison to the
  manuscript normalization is provisional (PDF pp. 556, 558–560,
  (A.3.1.2), (A.3.1.8), (A.3.2.1–2), (A.3.2.5)).
- `DiscriminantNormalizedIdeleHeckeGaussian.lean:37–54`
  (`9686ddf56f31de989478bca96b0898d52a9314bc`) gives the corrected
  absolutely integrable Gaussian pairing for each unitary character,
  with a fixed exceptional set and measure for all $\Re s>1$. The
  value is the completed **Euler product** times the discriminant
  factor, not a continued completion or a contour. The opposite
  complex angular weight is a project repair: Inherited rendered
  review in `.godel/obligations/complex-gaussian-angular.md`, PDF
  pp. 124, 130, 151–153, (3.2.2.1), (3.3.1.7), (3.4.3.1),
  (3.4.3.5), (3.4.3.11).
- `IdeleLogSplit.lean:54–119` (`57861b4dffce4629279593eb19764965b5ccdb5b`)
  gives compatible multiplicative topological splittings on ideles
  and classes using the continuous homomorphic log-norm section.
  The assessor's rendered reading of PDF p. 547, Lemma A.2.2.9,
  (A.2.2.12), found a continuous section hypothesis; the project
  uses homomorphicity for the multiplicative equivalence.
  `FiniteIdeleIdeal.lean:43–102` (`009a095f225482d741ac7ce82a09003ce69f8945`)
  gives the surjective finite-idele fractional-ideal map, valuations,
  principal-diagonal law, and integral-unit kernel.
  `IdeleIdealClass.lean:59–205` (`04ff9a764596ec2f8b425fbb9b56535ae2ef190f`)
  gives the ideal-class maps and algebraic kernels, including
  norm-one surjectivity. The comparisons to PDF p. 549,
  (A.2.3.12), and p. 552, Prop. A.2.3.9, (A.2.3.23–24), are
  provisional. None of these determines the quotient mass.
- `PadicConductorFourier.lean:167–185,223–234` at the pin proves
  primitive counting DFT modulus $\sqrt N$ at 1 and the negative-sign
  central Fourier modulus $p^{-n/2}$ at $p^{-n}$ on $\mathbb Q_p$
  with additive $\mathbb Z_p$-mass one, including $n=0$; the
  positive-level shell statement is separate. This does not prove
  the phase, local zeta-integral functional equation, finite-extension
  analogue, or global reflection. The rendered source comparison is
  inherited through `.godel/obligations/hecke-right-line-majorant.md:521–561`
  for PDF p. 136, below (3.3.1.30), and p. 141, (3.3.2.24).

The conditional reflection lemmas (`Proofs/Props/HeckeContourReflection.lean:28–32,55–70`)
assume the functional-equation germ or reflected log derivative and,
for the integral, right-line integrability. They do not assemble
continuation, conductor and reflection identities, divisor and
shifted polar data, or contour exhaustion for general characters.
Source dependencies remain provisional (PDF pp. 124–127,
Thm. 3.2.2.1; pp. 135–141, §3.3; pp. 614–615, (B.4.2.1–4)).
A normalized common global diagonal is also missing. The reviewed
$\mathbb Q(\sqrt{-5})$ pole test in
`.godel/obligations/trace-window-q-sqrt-minus-five.md:3–13,35–51`
separates local pole order one from raw norm-one volume $\pi/\sqrt5$.
Its raw-Haar reading of PDF pp. 519–520, Thm. 12.5.1.1, is
provisional. Rescaling removes this obstruction, not the need to
identify both evaluations.

The assessor's rendered crops corroborate the independent two-reader
review in `.godel/obligations/divisor-heading.json`: PDF pp. 522–523,
Thm. 13.3.1.2, contains a heading, unresolved reference, and insertion
note, not a stated divisor theorem. The preceding Thm. 13.3.1.1
(PDF p. 522, (13.3.1.1–5)) is a capped critical-line trace with
Mellin-jet conditions, not the full divisor or a positive-width
comparison.

**Reopen full GRH** after confirming the diagnostic is unassigned
and specifying an admissible ramified-isotype test at positive width
on which both a completed contour and a normalized common global
diagonal can be evaluated. Compare full-order and strip-supported
residues, tracking central and identity terms separately.

## Overlap and stopping condition

Companion landings `aceedd47ecbce262ef762eb415ee425b35c47399`,
`b529450077af23872e7c38ebdb87739e35af5850`, and
`d668388c053856ee44823abc6202705076b206bb` are independently
reviewed ordinary mathematics, not Lean. For the weight-four
left-action conjugate isotype over $\mathbb Q(i)$, $I=\{0\}$ and
Sobolev index $4$, they give inclusion of compact frequency multiples
in the Gaussian theta closure, trace class of the actual uncut
composition $P^{\mathrm{spec}}A$, and continuous descent of value jets
and of first derivatives at zeros of order at least two. Inherited rendered
locators are PDF p. 124, (3.2.2.3), p. 434, (10.1.1.3), p. 459,
Thm. 10.4.2.1, (10.4.2.5), and pp. 440–442, Thm. 10.2.1.1,
(10.2.1.5–6), (10.2.1.9). Reverse closure inclusion, scalar trace
evaluation, common diagonal, and positive width are not supplied.
Run `01a20298-6b19-764d-9c5d-71c4a99424dc` reported the local conductor
modulus landing at the pin and pointed next to an exact local
conductor-level check. This is not ownership of the ramified
positive-width comparison.

The manuscript loop's post-pin strict ideal-class landing is now
visible at `d171b684ba31797bdcdb50b71ebbdf4f6dc7eaed`:
`IdeleIdealClassStrict.lean` establishes the closed kernel embeddings
and open quotient maps for ideles and norm-one ideles. Its record in
`.godel/obligations/single-place-norm.md:181–226` attributes independent
statement review and lists the audit endpoints. It points next to an
Archimedean compact cover, before any disjoint fundamental domain or
quotient-volume calculation. This is off-pin prerequisite progress,
not evidence of either comparison and not a change to the assessment
pin. Neither loop was directed or modified by this cycle.

The records establish overlap on prerequisites, not assignment of
either exact diagnostic. A mismatch on one test rejects the proposed
comparison; a match warrants broader testing, not a claim of RH or
GRH. Neither hypothesis was proved, refuted, or attempted here.
