# Blitz outcome: Full Masullo GRH

**ATTEMPTED.** The selected conductor-three horizontal-exhaustion check
succeeded and landed in Lean. It locates no zeros and does not prove
full Masullo GRH or classical RH. Finish reason: `attempted: synthesis
ended the attempt`. The intermediate stopping condition was met on
pass 3, the cap was exhausted, and no further pass was opened.

## Evidence, target, and opening plan

- **Original evidence:** `af2e69d9f26188e34fe1b98c901a5c76533edb46`,
  selected from campaign status. Later integration bases do not change
  the pin. Lean `v4.36.0`; Mathlib
  `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`.
- **Edition:** Alessandro Maria Masullo, *The Music of the Primes*,
  940-page PDF, SHA-256
  `e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5`,
  matching the [source pin](../sources/masullo/README.md).
- **Target:** Unconditional critical-line location of every nontrivial
  Hecke zero of every continuous unitary idele-class character of every
  number field, including ramified characters. The scope reading at PDF
  p. 6, Acknowledgements, and p. 528, §14.1.2, is attributed to the
  rendered review recorded in
  [the prior decision](decision-01a202cd-7acf-7edb-97ce-044d9614d43e.md),
  lines 78–87. The multiplicity bound and the higher-rank conjecture
  are separate. A rational specialization, conditional implication,
  or isolated contour lemma is not the target.

The opening selected one intermediate obligation: Horizontal exhaustion
for Mathlib's completed Dirichlet L-function of the odd primitive
quadratic character modulo 3, `padicRamifiedThreeCharacter`, across
$-1/2\le\Re s\le3/2$. The pin supplies vertical reflection and the
conductor contact at $a=3/2$, not the horizontal limits. No saved
selection in the opening evidence duplicated this exact check.
Classical RH was assessed but not selected: The unconditional rational
full-order explicit formula and local fixed-annulus trace do not give
the Haar-compatible global diagonal with its terminal right projection,
compatible cutoffs, and both Mellin subtractions. The upstairs
norm-one Haar double-section lift gives zero against the unshifted
prime-two value $\log 2$, and the same-chain right mask independently
erases a shell. These reject the proposed identifications, not RH.

The unchanged opening plan began in INFORMAL mode with two independent
parts. A was to verify exact-character nontriviality and entireness,
recover the uniform $\Re s=2$ Möbius anchor without using the
product-specific conclusion, and test the radius-six disk and height
lemmas on the two reflected ordinate lists. The proposed output was a
common height in $(n,n+1)$ for both tails, with reciprocal and
fixed-radius Cauchy derivative bounds across the strip. B was to take
only that bare estimate as a hypothesis, verify the shifted odd Gamma
factor and its uniform logarithmic-derivative bound, distinguish
Mathlib's completion from conductor normalization, and use
`compactLogMellin_vertical_decay` to check both horizontal limits for
every smooth compact log profile. B was also to inspect rendered PDF
p. 614, §B.4.2.1, (B.4.2.1–2), and distinguish the printed argument
from the repair. No direct visual reading was verified.

Switch to LEAN only after independent critique confirms that heights,
strip, and completion agree, with pinned declarations or bounded proofs
for the transfers. Otherwise use another INFORMAL pass only for a
specific repair that can change the verdict. Any Lean landing requires
independent statement review, targeted builds, built-signature and
transitive-axiom checks, and confirmation of exact candidate adoption.
Stop within three passes total once an independently reviewed Lean
endpoint gives the common zero-free heights, uniform polynomial bound,
and both limits, or sooner if a precise unsupported premise has no
bounded repair. At the cap, report only what was checked. This stop
never substitutes the local result for full GRH, which would require a
separate rigorous audit.

## Pass 1: INFORMAL

Ordinary-math success, not a Lean landing. Contributor A
(`81e78fa8603fcc5af26669949efd422c9f9772f2`) used primitivity at level 3
for nontriviality and entireness, the private character-generic Möbius
anchor in `DirichletRightAnchor`, and the degree-six bound in
`DirichletLFunctionGrowth` on the disks centered at $2\pm i(n+1/2)$.
`AnalyticGoodHeightDisk` and `LogLossGoodHeight` apply to the tagged
union of upper ordinates and negated lower ordinates, preserving
multiplicities. The combined logarithmic loss is $O(\log(n+1))$,
giving a polynomial reciprocal bound on both segments, and unit-circle
Cauchy bounds the bare derivative. The product-specific good-height
conclusion did not transfer. The opening's height index here is for
positive $n$.

Contributor B (`dd66951d813c0a8dc88fc55fa3250c4802639335`) checked the
odd factor $\Gamma_{\mathbb R}(s+1)$ from pinned Mathlib's
`DirichletContinuation`. It is nonzero across the strip; the subtracted
Gauss integral in `GammaRealLogDerivative` gives linear growth of its
logarithmic derivative. In that estimate, for $w=s+1$ the kernel is
bounded by $|w-2|(1/2+x)e^{-x/2}$, which integrates to $5|w-2|$.
Decay of order $m+1$ against the completed bound $C(1+T_n)^m$ makes
each length-two horizontal integral $O((1+T_n)^{-1})$ for a fixed
smooth compact log profile. The heights are independent of the profile.
Multiplying the completion by $3^{s/2}$ adds $(\log 3)/2$ to its
logarithmic derivative; the added contacts cancel in the matched
right-minus-left expression, not on either vertical line individually.
This does not identify an idelic completion.

The pass synthesis and independent informal critique found the estimates
compatible on the same heights, strip, and completion. Both contributor
outputs were empty revisions; no endpoint was elaborated, built, or
kernel-audited. Layout and raster OCR did not verify the p. 614 reading.
The apparent upper-versus-lower height-bound issue at PDF pp. 604–605,
Def. B.3.1.1 and Lemma B.3.1.2, also remains provisional. The repair
uses the direct lower bound $T_n>n$ and does not rely on that passage.

## Pass 2: LEAN

Checked the unconditional endpoint in isolation, but did not land it.
`bare-heights` (`97e4add04db44fc0ff3c624457737951295912bc`) proved
`Masullo.padicRamifiedThree_bare_good_heights` using the generic anchor,
radius-six growth, real-character conjugation to share the heights
between tails, and Cauchy control. `completed-edges`
(`20dfb1dcaba89c3de410f6cecbe8bc65a260fa29`) independently proved
`Masullo.padicRamifiedThree_completed_horizontal_of_bare`, the
conditional Gamma and Mellin transfer. The wrapper discharged that
bare-estimate premise and chose $T_n\in(n+1,n+2)$ for $n\in\mathbb N$.

Both helper builds passed. The independent source statement review
`763b6f288bf6eca2fd8fa7f90bd61b1b25c8e19e` distinguished the conditional
helper from the endpoint. For complete checked output
`e815041e181080307be679c71028b42ea8a024d1`, the targeted
`lake build --wfail +Theorems.DirichletThreeHorizontalExhaustion` and
joint import confirmed the intended built signature and ten complete
transitive axiom reports limited to `propext`, `Classical.choice`, and
`Quot.sound`. Owning session `01a204e5-d7e5-7005-905f-23fe74fc730e`,
transcript entries 52, 95, and 120, records review, build, and joint
check.

Helper integration `5da95d9f8d2dabf9419f3f1adda40b12b0c5b875` on
`c39dc760e774083bf3154616de7f568b90c9c50e` went stale while the
wrapper was checked. Replay returned `unknown integration candidate`
as the accepted base advanced. The last observed accepted revision in
that pass was `a39f740d031ebe4afe2c49f6f5d1fb40c6324813`; fresh
allocation returned `a direct workspace is already pending`, so edits
stopped. The complete checked output was unadopted. Its checks did not
cover a replacement revision.

## Pass 3: LEAN

Recovered and landed the same eight-file patch on base
`6f1d672bc14e2f53d6fc17f45019bf1b61e64e8b`. The exact candidate
`56db126833c651350062b7de70fcc8a8e5ee1f5a` was adopted with
`stale=false`. Its diff against that base is byte-for-byte identical
to the patch from `c39dc760e774083bf3154616de7f568b90c9c50e` to
`e815041e181080307be679c71028b42ea8a024d1`. The owning workspace
matched the candidate source and Lean/Lake inputs. The closing review
confirmed the exact patch match, non-stale adoption record, and
ancestry of the accepted closing base.

Independent statement review `1704dda2f3543136e50797cf3f74e7d672309246`
checked the exact character, helper hypotheses, quantifier order, and
orientation of both edges. Independent recovery review
`c5eeca8a62d48c663b8147ce1b039b4ceca124f4` checked patch and declaration
provenance, including retention of the refactored product theorem's
statement. In the owning integration workspace, `lake build --wfail`
passed for all 18 changed or transitively importing project modules.
A fresh joint import matched the built signatures to the review, and
all ten complete transitive axiom reports were limited to `propext`,
`Classical.choice`, and `Quot.sound`. Owning session
`01a204f1-4b12-7a69-92e2-c41744de5a1e`, transcript entries 32, 37,
and 39, records build, joint check, and adoption. This resolved the
pass-2 landing blocker.

## Final result and reopening condition

The accepted theorem `Masullo.padicRamifiedThree_completed_horizontal`
([source](../../Proofs/Theorems/DirichletThreeHorizontalExhaustion.lean),
lines 22–35 at landing) assumes no bare estimate or zero-location
result. For Mathlib's completed L-function of the exact odd primitive
quadratic character modulo 3, it gives one sequence $T_n\in(n+1,n+2)$,
a constant $C>0$, and a natural exponent $m$. At both heights
$\pm T_n$ over the entire closed strip $-1/2\le\Re s\le3/2$, the
completion is nonzero and its logarithmic derivative has norm at most
$C(1+T_n)^m$. Both horizontal integrals of the compact-log Mellin
transform times the logarithmic derivative tend to zero for every
smooth compactly supported complex log profile, with the same heights
for all profiles. The integrals are both parametrized left-to-right;
reversing the upper one for a counterclockwise rectangle preserves
its zero limit.

This is a local repair for Mathlib's completion without a conductor
power. Its mapping to PDF p. 614, §B.4.2.1, (B.4.2.1–2), remains
provisional without verified direct rendered-page inspection. The
landed theorem does not verify the printed general slow-growth premise,
its test class, or the residue identity. The inherited rendered review
in [the divisor-heading record](../obligations/divisor-heading.json)
found no standalone divisor statement at PDF pp. 522–523,
Thm. 13.3.1.2; the preceding theorem's restricted tests and capped
orders do not give full-order agreement.

Reopen only as a separately authorized attempt. The next bounded GRH
check is whether the landed heights support conductor-three residue
exhaustion with full zero multiplicities in the tested strip for the
same profiles. A successful check would still require identification
with the normalized idelic completion and a same-test common
positive-width diagonal, with conductor, identity, pole, and
central-zero terms accounted for separately. A failed transfer rejects
that connection, not GRH. For the unselected classical RH route, reopen
only after a Haar-compatible lift identifies the actual global kernel
at one common positive width with the shell-preserving terminal right
projection and compatible cutoffs; the short bump derivative can then
be tested with level exhaustion before position exhaustion and the
orbital term kept separate from the Mellin subtractions. Neither
control would settle its full target.
