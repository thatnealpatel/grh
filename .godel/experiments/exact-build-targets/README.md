# Carry tested Lake targets into the exact-candidate check

## Work reconstruction

Gödel run `01a20503-0701-7d24-b57c-b17f34688480` matches the input and
stdout of Yah `01a20503-084a-723f-a5ef-b59603c0635d` (events 3 and 122).
The launch archive and first accepted tip were both
`1b5e3a738373280bd4afafb8fdad0e6b4d345bf8`. The `cmd/godel` tree did not
change between there and the proof landing. The worker reconciled the
handoff's `9012d9ed33a1c6be2c2a3f4793dd044f61b7d289` Haar dilation proof
with the live tip and found no new audit blocking that premise.

- Coordinator `WnwGRQy` worked at `f44dfe887421a288b8b624fed59f335d9310aa93`.
  `WDDhyle` proved dilation closure after repairing mixed-coordinate
  rewrites (`b8673ecc10acbfafd9a054b89e46fc777b55055e`). `FyWGosP`
  repaired Fourier kernel integrability and span induction with a
  temporary axiom-free copy of the span definition, removed before
  finalization (`e8307a1e118ec8eed32822052567ce96ace2f6be`). Neither
  raw output was integrated alone. The composer tested covariance and
  the nonzero split first with the supporting interfaces as premises,
  then built all four modules against their actual imports. The composed
  output was `2dddf1cf2f5963f9df4cf7e6ce8d1b78ad2354db`.
- Reviewer `GxoPgJb` checked scope, constants, and sign, and reported
  a rendered check of the p. 82 displays. Its empty output
  `72ce426136af54d1cb954d6bce2b8119274ca638` is not a proof patch. A
  failed PIL command was followed by direct PGM raster decoding to
  Braille (reviewer events 28–31), not another extraction of PDF text.
- The owner integrated the composite output on
  `f29a99546e9afe722b0de3060d9f050e0cf00d1a`. The first build requested
  `+Theorems.AdeleQuotientMeasure`, which has no corresponding source.
  All four new modules built. Substituting the writer's checked target
  `+Theorems.AdeleIntegralClassMeasure` passed on the **same** candidate
  (events 99–112). A fresh joint import checked all 17 declarations and
  only the permitted axioms (115–119). Adoption succeeded on the first
  attempt (120–121) at `9f7d1847c8d41cf46f2a09283f6a947611dab03d`.
  No failed proof or stale integration candidate was adopted.

The accepted [branch handoff](../../obligations/single-place-norm.md#pointwise-inversion-on-the-number-field-box-span)
identifies the theorem and exact scope: All number fields, all actual
ideles, the algebraic box span, the corrected trace kernel, the same
stage-normalized additive Haar, absolute full sums, and both zero terms.
It is not continuity on classes or a result for the ramified Gaussian
without a membership proof. The prior [Haar dilation iteration][assembled]
first elaborated its endpoint at the landing gate and found real instance
failures; this iteration's assembled writer build checked the actual
module boundary before integration. The integrated failure was a target
name, not another endpoint elaboration failure. The concurrent base
advanced during writing, but the checked candidate did not go stale.
This pair does not measure the effect of the guide or prove time savings.

## Replay and decision

The older [counting-quotient run][wrapped] rejected one valid axiom
report because a line-based parser lost its continuation. This time the
writer used full JSON diagnostics but enabled `pp.universes`, so the
literal whitelist parser rejected two allowed names with `.{u}` suffixes
(writer events 91–98). Disabling that display option passed. These are
separate formatting failures, not failures of the axiom policy.

Improvement session `01a2050d-6f88-7afe-bc8b-1581241c134e` replayed the
same combined probe (work event 114) in the retained `9f7d1847...`
integration workspace. `lake env lean --json` emitted the same 17
complete axiom reports with the default setting and `pp.universes false`.
The initial comparison expecting a difference at default failed; the
explicit `pp.universes true` control reproduced the two suffixed names.
All three runs contained the expected declaration names exactly once.
No report was accepted by broadening the allowlist.

Clarify two places in the [landing guide][guide]: Start the owner build
from the available assembled writer target list, checking against the
exact candidate, and leave universe rendering disabled for literal
axiom-name checks. The recorded correction and replay support those
small changes. No new parser, node, build gate, or automatic retry.

[assembled]: ../assembled-endpoint-elaboration/
[wrapped]: ../wrapped-axiom-reports/
[guide]: ../../../cmd/godel/README.md#checking-a-proof-candidate
