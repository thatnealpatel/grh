# Built signatures in the local Lean audit

## Decision

An exact-candidate kernel and axiom audit did not include the built
statements. Independent statement review and a separate `#check` run
were needed for the adoption decision. The separate run is easy to
omit or accidentally leave attached to the previous candidate after
a restack.

- Main run `01a200f6-cd75-715f-91d5-f96a05e4eefe` launched
  `41a17038c27c9ec7962e61a3cdf2b8048350dcf1`, with the same `cmd/godel`
  tree as the audited proof revision
  `d409f825a1ad2d57a50680d1551a43a9d74cbe48`. Yah work session
  `01a200f6-ceba-7622-963f-8bc1fe2cf743` ran the corrected kernel and
  axiom audit, then a separate built-type check (seq 106), before
  adopting that exact revision (seq 113). The first audit was
  cancelled after the worker spotted two incorrect endpoint names.
- Companion improvement session `01a200fa-4809-7509-bd30-9ffb44715d77`
  found a separate built-type check on an earlier candidate, not the
  accepted restack `f42386b6187314c36b80790b8b00806a179600a3`. It added
  a reminder in `6d279e8fedb22afcb3db41e1e6b837099d0c890e`. Neither
  incident shows a wrong theorem statement getting adopted. Selecting
  the correct endpoints is still the caller's responsibility.

## Bounded trial

In improvement session `01a20102-7cbf-7fef-869f-96df6c51ce37`, use the
finished integration workspace for `d409f825` and run
`lake env lean --json --stdin` with this source:

```lean
import Lean
import Props.ArchimedeanGammaRightLine
set_option pp.fullNames true
open Lean in
run_cmd do
  for d in ([`Masullo.compactLogMellin_archimedeanGamma_pair] : List Name) do
    logInfo (m!"endpoint signature '{d}':\n" ++ .signature d)
#print axioms Masullo.compactLogMellin_archimedeanGamma_pair
```

`MessageData.signature` is the pinned Lean printer used by `#check`
for a declaration identifier. The control (`tagged-signature-control`)
returned one informational JSON record with the complete multiline
signature and one with the three allowed axioms. A plain `#check`
control exposed the same hypotheses and conclusion. No proof routing
or theorem code was changed in the trial.

## Promotion

Record exactly one signature per requested endpoint in the existing
local audit, from the same Lean invocation as provenance and axiom
checks. Do not transfer signatures from an earlier revision. Inspect
the reported signatures against independent review before adoption:
the parser checks the receipts, not whether a statement is the intended
one. The legacy remote audit does not require or emit signatures.

Regression tests cover missing, duplicate, empty, unrequested, and
warning-level signature diagnostics, as well as multiline signatures
and primed names. The live promotion check is the revised CLI on the
exact program candidate, with the unchanged Lean inputs and the same
three Archimedean modules and nine endpoints as the work run.
