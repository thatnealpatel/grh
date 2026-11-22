# Recover the checked character proof

**Decision:** Recover the upstream proof rather than follow the scratch
handoff downstream. No router or retry loop was installed.

Run `01a2010e-11be-7d28-b7f1-966866bfc36a`, work session
`01a2010e-125b-7b4a-907b-8447e5b76a69`, launched the
`91921fc1d3de2c64a3349e59e74e3d82eb967cdf` archive. In that work
session `status` reported this seed, but `new` on it returned
`resolve direct base: unknown integration candidate`. Work continued in scratch;
Yah reviewer `rlvOLyV` independently approved the statement. A later
`status` resolved `d9e8169ccb20e4fc74ca084540bcabdca09b7b87`, but `new`
returned the same error. Neither call produced a candidate. The saved
source then passed warning-as-error elaboration, separate kernel replay,
and a built signature and axiom check in scratch. That is not a full
candidate audit. The work artifact and check logs are in
`/tmp/grh-character.wl9Bxo1P/`; its result and runnable successor are
recorded in the [proof handoff](../../obligations/hecke-right-line-majorant.md#continuous-one-parameter-character-classification).

**Recovery control:** In improvement session
`01a20114-4aae-7459-b5c8-bb52f9adc5cf`, the accepted base had advanced to
`616c5a9723c8342162bd3f3647cd07a4fa84ad06`. The two intervening accepted
changes since launch affected neither `cmd/godel` nor the Lean inputs.
One `new` on that current base produced a writer workspace. This shows
that the route reopened, not why it failed in the prior session. The
recovered module removes only the scratch axiom-print diagnostic and
has SHA-256 `3e4162057d8965488534081cb9bab0e2931e26b6c38a7adb8087921aa985c3d3`.
The exact-candidate `audit-local` command is in the proof handoff.

**Outcome:** Candidates `28fbbe896c73068eb7ff4aeb68e7370bdfc55527` and
`0a4a31f8b0d8ad4a3753f703d7614cc3f30b38aa` passed the full local audit,
but both adoptions were stale. The first advancing base added
`Proofs/Theorems/IdealClassSplitPrimeSign.lean`, so the second candidate
needed an ordinary audit. The next advancing base changed only
`cmd/companion/nodes.go`. We compared the Lean and Lake inputs, seeded
from the second candidate's trusted build cache, repeated the full
audit on `eba0e8a9fe1ad6a88f22b4f6ef6deeee8fcf9783`, and adopted that
exact revision after comparing the built endpoint with the review.
This is a recovery result, not evidence for changing the live router.

**Comparison:** The preceding run `01a200f6-cd75-715f-91d5-f96a05e4eefe`
(work `01a200f6-ceba-7622-963f-8bc1fe2cf743`, improvement
`01a20102-7cbf-7fef-869f-96df6c51ce37`) used the archive at
`41a17038c27c9ec7962e61a3cdf2b8048350dcf1`. It integrated the Gamma pair
and recovered a later stale adoption by restacking the audit-tool
change, a different failure phase. No evidence supports a program
change for the workspace rejection; the current recovery procedure
preserves the reviewed proof and still requires the full audit.
