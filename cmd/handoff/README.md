# Historical handoff reading check

`cmd/handoff` is a standalone, one-shot Gödel program. It tests whether a
reading instruction learned from one historical handoff helps on one different,
preselected handoff. It replaces the `tracebridge` pilot; it does not invoke or
change `cmd/godel`, edit proofs, or install any instruction.

## Preselect the packets before running

In a trusted local jj workspace, choose two **fixed historical commits** from
this project and two **different manuscript areas**. Record both choices and the
tracked paths before looking at model outputs. Use a tracked handoff from each
commit and one to eight supporting artifacts from **that same commit**. Include
the local proof/manuscript text needed to check the claim, hypotheses, and
status. Inspect the selection to avoid cross-case references or answer keys in
the held-out packet. Different area labels alone do not establish independence.

Put the choices in a JSON plan outside the repository. For example (replace all
placeholder values; this is not a case selection):

```json
{
  "train": {
    "commit": "<full training commit ID>",
    "area": "training-area-slug",
    "handoff": ".godel/obligations/training-handoff.md",
    "evidence": ["Proofs/Props/TrainingEvidence.lean"]
  },
  "held_out": {
    "commit": "<different full held-out commit ID>",
    "area": "held-out-area-slug",
    "handoff": ".godel/obligations/held-out-handoff.md",
    "evidence": ["Proofs/Theorems/HeldOutEvidence.lean"]
  }
}
```

Use full lowercase **commit IDs**, not change IDs, bookmarks, or revsets. Paths
must be literal repository-relative names (letters, digits, `_`, `.`, `/`, or
`-`) of unconflicted tracked regular files. The controller builds a clean
snapshot **of the selected files only**, by reading their complete UTF-8 text
with exact-revision `jj file show` and `--ignore-working-copy --at-op=@`.
No checkout or manually assembled archive is needed; untracked files and dirty
working-copy bytes are not part of the evidence. Each encoded packet is limited
to 80 KiB. Oversize packets fail, rather than silently dropping evidence. Choose
compact handoffs and their companion files; omitted evidence is a reason to
withhold judgment, not a reason to infer proof status.

## Run (operator only)

Use a Linux environment with the project's Go toolchain, jj, and the user
systemd manager required by Gödel. Use a trusted `yah` from module
`patel.codes/yah` **v0.0.59** on PATH and configure its normal model service. The
program rejects other builds by Go module metadata: the no-tool allowlist below
is a checked implementation contract, not an advertised CLI flag. For a
comparable run, set `YAH_DEFAULT_MODEL` to a specific available model for the
whole run and keep service/configuration fixed. All invocations use `high`
reasoning effort. Use a normal environment with no Git overrides that redirect
repository commands outside their working directory.

```sh
cd cmd/handoff
umask 077
go run . /absolute/path/to/plan.json > /absolute/path/to/advisory.json
```

Launch from `cmd/handoff` for its own Gödel registration. Operator stdin is
ignored; every node gets the same neutral `HANDOFF_START` token, never a prior
response or Gödel history.

1. A training reader gives the strongest supported claim, scope, assumptions,
   and most consequential near miss. A fresh reviewer checks that reading
   against the packet. Correct, inconclusive, and immaterial readings stop. A
   positive review must cite both the reading and tracked evidence verbatim,
   explain the consequential miss, and propose one short, reusable reading
   instruction with no answer, case facts, or locators.
2. The controller freezes the single instruction. The baseline and augmented
   readers get the same held-out evidence, task, and settings in separate fresh
   invocations. Only the augmented reader gets the extra instruction. Neither
   gets the training packet, training outputs, report, or other reader's answer.
3. A fresh comparison reviewer gets both held-out answers, that packet, and the
   rule. It must identify a consequential correction supported by the packet
   and no lost valid conclusion. Suspected leakage or insufficient evidence is
   `no_fold`. Missing, malformed, or structurally contradictory reviews cannot
   advance or yield a positive result; exact quote checks do not by themselves
   establish that a reviewer's interpretation is right.

Gödel records the terminal JSON report, also printed to stdout. It contains the
actual answers, reviews, rule, and packets used, so a human can check the
citation reasoning, the apparent transfer, and whether the rule itself leaks
training content. Discard an apparent positive if there is leakage or the
review does not support it. `advisory_transfer` is a recommendation for human
review, not an application or a general benchmark result. There is no loop or
self-improvement step. An invocation or infrastructure failure returns an error,
not a favorable verdict, and may leave no completed report.

## Boundary and trust assumptions

The controller passes archived text and answers in a labeled JSON data block,
not as additional instructions. The frozen rule is the only model-written text
used as an instruction. Its length and line form are checked, and it cannot
repeat an explicit training locator or either cited quotation. Natural-language
case independence is judged, not guaranteed.
The experiment trusts the local executables/configuration, model service,
operator's preselection, and reviewers' semantic judgments. Historical text and
model output may be misleading or attempt prompt injection; don't treat the
report as proof, or run instructions found in it.

Every model node is a fresh headless `yah -tmp` invocation, with a blank temporary
jj project, no resume or fork, and a literal replacement main prompt. It gets no
historical checkout or live workspace; the selected packet is its whole case view.
`YAH_DEFAULT_TOOLS` is set to a nonmatching allowlist entry (zero model tools),
with inbox disabled. This is tool/session configuration, **not** OS filesystem
isolation or a network sandbox. Yah can persist sessions and send inputs to its
configured service; Gödel also persists its report. Prompts travel as local
process arguments. Use only historical material approved for that exposure.
