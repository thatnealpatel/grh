# Evaluation and admissibility (freeze before launch)

The unit of comparison is **one pair of arms**, with the same two briefs in each
arm. The treatment is whether the coordinator starts B after A's successful
terminal or starts B immediately after A's launch acknowledgment. It is not a
comparison of independent theorems, incremental proof development, different
model budgets, or serial versus parallel model inference. A later launch in
`concurrent` can be delayed by admission/selection. Merely requesting two
launches is not evidence of overlap.

## Sealed evidence and gates

With both arms stopped and sealed, adjudicate these gates from the primary
records. Keep the original arm order and include every attempted arm. Do not
retry a lost arm, silently treat it as a failure of Lean, or drop it from the
report. Mark a gate PASS, FAIL (contradictory evidence) or UNKNOWN (missing or
ambiguous evidence); only PASS admits the arm. Cite evidence by receipt and
journal record/sequence number privately. An agent's final prose or zero exit
status alone does not pass any of the proof gates.

1. **Admission and equality.** Check the manifest and admission receipt for the
   expected root/tree/seed, initial accepted/main, protocol and exact command,
   binaries/toolchain, cache and PDF inputs, selector/library configuration,
   model/effort, timeouts and VM/service/network budget. Verify independent
   fresh checkouts/homes and no evidence of other inputs, disclosure across
   arms, unauthorized retrieval or publication. Record provider/selector drift,
   contention and differences even if an arm was already disqualified. Where
   equality is required and cannot be established, mark UNKNOWN; do not claim
   the runner verified cache or provider provenance.
2. **Dispatch and order.** Match the main tool calls/returns and terminal
   notices to the three dispatch journals and campaign inventory. Compare
   actual baseline revision, task text, model/effort, recursion and worktree to
   the protocol, including selector rewrites; verify the actual request model
   where recorded. The A and B task text and reviewer instructions must match
   across arms as prescribed, apart from mechanical candidate identifiers.
   Require exactly one fresh A and B rooted at the seed, no data or steering
   transferred between them, and terminal OK with a finalized output from each.
   Sequential requires the coordinator to observe A terminal OK before
   issuing B, not merely wait for a launch receipt. Concurrent requires the
   second launch at the next opportunity, with no terminal wait or intervening
   work, and a **strictly positive lower bound** on observed writer assistant
   span overlap (defined below). Insufficient resolution is UNKNOWN, not a
   successful concurrent treatment. No retries, repairs, resumption, forks or
   extra agents/workspaces outside the prescribed campaign actions.
3. **Identity and quality.** Use the sealed object store to verify each output
   has only its assigned new source file relative to the seed, and the single
   clean candidate integrated in A,B order contains exactly their bytes, no
   other tree edits, and the expected base. Match one fresh successful review
   journal at that exact candidate, without tracked edits, giving explicit
   passes and actual types for both endpoints against their briefs. Check that
   the unchanged `godel-base` audit ran once in the integration workspace at
   that full candidate ID with the two fixed modules and declarations. Require
   its real exit zero and log of the successful exact-revision build, module
   replay and axiom/provenance audit; record binary digest, candidate, arguments,
   status and log digest. This complements, not replaces, statement review: a
   kernel-valid proof of a weaker claim does not pass. Require one nonstale
   local adoption, with both the campaign's accepted commit and local target
   equal to the audited candidate, no intermediate adoption or publication.
4. **Completion and containment.** Require a clean coordinator exit, complete
   uncorrupted receipt/journals, and service lifecycle evidence, including the
   empty/removed cgroup and externally verified poweroff or destruction. A child
   terminal record, a `Wait` return, or a nominal timeout alone proves neither
   campaign cleanup nor release of all compute. Record missing evidence and
   whether the independent cutoff fired.

## Prespecified measurements

* **Primary: coordinator wall elapsed**, monotonic from just before the one
  Yah `Start` to return from its `Wait`, including startup, selection, waiting,
  integration, review, audit, adoption and coordinator exit. It excludes
  admission/preflight, post-`Wait` observation work, service cleanup, export and
  VM work. Durations in the JSON receipt are integer nanoseconds. An observed
  unsuccessful exit can have a wall elapsed but is not a time to success. If
  only the 2h service timeout or independent VM cutoff is observed, mark wall
  elapsed unavailable and report the cutoff separately, not as a completed time.
* **Writer session elapsed** (`writer_session_sum`) is the sum of A and B's
  baseline-to-terminal intervals. The baseline is persisted before execution.
  **Observed writer active elapsed** (`writer_observed_active_sum`) is the sum
  of their first-assistant-record-to-terminal intervals; it excludes the
  unknown time to first observed execution and includes waits, tools and
  terminal cleanup. Neither sum is wall elapsed for the arm, CPU time, or
  model-busy time. Do not add the reviewer to either sum.
* **Execution overlap evidence** (`writer_assistant_span_overlap`) is the
  length of the intersection of the two first-to-last assistant-record spans,
  not the intersection of launch-to-terminal intervals. A positive bound
  establishes interleaved writer execution evidence, not simultaneous calls or
  continuous progress. Each milestone is bounded by monotonic observations of
  its complete journal line, lower bound at the start of the previous poll
  (or launch), upper bound after reading it in the current poll. Polls are
  nominally a second apart but may be late. An interval length for start
  `[s_lo,s_hi]` and end `[e_lo,e_hi]` has bounds
  `[max(0,e_lo-s_hi), e_hi-s_lo]`. For overlap use the earlier end and later
  start, taking conservative bounds and clamping at zero. These are journal
  visibility bounds, not provider timestamps. A missing start/end leaves the
  metric unavailable, not zero. Preserve the bounds, not a midpoint estimate.
* **Token usage is separate.** Record per-role reported input, output and cache
  counts (and any separately reported reasoning counts), with source/field,
  scope and units. Use complete per-request usage or a documented complete
  per-session total, not both. Do not sum cumulative snapshots, sum cache or
  reasoning subsets into their parent totals, or assume failed requests have
  zero cost. If counts aren't recoverable, mark the affected category/total
  unavailable; explicitly label any known partial counts. Also record service
  resource observations if available, separately from elapsed time. Missing
  optional counters alone do not fail an otherwise evidenced arm.

Report the two wall elapsed values, the difference `sequential − concurrent`,
then ratio `sequential / concurrent` (positive elapsed only), **only if both
arms are admissible and complete**. Give the bounded secondary measurements
alongside, not as replacements for wall elapsed. Otherwise report each arm's
stage/outcome and available raw measurements, and mark the comparison not
admissible. No estimate of repeatability, statistical significance, population
speedup or superiority follows from this single pair.
