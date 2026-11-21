# Two-writer proof pair — summary template (not run)

Use one copy per prespecified pair. Replace placeholders only with adjudicated
values; use `unavailable — reason` rather than leaving silent gaps. Keep raw
journals, proof files, logs, VM/network identities, credentials and full
session data out of this directory. Use redacted evidence references that an
authorized operator can resolve in the separately sealed manifests.

## Shared inputs and order

- Protocol and operator build source/digest: …
- Frozen source `69355b3ae0441fa395a1110d88d0df06b01dcbc1`, tree
  `09b74ef69354212b6741c669578efa55388e957a`, synthetic root
  `4c0ccd361d70957dc93ec9be3cc109fb3362458a` (admission evidence: …)
- Before-launch order draw, order, and manifest references: …
- Yah, audit binary, Lean/mathlib, package/build cache and PDF identity and
  provenance (including any differences): …
- Hardware/service budget, selector configuration, runtime allowlist and
  cleanup/cutoff procedure confirmed before launch: …

## Outcomes

Use PASS / FAIL / UNKNOWN for gates. In each row provide the redacted evidence
reference or explain why the evidence is unavailable.

| | Sequential (A then B) | Concurrent (A + B) |
|---|---|---|
| Attempted? First/second? | … | … |
| Admission and equality gate | … | … |
| Last observed stage, exit or cutoff | … | … |
| Writer A (base, actual model/effort, terminal, output ID, scope) | … | … |
| Writer B (base, actual model/effort, terminal, output ID, scope) | … | … |
| Dispatch and order gate (including waits or overlap evidence) | … | … |
| Candidate ID, integration/byte-union check | … | … |
| Reviewer actual model/effort/base, terminal and no-edit check | … | … |
| Statement verdict A / B, type evidence refs | … | … |
| Audit binary digest, audited revision, module/declaration IDs, exit, log digest/ref | … | … |
| Adoption (candidate/accepted ID and stale status) | … | … |
| Identity and quality gate | … | … |
| Completion and containment gate (coordinator, cgroup, VM/revocation receipts) | … | … |
| Coordinator wall elapsed, s (not time to success unless all gates pass) | … | … |
| Writer session sum bounds, s | … | … |
| Observed writer active sum bounds, s | … | … |
| Writer assistant span overlap bounds, s | … | … |
| Usage by role (input/output/cache/reasoning; source and coverage) | … | … |
| Other resource measurements (scope and units) | … | … |
| Deviations and missing evidence | … | … |
| Admissible and complete? | … | … |

## Paired comparison

- If both arms pass: wall elapsed difference `sequential − concurrent` in
  seconds; wall elapsed ratio `sequential / concurrent`; secondary bounds above.
- Otherwise: **not admissible**. State which gates failed or were unknown;
  do not compute a timing difference or ratio from an incomplete arm.
- Scope: one pair, conditional on these briefs, inputs and observed treatment;
  no general speed or proof-quality conclusion.
