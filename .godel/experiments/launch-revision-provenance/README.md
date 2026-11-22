# Distinguish the launch revision from the proof tree

## Observed decision

Gödel run `01a200ca-544f-7c3d-a9a8-dd171c32773e` inherited a suggestion
whose theorem had already landed during the previous improvement.
The matching Yah work session `01a200ca-54f9-7555-a17d-d9120ad7f6ef`
started with `fb69586e959e4f31f38afdb73b7598a547a38219` as its campaign
base and moved to the unmet specialization. Its work prompt matches
that revision's `cmd/godel` prompt exactly. So does the improvement
prompt in `01a200d0-dd62-702c-8e60-c2e380ff8aaa`, even though that
session started from `756b8cd07027d5a4eb88c74abb657e9e8d00a912`.
The later tree contains the manuscript lookup instructions introduced
in `1f77a1d9d0de0bee313a3e653ceb8d2b9f33f43a`. Reading the final
accepted tree alone would misattribute those instructions to the run.
The old sessions identify the prompt bytes, but do not attest the full
commit ID archived by the bootstrap.

The same prompt comparison matches the preceding run
`01a200b7-0d73-7e20-b798-51d26a977150`: Work
`01a200b7-0e16-7dd4-a8ab-32d787ae8d07` and improvement
`01a200c1-19b3-787f-899e-9af93b9f2bce`. The latter explicitly noted
that the exact launch revision was unavailable. Inspect the raw prompt
without replaying a session with
`jq -r 'select(.type=="runtime_baseline") | .inference.system_prompt' main.jsonl`.
Compare its suffix to the role-specific append reconstructed from
`mission.md` and `mission_nodes.go` at the candidate historical revision.

## Control and decision

Keep route selection unchanged: The latest work skipped a closed
obligation, recovered two Lean draft failures, and independently
reviewed the character specialization (`ZJmYXhV`). Candidate
`ac9c539ca1d87a86395a933a49349ecd33531757` passed its audit but was
not adopted: The concurrent Chapter 6 handoff moved the base to
`d0593e1fb60831228faae73cff33c67a204df106`. The restack preserved the
Lean inputs, reused the build cache, passed the full audit again, and
landed at `756b8cd07027d5a4eb88c74abb657e9e8d00a912`. This is a case
where the existing recovery procedure worked, not a reason to add an
integration scheduler or weaken the audit.

The narrow change is to embed the exact archive commit in both Yah
system prompts, without changing the task message, work handoff,
run record, or bootstrap. The bounded control is to build the exact
integration candidate from `git archive` as the bootstrap does, check
that the marker equals the candidate ID and is embedded in the binary,
and test that both prompt builders expose a valid marker but omit the
unexpanded checkout placeholder. This tests provenance, not proof
quality or a changed routing decision.

The exact candidate `7c90a726c211b8f720b65d725d6b95e6e3c5eb19`
passed the archive expansion and binary checks, and `GOWORK=off go test
./...` passed in the extracted archive. The candidate was adopted.
See the `launch-revision-control` task in Yah session
`01a200d0-dd62-702c-8e60-c2e380ff8aaa`. No fresh live Gödel run was
performed, so there is no observation yet of the marker in a live
session baseline.
