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
`01a200d0-dd62-702c-8e60-c2e380ff8aaa`. That control did not launch
Gödel.

## Live follow-up

Run `01a200d7-3533-7c9f-836b-21a3bc4aaba4` is the first observed live
confirmation. The work baseline (`01a200d7-35e1-7637-a950-298bbf2f3b00`)
and the improvement baseline (`01a200df-d170-72c4-b615-4f74015dc623`)
both record `54d6c5b85297d0eda931e2ed551077449db713c3`. The recorded
append suffixes match `cmd/godel` at that launch revision, and the
session messages match the run record. Improvement started from
`6898a153192f7ca5adbbc77aa7a42700f49500d2`, not the archive revision.

Work used the accepted finite Euler product to prove the two separate
finite Mellin evaluations. Initial local elaboration failed on
inversion and smoothness lemmas, then on normalization at the finite
endpoint. Those failures were repaired without changing the reviewed
scope (`yfLWwpY`). Candidate
`7f809903a54929eeb5a6fe8ab1a233154ca6494d` passed the exact audit but
was stale on adoption because the companion's program-only revision
`b36fe6b7dbe21a8a3a9635138fe30de540b81c4c` had landed (companion run
`01a200d1-8d5d-7ebf-8a66-cd9e3fd53be7`, improvement session
`01a200db-9ddc-7cca-95ec-aba68d12ccbf`). The restack had identical
Lean inputs. Work reused the audited cache, reran the full audit and
type checks, and adopted `6898a153192f7ca5adbbc77aa7a42700f49500d2`
39 seconds after the stale result. As in the previous iteration, the
stale attempt increased checking time but did not block adoption.
Keep the current recovery and routing; no scheduler trial was run.
