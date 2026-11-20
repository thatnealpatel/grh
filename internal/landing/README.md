# Landing through Yah

Set `GRH_CAMPAIGN_ADAPTER` to the **absolute path of a trusted executable**
provided by the campaign operator. The executable and its configuration must
not come from the proof worker or a candidate checkout. Landing and anchored
reads also need `jj` on `PATH` with the `file list` and `diff` tree templates
(`-T`). No default adapter is installed. Without one, or without a successful
exact-revision worker check at both stages, `Land` cannot report success.

Yah's headless CLI takes an agent prompt, not a tool request. `tool_campaign`
is an in-process harness tool and `patel.codes/yah/internal/campaign` is not a
public Go API. In particular, `tool_campaign(new)` followed by implicit
`integrate` finalizes and replays in one call, which is too late to check the
finalized output before requesting integration. The following is a **grh
adapter contract**, not a Yah CLI or RPC protocol. An implementation must
have access to authorized Yah campaign facilities; it must not substitute an
LLM, direct bookmark/branch movement, or its own accepted target.

## Process protocol

The program invokes the same executable with no arguments, in the canonical
repository root, once per operation. Each request is a single JSON object on
stdin (terminated by EOF), with `op`, `root` (absolute repository root) and
the fields below. Return one JSON object on stdout and exit zero on a normal
result. For tool errors, unavailability or permission failures, use stderr
and a nonzero exit; don't turn partial tool results into success. In
particular, an interrupted call, invalid JSON, or a failed `adopt` command may
leave a remote side effect. The gate does not repeat it. Diagnostics must
not include credentials.

| `op` | Additional request fields | Required successful response and mapping |
| --- | --- | --- |
| `status` | None | `tool_campaign({op:"status"})` result: `available`, full `accepted`, and `unavailable` when applicable. This is the authority for the current accepted target. Do not substitute the initial seed, attempt flags, or a local checkout. |
| `prepare` | `on`: exact accepted base from status | Allocate an exclusive, clean, managed campaign assignment at `on` (Yah `Kernel.AssignWithMetadata` semantics). Return `path`, `base`, `checkpoint`: canonical absolute workspace path, exact base, and exact empty child commit of base. Do not write the proof files. |
| `finalize` | `workspace`: the complete `{path,base,checkpoint}` returned by prepare | Bind this request to the same assignment. Take a fresh `Kernel.Checkpoint` of the files grh wrote, set it on the workspace, then register it with `Kernel.Finalize`; return the registered output `{commit,workspace,base,conflicted}`, with `workspace` the absolute path string. Do not integrate or adopt. |
| `integrate` | `on`: original accepted base; `outputs`: one registered commit; `description`: commit message | Call `tool_campaign` with these fields and return its attempt JSON. The gate requires a clean `pending` result with the same `base`, exact `inputs`, and full `candidate`, not a no-op or pending-attempt replacement. |
| `adopt` | `candidate`: exact checked integration commit | Call `tool_campaign({op:"adopt",candidate:...})` and return its `{accepted,stale}` result, with an explicit boolean `stale`. Do not modify any other revision or publish on the gate's behalf. |

Every operation must use the **same authorized campaign attachment and
adoption target** and the same authoritative attempt/output registry. Separate
processes must coordinate access with the harness; they must not each keep a
private state copy or allow concurrent state writes to lose existing entries.
Hold the prepared workspace exclusively until finalization; it must be an
isolated workspace outside the control checkout, attached to the same store.
Commits referred to by the results must be readable by full ID from the
control repository. The integrated candidate must remain bound to its
campaign workspace as required by Yah's adoption check. A canceled caller
cannot assume an adapter operation or remote change was rolled back. On a
Gerrit-backed campaign the Yah implementation may only observe convergence to
an already accepted remote candidate; the adapter must not implement a second
publication path to force it to pass.

## Gate guarantees

`Land` adds proof files only. `LandReplacing` also permits modifications with
caller-supplied exact accepted preimages; unrelated accepted files and tracked
Lean/Lake pins must stay unchanged. `grh` writes the files itself, inspects
only immutable Jujutsu revisions, and verifies the output and candidate are
each one commit on the original base with exactly the authorized changes and
bytes. The worker callback receives the repository root, the full revision ID
and declaration names. It must check that exact revision in isolation, using
its pinned setup; checking the control working copy is not sufficient.

Before requesting adoption, the gate rechecks the accepted base and optionally
calls a durable intent hook with the exact integrated revision. Yah owns the
actual concurrency semantics of adoption; the status check does not lock the
accepted target. A non-stale acknowledgment must name the candidate or its
descendant, and a fresh authoritative status must independently confirm that
same candidate is still in accepted ancestry with all requested files
retained. `ReadLanded` verifies this ancestry and checks exact bytes and
non-executable regular file type at both the anchor and the observed accepted
head. A failed or ambiguous adoption is not a safe retry. Callers that recorded
an intent can reconcile it with `ReadLanded` later, without asking for adoption
again.
