# Put the base refresh at the allocation decision

Gödel run `01a204b4-da2e-7a81-995b-ae6a9f6876f8` matches the input
and stdout of Yah work session `01a204b4-db94-7e4a-8703-c35a370da3c0`
(events 3 and 79). Its baseline names launch archive
`56a97650d2239fe3b5aaff0a1a0dee08975e82e0`, also the initial accepted
revision. That archive's README already specifies a just-in-time status
refresh. The session read it, then used the startup hash in `new` 83 s
after reading status, without refreshing (events 4–5, 13–14, 28–31).
A docs-only landing moved the tip to
`679302695f48d985efd9175842a391487dd32893`; allocation was rejected.
No output or integration candidate was created. After stopping repository
edits the work node used the prior additive Haar candidate's artifacts
for a scratch proof. Three scratch attempts exposed Lean proof errors;
a fourth invoked the Lake-only `--wfail` flag on bare Lean. The final check
with `-DwarningAsError=true` passed with the seven reported axiom sets.
There was no work subagent or independent statement review in that run.

This is the same stale-base selection mechanism as in the
[earlier workspace-base refresh trial](../workspace-base-refresh/),
not the stale-*adoption* problem in the immediately preceding
[additive Haar run](../restack-lake-cache/). In the failed trace,
selecting the last known accepted hash before allocation instead of the
startup hash would change the request. That does not prove the allocation
would have succeeded. In the fresh improvement session
`01a204b9-9c06-7958-9ac8-47b71f2e2360`, the refresh and allocation
were 3.4 s apart (events 18–21) and succeeded on
`fefd46d3c1f02328611717a5870ceda53daf1b23`. Another landing before
integration did not block the description-only direct replay.

Decision: Put one short cue in the shared node prompt at the campaign
workflow instruction: Initial status is for reading; refresh just before
allocating a direct edit after investigation. Preserve overlap inspection
and the existing stop-on-setup-failure rule. Do not add polling, retries,
or a separate scheduling node. The successful control tested the action,
not whether a future Yah worker follows the new cue under contention.
