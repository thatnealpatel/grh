# Independent audit finding

Accepted parent `1088bcbba66b4ac4f9ea9824afe2c61aa6db6368`, reviewed commit `b8cabd6eb671c4db055ea68ff68acfed4fe16d1b`.

This handoff records defects, not a proof repair or a verdict on RH/GRH.

## Finding

The new premise check misses a proof-producing path. Work can correctly find no relevant note, then the independent auditor can publish one before improvement starts. Improvement can choose and land proof or source work using the newly disputed premise without violating its own prompt: It receives neither the new check nor a refreshed findings list. For a concrete input to this schedule, the b5a73da handoff published at c84b8fbd flags reliance on the generalized reflected-leg identification in .godel/obligations/isotypic-fourier-gluing-q-sqrt-minus-five.md:338–349, which is present at the pinned target. An improver extending that branch can miss the accepted warning even if the work node fully complied. This is a verified gap in prompt coverage, not an observed bad landing or a claim that the model can never discover the note independently.

## Evidence

The target is a direct child of the base. The entire parent diff adds one paragraph at cmd/godel/mission_nodes.go:31, and git diff --check passed. The paragraph tells the work node to look for new accepted audit findings by publication revision, check older findings relevant to a needed premise, and repair or avoid a premise that a finding still invalidates. It adds no automated check. No proof, Lean or Lake input, manuscript claim, or finding handoff changed.

I read the exact mission node definitions, their wiring in cmd/godel/main.go:46–51, the landing procedure in cmd/godel/README.md:26–46, the publication checks in cmd/audit/audit.go:121–177, and the node invocation and improvement input in patel.codes/godel v0.0.5. mission_nodes.go:21–35 appends the new paragraph only to work. The separate improvement role at lines 43–53 expressly contemplates landing proof or source work, but neither that role nor the shared practice at lines 57–83 contains the new check. Gödel run.go:70–102 invokes improvement after work and passes run context, not a refreshed list of findings. Its locks are per registered program, so the separate auditor is not serialized behind the mission's work and improvement cycle.

I read all six requested .godel/audit handoffs at their exact publication revisions: bdc7fec3eda49451961a66810d7c8c34ec7fe914.md at 8e376af0c2c77d2d4ad2643088d7506f7226475c; 54bc21bdee59a871dcd00a776c08037cb3906d66.md at 30b1ad710338302700ae02dbf82ce0806a13f19d; b5a73da9ef06f162482df5c594500fdc95f612ae.md at c84b8fbd08f48f796684f5d0570320b53a1b6e9c; 9f10e8ef6104bf715c07054bf7e3c4567f15f687.md at 7be14d9435fb9e4622cda1bddfabf8a41296723f; 140e39ba827eecb7f9e9b7026255fd2779974a8e.md at 5ed4f9a8111ce3a56ca7339db86fb0625283b677; and cae88c6045e9ebc4821f884d1770c08c0dd16e62.md at 53132cb9154238e8467341af68b51c1ee01145b9. All six publication revisions descend from the target, which has no .godel/audit entries. The b5a73da note is a concrete control for the publication rule: Its reviewed commit precedes the target, but its standalone publication follows it. The prior findings were read as context, not treated as work visible at the target, repaired, or re-adjudicated. No manuscript passage was assessed or visually verified, and no new load-bearing Lean claim was made.

From a scratch archive of the exact target including the pinned Lake files needed by Go test fixtures, offline go test -count=1 ./cmd/godel ./internal/accepted ./internal/godel ./internal/worker passed. An initial scratch run omitted the fixture files and failed in internal/worker for missing lakefile.toml; the corrected run passed. A separate scratch test called missionNodes and confirmed that the work prompt contains the audit instruction, the improvement prompt does not, and the improvement prompt explicitly contemplates proof or source landings. No live Yah, auditor, or proof landing was run.

## Proposed repair or follow-up

Put the premise check in the shared practice in cmd/godel/mission_nodes.go and apply it when either node chooses, recovers, or extends proof work, using the accepted revision it will actually build on. Leave program-only improvement outside the check. Add a prompt regression covering both roles, with a handoff example in which the reviewed commit predates the handoff revision but publication follows it.
