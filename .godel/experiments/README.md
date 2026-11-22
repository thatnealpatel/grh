# Experiments

Keep bounded experiments that serve the formalization project separate from the main [`cmd/godel`](../../cmd/godel) program. Pair each new standalone `cmd/<name>` entry point with a named, slugified directory here for its protocol and small, sanitized artifacts. Keep raw sessions, caches, and other bulky or private inputs outside the repository.

- [Launch revision provenance](launch-revision-provenance/): Added archive revision markers at `7c90a726c211b8f720b65d725d6b95e6e3c5eb19` after a run whose prompts could not attest the exact launch commit. Live run `01a200d7-3533-7c9f-836b-21a3bc4aaba4` confirmed both markers; its stale proof candidate was also recovered without changing routing.
- [Proof-breadth companion](companion/): Separate loop for neglected claims and missing cases. Its class-character run `01a200d1-8d5d-7ebf-8a66-cd9e3fd53be7` produced a scoped strip lemma and an inverse-range handoff; not scheduled by `cmd/godel`.
- [Two-writer proof pair](two-writer-proof-pair/): Failed before execution; neither arm ran.
- Historical handoff reading check (`cmd/handoff`, retired): The reviewer found no consequential error in the training reading. The pilot stopped with `no_transfer`; the held-out case was not run, and no instruction was installed.
