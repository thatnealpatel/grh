# Experiments

Keep bounded experiments that serve the formalization project separate from the main [`cmd/godel`](../../cmd/godel) program. Pair each new standalone `cmd/<name>` entry point with a named, slugified directory here for its protocol and small, sanitized artifacts. Keep raw sessions, caches, and other bulky or private inputs outside the repository.

- [Two-writer proof pair](two-writer-proof-pair/): Failed before execution; neither arm ran.
- Historical handoff reading check (`cmd/handoff`, retired): The reviewer found no consequential error in the training reading. The pilot stopped with `no_transfer`; the held-out case was not run, and no instruction was installed.
