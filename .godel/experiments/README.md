# Experiments

Keep bounded experiments that serve the formalization project separate from the main [`cmd/godel`](../../cmd/godel) program. Pair each new standalone `cmd/<name>` entry point with a named, slugified directory here for its protocol and small, sanitized artifacts. Keep raw sessions, caches, and other bulky or private inputs outside the repository.

- [Two-writer proof pair](two-writer-proof-pair/): sequential versus concurrent work on two frozen local proof obligations (`cmd/proofpair`).
