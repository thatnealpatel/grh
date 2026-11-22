# Experiments

Keep bounded experiments that serve the formalization project separate from the main [`cmd/godel`](../../cmd/godel) program. Pair each new standalone `cmd/<name>` entry point with a named, slugified directory here for its protocol and small, sanitized artifacts. Keep raw sessions, caches, and other bulky or private inputs outside the repository.

- [Launch revision provenance](launch-revision-provenance/): Work and improvement in `01a200ca-544f-7c3d-a9a8-dd171c32773e` used prompts older than the final accepted tree `756b8cd07027d5a4eb88c74abb657e9e8d00a912`. Record the archive revision in both prompts; leave proof routing and Gödel records unchanged.
- [Proof-breadth companion](companion/): Independent loop for neglected claims and missing generality; not run or automatically scheduled.
- [Two-writer proof pair](two-writer-proof-pair/): Failed before execution; neither arm ran.
- Historical handoff reading check (`cmd/handoff`, retired): The reviewer found no consequential error in the training reading. The pilot stopped with `no_transfer`; the held-out case was not run, and no instruction was installed.
