# Reuse a finished build on an additive Lean restack

## Observed decision

Gödel work run `01a20315-7772-7a69-8642-314f9d8592dd` (Yah
`01a20315-7831-7273-a051-683329eec269`, launch
`b6ce6ff51118689d7ea4b1925774cb1539133c4a`) audited
`1f1666820166c7bf5f6d6635ceb779ef75a9f17f`. Adoption returned stale,
so work restacked the same proof at
`e06c182eb8bb81ef3024246a7147ce263def93d8`. The entire delta in
`Proofs/` and the pinned Lake inputs was one module addition,
`Proofs/Theorems/IdealClassSplitPrimeFactor.lean`. Under the existing
identical-input rule, work ran the new audit from an empty project
build directory. The task took about 145 seconds and passed, but
adoption again returned stale after a Companion-only Go change.
The third audit used the identical-input reuse rule, took about 18
seconds, and landed at `e83eadb295066d9e9a3555046e0c8dfe49631310`.

The previous run `01a202f7-5d01-7c13-9fc9-912200cda5a3`, improvement
Yah `01a20302-ad3d-7d7c-bccb-90cd7c861684`, faced the same choice:
`bd37ccf79f0d185d9f5f353420f2e83b60318d4f` to
`63b95764632d95b7ad772b43bc1135cf5ce65f38` added just
`Proofs/Theorems/IdealClassSignCharacter.lean` to those inputs. It
also reran the audit from an empty project build and adopted after
passing. Neither case indicates a proof-routing problem.

## Replay and decision

In improvement session `01a20321-beae-7d49-8fe9-5c1015370cb1`,
compare the first case's two exact revisions with `jj diff --summary`
on `Proofs/`, `lakefile.toml`, `lake-manifest.json`, and `lean-toolchain`.
Copy the later candidate's proof sources and pinned files into
scratch, link to the same trusted Lake packages, and seed `.lake/build`
from the first candidate's finished audit. Check that the added module
has no `.olean` in the seed, then run `lake --wfail build Proofs`. The
copy took about 1 second and the strict build took about 4 seconds.
Lake built the added module; it did not re-elaborate the unchanged
proof modules. The seed came from the same pinned toolchain and
package tree, not an untrusted or failed build. In a second scratch
run, warm copy and strict build took 11 seconds together. Joint
import, separate kernel replays of the three proof modules and the
added module, matching the four log-Haar signatures against the
historical audit, and five axiom checks then passed in 43 seconds
including the build. This did not run the integration workspace's
archive comparison or adopt a candidate.

This is a historical replay, not a live race or an adoption. It
supports reusing the trusted project cache on strictly additive Lean
restacks while retaining all checks on the exact new candidate. Do
not extend the procedure to edits, deletions, renames, Lake input
changes, or a seed already containing artifacts for the added
modules. Do not install an automatic restacker on this evidence.
