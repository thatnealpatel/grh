# Private tmpfs copy of a finished Lean audit cache

## Decision

Run `01a20347-5779-7a31-9811-d8a9af938417` used the documented
additive cache copy to audit `9e9393019a60e6b275281ca74bd9a11a8f03e0e9`.
The filesystem rejected an earlier reflink probe. At improvement
startup it had about 40 MiB free, too little for another 763 MiB
project build cache. There was space in `/dev/shm`. A private copy
there could keep the existing audit viable without writing to a
shared seed or changing the candidate's tracked inputs.

## Control

In improvement session `01a20350-96e4-7bfd-a9ef-8a2f45d5a914`, the
`tmpfs-control` task copied the checked `9e939301...` proof tree and
three pinned Lake inputs into scratch on the workspace filesystem.
It copied the finished project build cache of
`67716c9573f27e8decf4b39b120cb68d9636980e` to a private tmpfs directory
and symlinked the scratch tree's `.lake/build` to that copy. This is
the same additive pair used in the live work audit. The package
cache was the same trusted Mathlib installation.

The scratch `lake --wfail build Proofs` built the three added
modules in 8.85 seconds, and separate `leanchecker` runs replayed
both Gaussian modules. The new radial object was on tmpfs. The
project cache there grew from 762 to 772 MiB; available space on
the workspace filesystem moved from 29 to 22 MiB during the control.
The task removed both scratch directories on exit. This did not
run the exact-candidate command or transfer an audit verdict. The
live `9e939301...` audit used the ordinary disk copy, not tmpfs.

Document tmpfs as a manual destination for an otherwise valid cache
seed, with a separate capacity check and unchanged exact-candidate
requirements. Do not automate the choice or silently share writable
build directories.

## Live follow-through

In that same improvement session, exact audits of the scalar section
(`470bd0deacc5d88db570d7531cc7b5c04439fcbf`) and the compact Gaussian
support lattice (`00d93f83469610f817c3727f8e386b8f7ef278b5`) used separate
private tmpfs copies of the finished `9e939301...` cache, after checking
that the proof-input differences were additions with no seed artifacts.
Lake built those additions, the listed modules passed kernel replay and
endpoint checks, and both exact candidates were adopted. The root
filesystem had only 82 MiB free before the second audit. This confirms
that the manual fallback can complete the ordinary check, not that it
should become the default.

The first setup for the second audit attempted to recreate the existing
`.lake/packages` symlink and stopped before Lean. The successful setup
verified its target without trying to create it again.
