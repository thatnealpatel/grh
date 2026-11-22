# Import the project together before the scoped proof audit

## Trigger and decision

Gödel work run `01a20275-aefa-720f-99b0-f8f425d92cd1` (Yah work
session `01a20275-afc8-7bdd-b643-280835b8b1ff`) adopted the general
idele norm section at `8fa08a83fc7120f12fba0263b06ee73f44c4a812`
after the 9,054-job `Proofs` build, two separate kernel replays, and
seven endpoint checks. The general and rational section modules both
exported `Masullo.ideleNorm_logSection` with distinct statements. The
scoped audit did not import both, so it passed. The improvement review
caught the collision when it tried to use both modules.

Decision tested: Should a local audit reject such a candidate before
its scoped kernel and endpoint checks, instead of letting the collision
surface in downstream Lean work? The control contrasts the same
project on the broken revision and the repaired proof, not two prompts.

## Bounded trials

In improvement session `01a2027a-7a02-74cb-918f-2b3bfb3310df`, task
`replay-all-imports-exact` performed this control in the two integration
workspaces after their local builds:

```sh
set -o pipefail
find Proofs -type f -name '*.lean' | LC_ALL=C sort |
  sed -e 's|^Proofs/|import |' -e 's|\.lean$||' -e 's|/|.|g' |
  /usr/bin/time -v lake env lean --stdin
```

- `8fa08a83fc7120f12fba0263b06ee73f44c4a812`, 303 imports: Exit 1.
  Lean reports that `Theorems.IdeleLogSection` conflicts with the
  declaration from `Theorems.RationalIdeleLogSection`. 1.97 seconds,
  about 3.3 GiB peak RSS.
- `27f135ecb850d7d2fe8c1a16e530170120eee76f`, 305 imports: Exit 0.
  2.98 seconds, about 4.0 GiB peak RSS. The repaired Lean tree was
  subsequently adopted at `57861b4dffce4629279593eb19764965b5ccdb5b`
  after an exact-candidate audit. The intervening changes did not
  modify Lean or Lake inputs.

Task `coimport-live-regression` then exercised the edited Go command in
those same conditions, with just one selected module at a time. On
`8fa08a83f`, the project still builds, but the new command rejects it
at the joint import before the scoped replay. On `57861b4d`, the
command passes and still reports the built signature and permitted
axioms of `Masullo.ideleClassLogSplit_mk`. The Go fixture also checks
that an unselected project module appears in the joint import and that
failure leaves no audit receipt. `go test ./...` passed.

## Disposition

Install a separate, import-only Lean invocation after the warning-as-error
build. Retain the individual kernel replays and scoped signature, axiom,
and provenance audit. This checks that future steps can combine project
modules, not that every declaration in the aggregate environment is a
reviewed theorem. The measured cost is one short, sequential Lean process
with a substantial memory peak, not a second proof build. No launcher,
router, proof statement, or remote worker is changed by this experiment.
