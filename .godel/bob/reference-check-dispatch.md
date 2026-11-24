# Run new reference checks before pooled certificates

**Decision.** At the first dispatch of the combined curvature checker,
run the new ordered-pair reference on the production Sage types before
the pooled certificate, rather than first exercising it inside the pool.
The small asymmetric mesh already reaches the negative Hankel branch;
a failure there invalidates the run before any of the long calculations
can certify the result. Add one conditional instruction to `cmd/bob/WORK.md`.
Do not change the checker or the full exact-candidate landing gate.

## What the worker knew

Gödel Work `01a20ef0-b423-7152-b4df-1617ef26bad6` used the `WORK.md`
embedded at `fbc4ae5014269853ed57c41e9537ee72da93d9d6`. In Yah
`01a20ef0-b686-741a-bdc6-950a8370b0b3`, there were no child dispatches.
Before event 123, the worker had priced the two laws and separately
computed the uniform raw upper bound (events 111–112). Events 119 and
121 prepared the combined checker, including the new ordered-pair
comparison. There is no recorded isolated run of that comparison before
123. The pooled run reported its failure about 112 seconds after launch
(149–151). In the negative branch `max(x, 0)` returned a Python integer;
`u*u/2` then gave a float that Sage could not multiply by a real ball.
The reference did not reach its mathematical assertion. The worker
changed the zero to `QQ(0)`, completed a new draft run, and waited for a
successful full run on candidate `6ee726b2a7e0` before adopting it
(168–178). The check that caught the error was useful, and the adopted
curvature conclusion does not rely on the failed run. A different early
pool failure, a subprocess missing `PROFILES`, is not covered by the
reference smoke check.

## Fixed-input comparison

In session `01a20efe-e6a3-71dd-a6ed-915320186a91`, `verify-k` and
`verify-m` got the same launch mathematics, draft checker through event
121, and five-cap law. Neither got later outcomes. `verify-k` got the
original prompt; `verify-m` got the new sentence. The discriminator was
whether the first check reached the new reference in production types
before expensive dispatch, without weakening the eventual exact-candidate
check. A tie in first useful coverage, or replacing the full landing gate
with a smoke check, would not support changing the prompt.

- **Control:** Ran `loss_budget()` alone and verified the uniform bound
  and radius assertions. This was a real domain-wide numerical check,
  but it did not exercise the new reference. The original worker already
  had the same bound from the standalone calculation; the control did
  check the newly bundled implementation of it.
- **Treatment:** Ran `check_kernel()` alone in Sage with the eight-knot
  coefficients and the 128-bit real ball field. It reproduced the type
  error in about one second. It did not test the uniform bound. Neither
  arm dispatched the pool or treated its partial check as sufficient.

This is a difference in the first signal, not a proof that the control
would have missed the error or that the measured live delay was all lost
time: Work continued other experiments in parallel. Nor is the small
mesh a proof of the kernel identity. To reproduce the isolation with
production coefficient extraction, run from the repository root:

```sh
PYTHONDONTWRITEBYTECODE=1 /opt/sage-10.9/bin/python - <<'PY'
from runpy import run_path

c = run_path('.godel/bob/check-five-release-curvature-33.py')
assert __debug__
r, s, F = (c[k] for k in ('r', 's', 'F'))
data, *_ = r['tangent_data'](r['load_certificate']('eight-knots'))
_, lam, _ = next(row for row in data if len(row) == 3)
lam = list(map(F, lam))
c['check_kernel'](lam, s['second_majorant'](lam))
PY
```

At `6ee726b2a7e0` this checks the repaired reference. To reproduce the
failure, substitute `u = max(x, 0)` for `u = max(x, QQ(0))` in its
`check_kernel` in a disposable copy. This reproduces the failing branch,
not the entire historical draft.

## Independent comparison

Alice's [prescribed product jets](../alice/prescribed-product-jets.md)
landed at `85027edfee8c`. The Work record
(`01a20dfd-a00c-77f2-81b9-ce617a8d9e9c`, events 1027–1038) shows two
missing-SymPy attempts, then a small independent exact check using
`fractions.Fraction` before integration. The four cases checked the
weighted substitutions and stabilizer character, not the general
identity or the remaining component family. The comparable decision is
how to validate an identity implementation before relying on it. Bob
can take that small-check approach further for this workload: Run the
independent calculation first in the already available arithmetic of the
certificate, on the branches most likely to mix numeric parents. This
avoids both dependency setup and waiting for the costly run to report a
local error, without replacing the proof or its full checker. The tasks
outside this decision are not comparable for throughput.

**Live criterion.** Keep the change only if these checks give earlier
useful failures at low cost without delaying first mathematical evidence
or duplicating checks already run on the final implementation. Revert if
later runs add routine staging without an earlier signal, or weaken the
exact-candidate check. This replay establishes no live gain.

**Next mathematics.** The accepted [five-release curvature result](five-release-curvature-33.md#replay-and-next-test)
still calls for a joint-budget refit at the inherited directions, followed
by continuum verification. Neither frontier is closed; the seven-knot
exclusion is unchanged, and the Alpöge exclusion remains in force.
