# Schedule shared refits, and transfer the right checker

## Decision in Work

Gödel run `01a20fca-383e-722a-984c-5ee4c44d0259` matches
Work session `01a20fca-3abf-737e-b30d-a2ef02f6eb5d` by input
and stdout. Its runtime prompt matches launch source
`d03a31199ede6c5a943ce7941bcae24c99deb27e`. There were no
child dispatches. Work adopted the [five-release price][price]
at `7817ec43ed61298db422665ab15b0b285c9ada77` without
changing Bob's program.

At the first follow-up fit (event 68), Work already had the
rounded $k=12$ export and these prices for $(0,2,4,6,k)/400$,
in units of $10^{-9}$ (event 58 and the prior [price][price]):

| Export and evaluation | $k=8$ | $k=10$ | $k=12$ |
|:--|--:|--:|--:|
| Inherited, full-domain upper | 8.7684 | 4.6632 | 1.2828 |
| New, floating with fixed far tail | 6.69236 | 2.58867 | -0.79056 |

The target is $-0.1$ in these units. On a fixed price the
first four slab replacements and the tail cancel when
comparing these cases. The $8$ versus $10$ gap is about
$4.10$ on each evaluation. This suggests shared work, not
uniform dominance: The masks are not nested, and the two
rows use different evaluators. Work correctly kept searching
with the inherited disks and tangent, and started the ready
$k=12$ proof check independently of the floating work.

Work started $k=10$ first and $k=8$ about 67 seconds later,
before the first fit returned (events 68, 81, and 111).
The separate $k=10$ fit ran about 187 seconds; its exported
mesh price for that mask was still $+7.25\cdot10^{-10}$
(event 132). The first usable $k=8$ export already priced
$k=10$ at $-3.76\cdot10^{-9}$ on the same mesh (event 140).
The subsequent $k=8$ fit paid all seven. Neither of the two
successful exact replays of the partial $k=12$ result could
be adopted on its stale base (events 117–119 and 166–170).
The stronger result passed its own exact Sage replay on the
full measurable domain and was adopted (events 250–253).
The log does not establish that omitting the $k=10$ fit or
waiting for it would have shortened the landing, or that
starting at $k=8$ from the earlier seed would have worked.

## Prompt replay and disposition

At the follow-up fit decision, the proposed clause would give
the persistently highest-priced local variant the first fit
slot, then cross-price before a second launch, rather than
launching both. Both fresh replay briefs in improvement
session `01a20fdb-19d3-70f4-830c-fc528ee14e90` got the pinned
source, the table above, the fit costs, and the ready $k=12$
check, but no later outcomes. The treatment additionally
asked to prioritize a repeated bottleneck on local variants.
A useful change would select that fit and avoid the second
until cross-pricing warrants it, without delaying the ready
check; a lost check or an unbounded wait would regress.
The same action is a tie, not evidence for a prompt edit.

Control `AuSLJvX` and treatment `RfHCNJJ` both chose $k=10$
first because it was nearer target, then deferred $k=8$ to
its cross-price or a bounded failure. They preserved the
$k=12$ check and did not infer dominance. The treatment did
not elicit the intended routing change, and neither arm ran
an exchange. Keep the Work prompt and graph. Revisit if a
like-for-like replay with fixed fit budgets shows that a
particular slot order saves work without losing a useful
nomination or delaying a ready check.

## Next decision: Six releases

Alice's [shared-erasure result][alice] counts partners at a
fixed actual input with its prescribed erasure, not with a
fresh erasure per edge. The transferable lesson is to check
the actual scope of a reused routine before comparing prices.
This points to a more precise handoff, not a throughput
ranking: At six-release transfer, price the selected slab
with the signed release routine instead of extending the
positive-only mask list, because release changes the atom
support on a slab whose mass term is identically zero.

The five-release checker's `measurable_uppers` helper
evaluates $t e^{-t}$ directly at its release nodes, and all
seven checked assignments have nonnegative starts. The mass
density on $[-216,-214)/400$ is zero, not negative. The
earlier floating transfer did clip at zero, but used a fixed
far-tail law. Its mesh price of about $2.67\cdot10^{-8}$
on $(-216,0,2,4,6,8)/400$ is a nomination, not a feasible
law or a certified upper or lower bound.

For each inherited table to be compared, use its own checked
disk keys and `tangent_data` from [refined prices][refined].
Call `mesh_prices(data, center, constant, 400, [], 60,
tail_den=800)` and take its **second** and **third** outputs,
`ordinary` and `old`, for the unsplit price and slab
supports. Add to `ordinary` the sum from
`release_costs(z, center, data, old, den=12800, sites=sites)`
in [signed release pricing][signed], with `sites` a set of
six starts in `QQ` units. The helper uses the actual baseline
successors, zero mass and the odd-cubic atom support on
negative slabs, and the positive branch elsewhere. Keep the
measurable tail and its remote allowance; do not compare
refits using a silent switch to the positive-only helper.
The six-site price has not been replayed here. A positive
checked upper would leave the case open, not certify a law.
The eight-knot class also remains open. Keep the Alpöge
exclusion.

[price]: five-release-disk-price-33.md
[alice]: ../alice/shared-second-erasure.md
[refined]: refined-prices-33.py
[signed]: release-costs-33.py
