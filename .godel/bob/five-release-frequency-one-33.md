# Delete-33: The frequency-one cap leaves a common raw price

At $c=39/20$ on the release set $(0,2,4,6,16)/400$, one law
has all nine accepted [raw tangent prices](eight-piece-deletion-33.md)
strictly above $3.5\cdot10^{-11}$. It obeys both DC caps and the
$A$ cap at frequency one, all with modulus less than $0.91$.
The smallest price is the `eight-knots` price, about
$3.58386138\cdot10^{-11}$. The moduli are approximately
$0.900000000011$, $0.900000000031$, and $0.906519343103$.
Thus a convex recombination of the nine prices, even with
nonnegative penalties for these three cap slacks, cannot
exclude this release set. This says nothing about full
quadratic prices or new tangents.

The [serialized law](deletion-laws/delete-33-five-release-frequency-one.json.gz)
uses four atoms per cell, with weights and $u$ sites given
as integers in units of $10^{-12}$. The checker reconstructs
the original finite boundaries, adds $1/3200$ subdivisions
in the five named slabs, and uses the earlier common-witness
tail mesh through $48$. Beyond $48$ use $u=1/\sqrt{2}$, so
$A=B=0$; left of $-144/25$ use $X=0$. The law's prices and
fields are evaluated by Sage balls, not by the nomination LP.
A trial regenerating atoms from rounded LP multipliers did
not reproduce the cap values. The fixed atoms, not the
multipliers, are the evidence.

```sh
/opt/sage-10.9/bin/python .godel/bob/check-five-release-frequency-one-33.py --jobs 5
```

**Follow-up.** A [five-disk witness and curvature check](five-release-curvature-33.md)
now carry out the test below on this same release set.

**Experiment posed at the handoff.** The law fails both continuous caps:
$|V_A(611/10)|>3.88$ and $|V_B(2/5)|>2.3$, verified at
those exact points. They were nominated by a grid search,
not proved to be maxima. On this release set keep the three
existing caps and refit with these two additional unit disks,
leaving the negative constant laws free. The reset probe's
$B$ frequency $223/50$ is not a direct substitute: On the
unreset frequency-one law its modulus is about $0.2104$.
If the finite refit survives, check a serialized witness and
price the full second quadratic remainder separately before
exchanging whole frequency lists. If it nominates a separator,
check an upper price below $-10^{-10}$ for arbitrary laws on
the released slabs and the measurable tail, not merely for
this fit mesh. The other six frequency-one probes are still
floating-point only. Neither full frontier is closed, and this
law is not a surplus witness. Keep the Alpöge exclusion.

## Handoff decision

**Evidence at the decision.** Gödel Work
`01a20e8a-452c-71fa-8d3d-168e4d98dec6` used `cmd/bob` at
`58e1e3576b055`; `432066cde80a` is the later accepted result,
not the launch source. In Yah `01a20e8a-47b6-7fe4-ab21-825f503848c9`,
events 1254–1255 screened all seven release sets with both
DC caps and eight projections of $V_A(1)$ at radius $0.90$.
The projected disk bound was $0.90/\cos(\pi/8)<1$. All seven
printed raw margins were positive; the tightest was about
$3.584\cdot10^{-11}$. Neither that floating result nor the
corrected negative-slab reset at events 1280–1281 was a
certified law. Work correctly reported the scope of its
adopted DC profiles and reserved a separate curvature check,
but event 1282 handed off frequency one without the earlier
probe. The record does not establish why. The only original
child (`primal-eight`, `vHUEPwT`) worked on a different fixed
mesh and had no finished result when cancelled at event 129;
the parent's checked fixed-mesh upper bound made its primal
search unnecessary. No missing child verdict explains this
handoff omission.

**Intervention and replay.** At the final handoff, a prompt
reminder should carry forward a completed point-cap probe
instead of reassigning its floating screen, because its
positive margin already distinguishes a refit from merely
rejecting the old profile. Both readers saw the same pinned
revision and event window 1235–1281, without the live handoff.
`handoff-k` had the launch prompt; `handoff-m` also had a
sentence asking it to reconcile proposed work with completed
probes and their evidence levels. Better meant a justified
narrower next test that the control missed; promoting a
floating result to a certificate was a regression. **Tie:**
Both recovered frequency one, kept it as a constraint, and
nominated the reset probe's two additional frequencies for a
joint test. Neither had checked the frequency-one law. The
focused window restores proximity that the long live run
lacked, so this does not test live retention. Keep `cmd/bob`
unchanged; reopen if a realistic long-context comparison
shows a change without losing scope or evidence distinctions.

**Peer comparison.** Alice's accepted
[through-point component result](../alice/through-point-components.md)
at `e21456677229` repriced previously identified classes at
the actual new filter width and narrowed the remaining cubic
experiment. Alice's [handoff replay](../alice/through-point-handoff-decision.md)
also tied. The comparable decision here is whether to send
a narrower experiment on the strength of a prior probe. To
justify that decision more fully, we freeze and check the
point-cap law and measure candidate cuts on that same law,
not only on a different reset law. This is stronger evidence
for the handoff, not a throughput ranking or a live program
improvement.
