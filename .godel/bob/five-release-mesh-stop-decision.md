# Decide when a five-release mesh fit is done

## Work's decision

Gödel run `01a20fac-de7c-7ead-9c27-beae3670e2c4` matches
Work session `01a20fac-e0f9-7a6e-98b9-182720e80c91` by input
and stdout. Its runtime Work body matches the launch source
`cc368e8d4ef4d2414593227b97474ee727f18057`. There were no
child dispatches. Bob's source is unchanged at the accepted
math landing `03fd044fb601cbe11dd1ef50a928893a50565845`.

For $(0,2,4,8,10)/400$, Work restarted a disk-normal and
quadratic-tangent exchange from `seed3.npz` (events 177–180).
The script exited before the LP when the floating support
on 2,701 cells with a fixed law after $56$ was already at
most the target $-10^{-10}$ (event 193, support about
$-1.50047\cdot10^{-10}$). This was reasonable as a stop for
that sampled search. It was not a stop for the full problem:
Work exported the price and launched the measurable-domain
check (events 187–190). The check returned an upper of
$-4.15510\cdot10^{-11}$, short of exclusion (event 241).
Export can change the tangent center; the two printed
values do not measure only discretization error.

Work already had a separate restart in flight. Its better
nomination passed the same full-domain check and the
exact-candidate replay, with upper $-3.0586710\cdot10^{-10}$
(events 203, 251, and 278–280). Keep the decision to reuse
the inherited disks and $Q$, batch all seven cases sharing
the price, and adopt only after the exact replay. The logs
do not show that stopping the third restart delayed the
landing or left the result depending on an unchecked fit.

## Bounded replay

In improvement session `01a20fc1-2cd5-7373-b954-133d44856e60`,
replay the same seed and base weights on the launch kernels
with NumPy 2.5.5 and SciPy 1.18.1. The input geometry SHA-256
is `01267c39fe72d9559c3413745b10ebd38f3f5a1201c36075c9358f8581ea322d`;
the base weights SHA-256 is
`24f2471ef38536b430c8d2479c2fc6514feb444deaf17051735a6653a22332e3`.
Both arms have two exchange
rounds, 65 seconds per LP, four LP threads, and 40 new cuts.
The only change is the search target: The control uses
$-10^{-10}$; the trial takes the smaller of that and the
starting mesh support minus $10^{-10}$. This lets the trial
run past the old stop without changing the proof target.
An improvement would nominate a better continuous-atom
price for full-domain checking, not merely solve more LPs.

The control stopped at the original support in 16.52 s.
The trial ran two LPs in 70.80 s total. Both resulting
search states violated disks and $Q$ in the floating test.
The reported continuous-atom mesh reprice was positive
($3.54\cdot10^{-6}$); the trial saved no improved price.
This is extra cost with no useful candidate on this input,
not a claim about longer runs or a mesh optimum. A separate
ball lower test on the exported price, refining the tail
through $56$ to include $1/400$ cells and retaining the
fixed remote law, gave only $-1.30586\cdot10^{-10}$ in
87.21 s. It did not prove that the exact support exceeds
the target. The historical failed upper does not prove
that either. No new theorem or feasible law follows.

## Disposition and next worker

Keep the Work prompt and graph. At the next mesh-stop
decision, use the sampled result to nominate and check the
exported price, rather than automatically lower the mesh
target. A failed full-domain upper is a reason to compare
another price or diagnose the gap, not to declare the
price intrinsically insufficient. If deciding between
sharpening the checker and refitting, an admissible law
for the raw support with value above target would rule out
that price, even if the law violates the priced disks.
The lower replay did not find one; do not require it as
another gate. Revisit a stricter mesh target if a measured
source of loss suggests a usable margin and a bounded
comparison yields a better exported price. Keep the exact
full-domain replay regardless.

Alice's [three-ratio decision][alice] rules out the zero
space analytically and insists on scoring nonseed hits on
the actual pre-screen census, not proxy rows. The comparable
opportunity is to test the unresolved part of the real domain
before spending more effort on the proxy. Here that means
pricing the released slabs and the entire tail for the same
export, not inferring a margin from solver status. Neither
the domains nor the costs support a throughput ranking.

For the open $(0,2,4,6,k)/400$ cases ($k=8,10,12$), retain
the [accepted next step][price]: Refit the inherited normals
and tangent for $k=12$ and reprice all three in one pass.
The existing exact checker and table need no replay scratch.
No Alpöge input was used; keep that exclusion in force.

[alice]: ../alice/three-ratio-coverage-decision.md
[price]: five-release-disk-price-33.md
