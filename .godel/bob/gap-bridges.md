# Two second answers: Bridge the gap intervals

For ordered $3t$ shifts $(s,s+d)$, $d\ge0$, the $(10,2)$ shallow comparison at depth $39/20$ admits simultaneous zero second answers unless

$$-9/50<s<1/5,\qquad 1<d<141/100.$$

Here “unless” is a necessary condition for nonmatching, not the assertion of a failure inside. All first translates, orders two through ten at $t$, and the strict angular failure mean are retained. The joint witness can depend on $(s,d)$. The result makes no assertion about arithmetic realization.

The [checker](check-gap-bridges.py) prices constant mixtures of three certified prime profiles: The [mid-gap sector](midgap-sector-10-2.md), the [negative-slab fit](negative-slab-strip.md), and the hard-pair law from [two-term-10-2.md](two-term-10-2.md), in that order. The entries below are integer weights divided by their row sum. All endpoints are included. Each profile has its caps and strict mean independently replayed; hence so does each mixture, by linearity and convexity. Combine the **jumps** before computing the quadratic sum and difference kernels. Do not average the separate law slacks.

| Gap $d$ | Weights | Earlier shifts $s$ | Compact boxes |
|---|---:|---|---:|
| $[.663,.72]$ | $(1,4,5)$ | all | 71 |
| $[.72,.78]$ | $(1,2,7)$ | all | 81 |
| $[.94,1]$ | $(1,0,9)$ | all | 111 |
| $[1.41,1.5]$ | $(3,0,2)$ | all | 81 |
| $[1.5,1.85]$ | $(9,0,1)$ | all | 151 |
| $[1,1.41]$ | $(0,0,1)$ | $s\ge.2$ | 90 |

Use the [squared-imbalance chords](imbalance-chords.md) in each row, for **all** same-sign directions and both orientations. In the last row only the left edge of the compact shift interval changes. Replay with `sage .godel/bob/check-gap-bridges.py` from the repository root (SageMath 10.9, assertions on). Each normalized slack exceeds $10^{-5}$, including the analytic outer shift ranges.

For $s\le-.18$, $1\le d\le1.41$, the mid-gap sector certificate already handles the same directions. For all $s$, the remaining gaps outside $(1,1.41)$ are covered by the [negative-slab strip](negative-slab-strip.md) and its predecessors, the [imbalance strips](imbalance-chords.md), and the [large-gap result](two-gap-window.md). The single-shift law covers all opposite-sign scalar directions at all gaps. For each fixed pair in the combined region the compact convex hull of the corresponding answer images therefore contains zero, as proved in [imbalance-chords.md](imbalance-chords.md). Mixing complete witnesses attains the joint answer; no exchange of the quantifiers on pairs and witnesses is required.
