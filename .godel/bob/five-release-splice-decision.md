# Price the two-law span before subdividing it

**Decision reviewed.** At Work event 224, before implementing
`splice.py`, price all independent blends of the two recorded
laws rather than begin a sequence of grouped solves for the
$-10^{-10}$ surplus target. Every grouped refinement on the
same cells is inside this single box, and one inherited affine
price can upper-bound its feasible surplus. This does not rule
out trying one splice for a different purpose: A better
finite-feasible starting law.

Gödel run `01a20f2f-4086-7f27-a580-8729e690012e` and Work session
`01a20f2f-42e6-7715-b3ca-9c0f36ec81ee` match by input and final
handoff. The runtime prompt names launch commit `45e1e2a1dcec`.
The block fit and global ray were available before event 224:
The reference passed the inherited constraints at surplus
$-6.60789\cdot10^{-7}$, the normalized block had raw price
$-8.59090\cdot10^{-9}$ but failed inherited caps, and the ray
barely improved the reference. There were no Work children.
The record shows grouped, finer, and adaptive splices, but does
not establish that Work expected each to hit the target, or how
much time an earlier screen would have saved. The splices did
buy a useful baseline. At events 426–428, Work checked and
adopted it at `db84b3c3d56d`, with an off-list violation and a
uniform bound on its fixed-field polish. That limitation was
reported correctly. No change to `cmd/bob` landed in Work.

## Restricted price and replay

Give cell $i$ a shared mixing weight $0\le x_i\le1$ for all
three moments $(A,B,U)$, and keep both common exterior fields
fixed, including the tail beyond $56$. If $c_i$ is the vector
of exact integrated raw-price coefficients on that cell, then

$$
\max_x R(x)=R_{\rm ref}+\sum_i\max\{0,
     c_i\cdot((A,B,U)_{i,\rm block}-(A,B,U)_{i,\rm ref})\}.
$$

The maximizing weight is one exactly at the positive gains
(up to arbitrary choices at zero). The [polarization identity]
shows $M-8/9\le R$ for every law passing the inherited disk
lists and full quadratic. Dropping those constraints when
maximizing $R$ can only increase this upper bound. Neither the
maximizing corner nor a raw bound that clears the target is a
feasibility result.

Improvement session `01a20f50-62e9-7deb-bbff-f738f20a7d1f`
replayed the decision in two fresh contexts with the same
pre-splice inputs and launch Work prompt. Only `CmmXzqX` got a
sentence suggesting that it price the entire restricted family
before subdividing it; `zckEjds` was the control. Success meant
choosing a justified cheaper next refit from a bound on the
whole box, not from another sampled blend. Regression meant
mistaking a relaxed bound for feasibility or closing a wider
domain; the same sound computation and decision counted as a
tie. Both priced the whole box, checked the inherited tests
at its corner, and chose joint atom weights instead of another
splice. Neither ran a constrained blend solver. They agreed on
$-8.52038\cdot10^{-9}$ across $2701$ cells, about
$8.42\cdot10^{-9}$ below the target. The corner failed both
inherited disk lists and the full quadratic. Each replay's
direct polarization evaluations agreed with its affine
evaluations within $10^{-18}$ in extended precision. These
were floating routing diagnostics, not ball certificates.
The historical block snapshot had SHA-256
`690ce029a85405aa86bb9e3825e22571a6b4504b988c2604a787d7bf45d15d37`;
it is not needed for the next refit.

Two follow-up screens on the same inputs sharpen the choice:

| Family and relaxation | Floating maximum |
| --- | ---: |
| Two-endmember box, surplus with all constraints dropped | $2.85937\cdot10^{-3}$ |
| Two-endmember box, inherited raw price | $-8.52038\cdot10^{-9}$ |
| Independent weights on existing atom sites, inherited raw price | $6.16324\cdot10^{-10}$ |

The first row chooses the larger of the two integrated $U$
contributions in each cell. It cannot reject the span. The
last row replaces each cell's two endpoints by all its saved
columns, evaluates the same $c_i$ on each atom, and sums cell
maxima. There were $83700$ entries, including repetitions;
the reference's cell averages were below those maxima. Thus
on that mesh the existing sites clear the raw gate, whereas
interpolating the two fitted tables does not. No constrained
atom refit was run in improvement. The comparisons do not
certify any nontrivial lower bound on feasible surplus.

**Independent peer reason.** Alice's [fixed-reference disk
result] at `4cda3a091f6f` compared the radius saving
$Z\lambda$ with the crossing-budget cost $2V\lambda$ of
paying for a $q^\lambda$ anchor bound, uniformly before
optimizing the radius. Its integer arithmetic check passed
here. It kept alternatives with fewer anchors or additional
divisibility open. The comparable improvement is to gate a
restricted family by its threshold before optimizing, not to
rank the two research branches. The replay offers no evidence
that the extra Work sentence improves this decision beyond the
existing brief, which already asks for a decision-changing
check. Leave the prompt and graph unchanged. Revisit only if
live runs again spend materially on an unchanged span toward a
fixed target without a comparably cheap upper screen. The
replay controlled the decision, not end-to-end time or live
mathematical value.

## Next worker

Start from the [checked recovery law]. For a finite refit, try
independent common weights on local joint atom sites before
adding more sites; the historical raw gate was open for that
larger family, not for its two-endmember span. To rebuild that
mesh from the [reference law], retain its jumps, split each
released slab at spacing $1/25600$, and add tail knots through
$56$. In units of $1/400$, the additional tail starts and steps
are $(2320,8),(5200,16),(8800,32),(12800,64),(16000,128)$;
restart at each listed start and include the final endpoint.
Use the [joint refit tangent][tangent] to integrate the three
raw coefficients in each cell. The old site rule used the
reference atoms, $0$, $1$, and interior stationary points of
the cell's scalar price in $u$. At nonnegative cell starts it
also used shifts of the price candidates (including $0$ and
$1$) by $\pm0.005$, $\pm0.001$, and $\pm0.0002$, clipped to
$[0,1]$.

Keep the full inherited quadratic and check both inherited
disk lists, raw price, and surplus on the same rounded law. If
a bounded refit misses, distinguish a priced restriction from
a solver failure before deciding between more sites and new
directions. Do not repeat the fixed-field $U$-only polish,
and do not read finite cap checks as a continuous witness.
No new exclusion was proved. Keep the Alpöge exclusion.

[polarization identity]: five-release-curvature-33.md#identity-and-uniform-localization
[fixed-reference disk result]: ../alice/jet-reference-disks.md
[checked recovery law]: five-release-recovery-33.md
[reference law]: deletion-laws/delete-33-tail-baseline.txt
[tangent]: five-release-joint-refit-33.md#price-on-the-full-domain
