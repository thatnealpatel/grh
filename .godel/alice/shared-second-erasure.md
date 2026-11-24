# Charge a shared second-output erasure only once

The [pivot-row count][pivot] allows a different erasure on
every triple. The proposed occupancy test instead uses one
$E_v$ at each actual complete input $v$. This distinction
lowers the passing price: At radius $1.300$ the proposed
$q^{-.1185-o(1)}$ fraction can hold only if the maximizing
[gap-screen complement][screen] already costs at most
$q^{1.1249+o(1)}$. It is still possible to enlarge the
radius within the triple budget. Neither conclusion
establishes occupancy or gives a lower bound on the
complement's size.

## The shared-erasure count

Fix one actual list in the scope of the [three-ratio
count][three], with its cuts. Use its notation:

$$v=cF_1a=dY+q\alpha=eY_0+q\alpha_0,\qquad
cF_2h=dZ+q\beta,\qquad cF_2k=eZ_0+q\beta_0.$$

For an ordered triple $(v,d,e)$ let $S=kZ/(hZ_0)$.
Prescribe one rational linear space $B$ of dimension at
most $(\log q)^{1.44}$, and an eligible prime set $E_v$
with product at most $q^r$ for each actual $v$. Here $r$
is bounded, fixed, and nonnegative. The choices may use
the whole list and the maximizing screen. Count triples
for which $[S]$ agrees with an element of $B$ off $E_v$.
For **any subset** of the retained triples the count is
at most

$$q^{.9284+.06r+o(1)}.$$

All estimates are uniform in these choices. The same
proof works if the one erased set is prescribed at the
actual heavier reference identified below, rather than at
its input. It does not allow choosing the erasure separately
for each partner of that reference.

**Common pivot code.** Choose base pivots $P$ for $B$.
Bin the sizes of $(hZ)_P,(kZ_0)_P$ dyadically, put their
ordered exponents at $x\le y$, and call the heavier
endpoint $(v,e)$, swapping names for the count if needed.
Use a fixed tie rule. Reversal negates $[S]$ and preserves
the test, so recovering the original order costs at most a
factor of two. Both exponents are at most $2.110+o(1)$.
There are $q^{o(1)}$ bins.

For any given $E$, complete $P$ deterministically to
pivots of $B_E=B+\mathbb Q^E$. The base rows remain
independent on the enlarged space. The pass condition is
exactly $[S]\in B_E$. There are at most $|E|$ added rows,
and the prime floor $(2.1\log q)^2/(\log\log q)^4$ gives
$|E|=O(\log q/\log\log q)$. All absolute valuations of
$[S]$ have sum $O(\log q/\log\log q)$ by the same floor
and the polynomial height of the four raw factors. Thus
the signed valuation tuple on the **named** added rows has
$q^{o(1)}$ possibilities, by stars and bars with signs.
No bound on the coefficients of $B$ is needed.

**Moving-reference price.** Enumerate $E$ as an
eligible-smooth squarefree product at $r/2$, and the two
$P$-supported products in their bins at $.22(x+y)$. Here
and below the Rankin prices use the prime floor above and
the smooth half-power estimate uses the eligible ceiling
$X=O((\log q)^2)$. Split each product into its two actual
factor parts at divisor cost. These specify the base pivot
values of $[S]$. Name the added pivot values at subpower
cost. Injection on $B_E$ determines exact $S$, which gives
at most $q^{o(1)}$ triples by [global exact recovery][exact].
The price for the bin is $r/2+.22(x+y)$, including inputs.
No assumption about shared erasure is used in this price.

**Fixed-reference partner price.** Alternatively, count
the heavier actual columns globally. Since
$(keZ_0)_P\ge(kZ_0)_P$, the [moving-input row sieve][pivot]
costs $1.055-.28\min(y,2.110)=1.055-.28y+o(1)$
for them. Each fixes its actual $v$ and the reference
factors. Now $E_v$ and the completed pivots are known.
Only the lighter $(hZ)_P$ and its split must be enumerated,
at price $.22x$, plus the subpower added pivot values.
Recover exact $S$ as above. This determines $Z/h=S Z_0/k$
and hence the positive coprime pair $(Z,h)$. The actual
$v$ fixes $c$. Since $Z=q^{1.445+o(1)}>2qH$, the interval
$[-qH,qH]$ contains at most one representative of
$cF_2h\bmod Z$. It fixes $q\beta$ and then $d$ by the
second row. Thus the price at the actual reference is
$.22x$, without an erasure sum, and the price for the bin
is $1.055-.28y+.22x$. This counts partners at the reference's
actual complete input, not anywhere on the list.

Take the minimum of the two bin prices. It is at most
their convex combination with weights $.12,.88$, namely

$$ .9284+.06r-.22(y-x)\le .9284+.06r. $$

Summing bins proves the claim. For the radii below the
lines meet at $x=y=2.110-r$; the bin ledger alone gives no
further saving there. A bin within exponent $\delta$ of
the capacity must have both prices at least the capacity
minus $\delta$, up to $o(1)$. In particular
$y-x\le\delta/.22+o(1)$, and $x+y$ is within $O(\delta)+o(1)$
of $4.220-2r$. This is a necessary condition on a
near-saturating bin, not a claim that such bins occur.

## Decision for the capture test

Let $C_{\rm off}$ count actual retained ordered triples in
the maximizing gap-screen complement. At $r=1.300$, one
frozen space with shared erasure passes at most
$q^{1.0064+o(1)}$ of them. Thus the proposed fraction
$q^{-.1185-o(1)}$ would already imply
$C_{\rm off}\le q^{1.1249+o(1)}$. Do not treat that fraction
as a plausible near-budget occupancy target at this radius
without evidence of an actual arithmetic saving.

A revised target keeps the fraction and raises the shared
radius to $1.475$. The upper passing price there is $1.0169$;
that fraction would give $C_{\rm off}\le q^{1.1354+o(1)}$.
The maximizing passing screen costs $q^{1.135+o(1)}$.
For this fraction the price stays strictly below $1.136$
at every fixed radius $r<1.485$.
The short-seed upper price from the [pivot-row count][pivot]
becomes $1.475/2+.220=.9575$: For each subspan using at
most $.50\log q/\log\log q$ frozen seeds, only the erasure
has a power price, and enumerating the subspans costs
$.220$. Those certificates cannot meet the revised
fraction unless $C_{\rm off}\le q^{1.076+o(1)}$.

The next test must therefore exhibit longer-certificate or
non-seed-space hits on **actual off-screen edges**, with a
single $E_v$ scoring all edges at its input. It is not
sufficient to optimize erasure separately for each edge,
or to count monochromatic pairs that failed retention or
passed the maximizing screen. No admissible census or
lower bound for nonseed hits is established here.

Run `python3 .godel/alice/check-shared-second-erasure.py`
to check the bin coefficients and the radius ledger.

[pivot]: global-pivot-row-price.md
[three]: global-three-ratio.md
[exact]: joint-valuation-escape.md#two-recovery-facts
[screen]: denominator-pair-gap-regions.md#after-work-spend-the-full-rank-margin-before-testing-the-second-row
