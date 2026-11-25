# Buy the actual input before filtering singleton hits

The [singleton erasure bound][singleton] prices passes of one
frozen space, not the unrestricted widened-screen complement.
At radius $1.475$ its near-cap bins ask for an erased signed
radical of weight $1.475-o(1)$. The same erased factors now let
us count the heavier erased endpoint **at the actual input**.
This eliminates the previous large-radius capture rate on a
target-sized complement, even with unrestricted certificates.
It leaves the previous small-radius price unchanged.

## Count on a fixed mask

Use the same list, cuts, and notation as [the singleton
bound][singleton]. In particular $v=cF_1a$ is the complete
first input, and the second row at $d$ is

$$cF_2 h_d=dZ_d+q\beta_d,\qquad R_d=Z_d/h_d,\qquad S=R_d/R_e.$$

Fix the space $B$ of dimension at most $(\log q)^{1.44}$ and
one eligible erasure $E_v$ per actual $v$, with squarefree
product at most $q^r$. The number of hits in **any subset** of
the retained triples, uniformly for $0\le r\le1.475$, is at most

$$q^{\max\{A,J(\min(r,u_*))\}+o(1)},\qquad
 A=(671/900)C,\quad C=1.055,\quad
 J(u)=C-\frac7{18}(C-u/2),\quad u_*=\frac{5033}{3425}.$$

Fix one separating mask $T$ from the inherited subpower
family. It is disjoint from $E_v$ at the inputs being counted,
and the covered columns have all raw $h_dZ_d$ primes on
$T\cup E_v$. The inherited repeated-signature charge is
$q^{A+o(1)}$ and uses unpunctured actual pairs before the cuts.
For the remaining singleton hits, each actual endpoint has
$q^{o(1)}$ partners at its input on this mask: They must lie in
its projected $B|_T$ coset, with at most one column per
signature on $E_v$. This counts partners in either order.

Let $P\subset T$ be fixed pivots for $B|_T$. In dyadic bins
write $x,y$ for weights $\log_q$ of the two raw $P$-parts,
$t$ for the radical weight of the signed $[S]|_P$ support,
and $u$ for that of $[S]|_{T^c}$. Thus $0\le u\le r$ and
$t\le x+y$ up to bin errors. The inherited moving price
$M=u/2+.22t$ buys the signed radical on the two regions,
interpolates exact $S$, and recovers actual triples at subpower
cost. The reference price $D=C-.28\max(x,y)$ buys the actual
pivot-heavier endpoint and then uses the singleton bound. On
the same bin $\min(M,D)\le J(u)+o(1)$, by the inherited
$7/18,11/18$ combination. No new cost is imposed on the
repeated-signature branch.

## Cross at fixed input, with the erasure already named

Choose the endpoint with heavier full raw $E_v$-part of
$h_d Z_d$ (swap the order at constant cost). Write its weight
$b$; it is at least $u/2-o(1)$, since every outside signed
prime divides one of the two raw $E_v$-parts. Take uniform
bounds $h_d\le U=q^{.665+o(1)}$ and
$|\beta_d|\le H_0=q^{.390+o(1)}$. If this endpoint's combined
$E_v$- and $P$-parts exceed $2UH_0$, there is a third code:

1. Buy $v$ first. The smooth product $ca=v/F_1$ is at most
   $q^{1.720+o(1)}$, hence there are at most $q^{.860+o(1)}$
   choices by the eligible-smooth half-power bound (prime
   ceiling $O((\log q)^2)$). This names $c$ and the prescribed
   $E_v$; it does not choose an erasure afresh per endpoint.
2. Name the full $E_v$-part of $h_dZ_d$ at subpower cost.
   The floor $(2.1\log q)^2/(\log\log q)^4$ bounds both the
   number of available coordinates and the total multiplicity
   by $O(\log q/\log\log q)$. Choose a divisor $f$ crossing
   strictly above $2UH_0$, prioritizing $E_v$ factors. The
   required $P$-multiplier has weight at most $(C-b)_++o(1)$
   by the one-prime overshoot, so costs $.22(C-b)_+$ up to
   $o(1)$ by the [pivot Rankin bound][pivot].
3. Split $f=f_h f_Z$ with $f_h\mid h_d$, $f_Z\mid Z_d$,
   at divisor cost. The conditions $f_h\mid h_d$ and
   $cF_2h_d-q\beta_d\equiv0\pmod{f_Z}$ have index $f$ in
   $(h_d,\beta_d)$: Substitute $h_d=f_h k$ and solve for
   $\beta_d$ modulo $f_Z$, where $q$ is a unit. This does not
   require coprime filters. A determinant in the box has
   absolute value at most $2UH_0<f$, so any two qualifying
   vectors are collinear. Row primitiveness and $h_d>0$ give
   at most one. Its full output $cF_2h_d-q\beta_d$ has a
   deterministic sorted prefix $d$. Thus the filter gives
   an actual endpoint, not a hypothetical choice of partner.
   Its partners at this mask cost subpower by singletonness.

The local count is at most $q^{.22(C-b)_++o(1)}$ per actual
input, after which the input sum gives a price no greater than
$F(u)=.860+.22(C-u/2)$. Here $C-u/2>0$ on the stated range.
This is an alternative to the moving and reference codes, not
an additional factor in either.

If the chosen endpoint does **not** cross, its pivot weight
is at most $w=C-u/2+o(1)$ regardless of which endpoint has
larger pivot weight. Put $m=\max(x,y)$. Then

$$M\le C-.78w+.22m+o(1),\qquad D=C-.28m.$$

The minimum is at most $C-.4368w+o(1)$ by intersecting the
lines at $m=1.56w$. This branch is bounded by $J(r)$ for
$r\le u_*$, since $.4368>7/18$, and by $.916316$ throughout
the stated range. In the crossing branch $J(u)$ increases
and $F(u)$ decreases, meeting at $u_*$ with
$J(u_*)=50989/54800=.930456204\ldots$. The maximum of their
minimum for $u\le r$ is $J(\min(r,u_*))$. Sum the subpower
number of bins and masks, and add the repeated-signature
charge. The proof never changes the screen or assumes the
actual survivors fill any bin.

## Consequences and discriminator

At the same complement target $1.1354$, radius $1.300$ still
has hit exponent $.897500$ and sufficient capture loss
$.237900$. At radius $1.475$ the new hit exponent is
$.930456204\ldots$ and the sufficient loss is
$.204943795\ldots$. In particular the **previous** loss
$.203872222\ldots$ at $1.475$ would already imply complement
exponent at most $1.134328426\ldots$. On a target-sized
complement it is impossible, whether or not the certificates
are short. To tie the small-radius price at the same target,
the large radius needs a certified relative gain of
$q^{903/27400-o(1)}$. There is still no certified gain or
lower bound on either capture fraction. The upper-price
plateau after $u_*$ does not show that the assigned erasures
can be shrunk: The valuation-space witness may be nonzero on
erased primes absent from the actual signed support.

**Near the new large-radius cap.** For a bin of exponent
$J(u_*)-o(1)$, both $J(u)$ and $F(u)$ must reach that value
up to $o(1)$, so $u=u_*+o(1)$. In particular the old full
$1.475$ signed-radical bin now costs at most $.929850+o(1)$.
The slack identity for $M,D$ in the [singleton proof][singleton]
(with radius parameter $u$) gives $t=x+y-o(1)$ and $x-y=o(1)$;
then $M,D\ge J(u_*)-o(1)$ gives
$x,y=975/2192+o(1)$. The more precise input price
$.860+.22(C-b)_+$ also must reach the cap, forcing
$b\le u_*/2+o(1)$. Since the raw erased weights sum to at
least $u$, both are $u_*/2+o(1)$, and the sum differs from
the signed radical weight by only $o(1)$. Thus **at this new
cap** the erased raw product has negligible repetition and
cancellation, as does the pivot raw product. The same local
code, at most $q^{3861/54800+o(1)}$ per input in this bin,
requires $q^{.860-o(1)}$ distinct actual inputs to attain
the cap. These are necessary conditions on a near-saturating
bin, not conditions on each hit or on the whole complement.

The [short-seed handoff][seed] can use $u_*/2$ instead of
$1.475/2$ when pricing the outside radical near this cap. A
uniform shortening to strictly below $975/2192$ times
$\log q/\log\log q$ seeds would exclude that branch from
saturation: Its projected span costs $.44$ times the seed
coefficient, and $(J(u_*)-u_*/2)/.44=975/2192$. This still
does not follow from the inherited $.50$ cutoff. It does not
address long certificates.

If an admissible export appears, retain the [same-population
paired scoring][paired] with the updated losses. Without an
export, the repriced large-radius lower rate at target can
be falsified by a fixed saving below $3861/54800$ in the
number of **matched singleton cosets per actual input** in
a fixed neighborhood of the new cap shapes, uniformly in
the mask and assigned erasure. Outside that neighborhood
the price inequalities above give a fixed saving already.
The precise local test can fix both endpoints' full erased
parts, split between $h$ and $Z$, at subpower cost at that
input. With those parts and $v$ fixed, test the simultaneous
actual row conditions, including $dY=v-q\alpha_d$ and its
partner, on the matching of the two signature classes. The
current price uses only the second-row filter on one side;
a second nominal congruence index on that same row would
not prove a saving. If that local test does not save, the
count here supplies no lower capture bound; the alternative
is a direct count of unrestricted survivors, not another
relaxation of the radius. No RH or GRH conclusion or Alpöge
input is used.

Run `python3 .godel/alice/check-input-first-erasure.py` for
exact checks of the crossing, discarded bins, and thresholds.

[singleton]: singleton-erasure.md
[pivot]: global-pivot-row-price.md#single-rows-with-moving-and-with-fixed-inputs
[paired]: shared-erasure-radius-decision.md#next-worker-one-paired-gate-not-two-censuses
[seed]: singleton-handoff-decision.md#next-worker
