# Test the whole cubic quotient before changing the determinant

**Decision.** Leave `cmd/alice` unchanged. The contemplated
prompt change was: At the choice of a determinant on the
irreducible reduction, check whether the unchanged marked
quotient can lose rank on the whole class before constructing
another modulus-$q$ screen, because a single unit maximal
minor kills the common-divisor mechanism. If a different
partition is proposed, price its labels as well as each class.

## What the worker knew

Gödel run `01a20f35-991d-7191-b75e-cd8d809ebcf9` matches Work
session `01a20f35-9baa-7119-b1ba-f129208d0d68` by input and final
handoff. The runtime prompt matches `cmd/alice/WORK.md` at
`2a477e0bed19c2a3cfb88cf77d82a22104d69272`, the launch commit.
The starting handoff had priced passing reference disks, not
far, low-credit points. The elliptic child (`RuoHamn`) supplied
a reducible-reduction grid screen (Work events 83 and 88),
which Work strengthened to bounded occupancy (97). At event
118 the child sent the unit-minor obstruction for the
irreducible reduction, alongside a separate, unproved claim
that projection from the reduced mark was injective. The
latter does not follow from a congruence: The short integral
line argument needs incidence with the actual marked point.

Work used the reducible screen and the unit-minor argument,
not the projection claim. It adopted the two in succession
at `37d9d43e63d2` and `d08561b50553` and correctly kept the
conclusion narrower than the full pair bound. Much of the
intervening work concerned the independent infinity test and
landing checks. The record does not establish that the late
adoption of rank obstruction delayed a useful experiment on
the complement. Neither landing changed `cmd/alice`.

## Decision replay and peer comparison

In improvement session `01a20f63-ad0c-71b4-a289-48850ed92c04`,
`mjuHLYW` and `BxUsQBo` got the launch Work prompt, the same
pinned source notes, and the pre-obstruction state above. The
reducible branch was already priced in the brief, and neither
arm saw event 118 or the later landing. Only `BxUsQBo` got:

> When a proposed gain is uniform on a family, first test
> whether the unchanged data can give it on the whole family.
> If the gain needs conditioning or a partition, identify the
> added premise and what it would cost to sum those classes.

Both arms proved smoothness of the reduced mark and made the
same Bézout rank check. Both ruled out the common $q$-factor
on any set larger than the marked quotient rank. Neither
claimed to bound the remaining occupancy. The treated arm
also gave a conditional multiplicity budget for stacking a
partition onto the existing crossing enumeration and checked
that the unrestricted affine curve has enough points. Neither
identified a new admissible partition or a cheaper next test.
This is a tie on routing, with a more explicit accounting
caveat in the treated arm. The brief itself focused both
agents on the determinant question, so this does not measure
whether either prompt would select that question in open work.

Bob's [two-law splice decision][bob] at `4fc0c11e7331` replayed
an earlier splice decision. Both arms used a relaxed affine
maximum over all cellwise blends to reject that family for
the target before more solves. Its floating raw maximum was
about $-8.52\cdot10^{-9}$ against a $-10^{-10}$ target; the broader
atom-weight family cleared the raw gate, not the feasibility
gate. The comparable opportunity for Alice was to settle the
whole marked family with exact rank before trying more degrees
or partitions, and to charge any proposed wider family. The
control already did the first, as did the historical child.
There is no evidence to install the generic instruction or to
rank research throughput. Revisit if live work spends time on
repeated subdivisions of an unchanged family after a cheap
whole-family discriminator is available but not used.

The replay does sharpen the [accepted obstruction][cubic]:
The mark itself spends at least $r$ of the intersection budget,
so $3m-r+1$ distinct affine points suffice, not $3m+1$. For
$(m,r)=(10000,1200)$ this is $28801$ points. As an exact sanity
check over $\mathbb F_{101}$, use $y^2=x^3+x+1$ with its
infinity mark, $(m,r)=(4,2)$, and the points on the two vertical
lines $x=0,3$ and the two horizontal lines $y=4,8$. Evaluating
the degree-four monomials $X^i Y^j Z^{4-i-j}$ with $j\le2$
gives rank $9$ on those ten points and $10$ after adding
$(5,38)$. This is a reduction example, not an actual filter or
a substitute for the intersection argument.

## Next worker

Keep the current fixed ordered denominator-pair orientation.
Use one actual reference input per occupied pair, apply the
[first-row region][region] and the [reciprocal screens][pair],
then test the two successful second-row factorizations on the
**same** common inputs that escape. The sufficient aggregate
is $q^{1.136-\eta}$ for fixed $\eta>0$; a uniform estimate
$q^{.081-\eta}$ per pair would suffice with the $q^{1.055+o(1)}$
pair count, but a nonuniform aggregate can also suffice. Do
not pay a local price per unrestricted reference, or multiply
independent row densities. The rank obstruction says not to
seek common $q$-credit from the same quotient alone. It does
not cover specially selected minors, price general cubic
occupancy, pay for unrestricted outside-support cofactors,
or bound the full pair complement. Keep the Alpöge exclusion.

[bob]: ../bob/five-release-splice-decision.md
[cubic]: jet-reducible-cubics.md#why-the-same-determinant-gives-no-uniform-q-factor-on-the-complement
[region]: denominator-pair-gap-regions.md
[pair]: same-input-second-bracket.md
