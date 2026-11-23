---
evidence_revision: 77927754e54e5b19da0983def22d8daccda5d8cf
---

# Short brackets at a selected reference cost at most $q^{.995+o(1)}$

At $g=1$, fix a first incidence, its ordered two-position list, and the actual remaining partner fibers $C_d$ after the full cofactor cut. For each nonempty $C_d$ choose any actual $c_0(d)$, with no restriction on how the choice depends on the fiber. For either row $i$, write $x_i(c)=F_i h_i(c)$ and $cF_i h_i(c)-dy_i(c)=q\delta_i(c)$, where $q$ is prime and $(x_i(c),d)=1$. The smooth coordinates have prime factors at most $X\asymp(\log q)^2$, $Z/X<c,d\le Z=q^{1.055+o(1)}$, and $h_i(c)=q^{.665+o(1)}$. A column fixes the rows on its list.

**Claim:** Uniformly in the input incidence, denominator, position, and choice of reference, at most $q^{.4675+o(1)}$ distinct endpoints $c\in C_d$ satisfy $|\delta_i(c)h_i(c_0)-\delta_i(c_0)h_i(c)|\le q^{.935}$. The union over positions and denominators costs at most $q^{.995+o(1)}$. This is a short-bracket exclusion, not an estimate for the remaining far endpoints.

**Source and payoff:** [One actual reference per denominator](../../alice/one-reference-lifts.md), “Price of a short bracket,” is used in the same note's partner reduction and in the new “After Work” paragraph of [Simultaneous modular output tests](../../alice/simultaneous-output-cuts.md). Without the exclusion at this price, the selected-reference reduction cannot charge short brackets to the stated exceptional budget by this argument.

**Discriminating test:** Derive the signed interval and its unit-slope congruence modulo the actual denominator at fixed $h=h_i(c)$. Reconstruct a uniform strip count with $K=q^{.935}/h_i(c_0)$ and $V=ZK/d$, charging singleton filters, ordinary direction occupancies, and any exceptional nearly parallel direction separately. Check that filtering by $e\mid c$ multiplies the index even for $(e,d)>1$, recover $e$ with the filtered step content, count positive smooth values along an affine line, and verify the exponent after summing over $h$ and $d$. As finite checks of the arithmetic, enumerate smooth numerators for $X=5$, $d=110592$, $Z=2d$, $K=3$: Use $(a,b,e)=(1,0,512)$ and $(125^{-1}\bmod d,402-d,625)$ in the strip $u\equiv ac\pmod d$, $|u-b|\le K$, $e\mid c$. These probe horizontal filters sharing factors with the modulus and oblique filters with nontrivial line step. They test the relaxed strip, not the existence of asymptotic prime-conductor partner families.
