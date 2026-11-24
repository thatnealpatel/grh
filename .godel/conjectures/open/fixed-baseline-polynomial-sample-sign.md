---
evidence_revision: 1344a39f1fb2c622fafd8f9c813da961976ecdc5
---

# Test one-sided signs on polynomial samples

**Proposition to test:** Retain the absolute $C,D\ge1$ of
`1344a39f1fb2c622fafd8f9c813da961976ecdc5`. For every
integer $q\ge2$ and every fixed positive integer $B$, put
$m=\max(8,\lceil C\log(2q)\rceil)$, $M=10^{15}$,
$a=\log 2$, $h_m=\mathbf1_{[0,a]}^{*m}$, and
$k_m=4h_m^{(4)}-5h_m''+h_m$. With natural logarithms let
$$W_{q,m}(X)=\sum_{p\nmid q}(\log p)
[Mh_m(\log(p/X))
 +\mathbf1_{p\equiv1\bmod q}k_m(\log(p/X))].$$
Joint GRH for the primitive inducers modulo $q$, including
zeta, is equivalent to $W_{q,m}(n^B)\le M n^B$ for every
positive integer $n$ with $n^B\ge(2q)^D$. In the reverse
direction, an arbitrary eventual tail of these signs should
suffice. No uniformity of converse estimates in $B$, signs
between samples, or comparisons of samples are premises.

**Source and payoff:** The polynomial-onset landing proves
strict increase on a full real interval under joint GRH.
The pinned fixed-baseline landing
`f5fbeb09e9b972565848e25ac295f3341a537afd` gives the
unconditional mean and the exact prime-deficit transform.
This operator proposal replaces the continuous witness by
one sparse sequence of one-sided bounds, not by a finite
test or by monotonicity of the sampled values.

**Discriminating test:** Anchor at the last sample and
use the exact polynomial cell length to interpolate a power
lower envelope for $H=MX-W_{q,m}$. Add that envelope and
test whether Landau forces a better zero bound on the open
half-plane beyond the envelope exponent and $1/2$. Check
all pole signs, visibility, and the endpoint at one. From
the resulting open zero-free region alone, shift the
prime-power derivative contour to its right. Check the
multiplier $sK_f(s)$ at order eight, the principal residue,
character averaging, and the prime-power subtraction.
Spend the gap exponent again and verify finite termination
at $1/2$ for every fixed $B$, including boundary zeros.
Verify the forward signs using the unchanged onset and mean.
