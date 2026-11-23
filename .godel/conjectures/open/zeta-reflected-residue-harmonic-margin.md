---
evidence_revision: 2f8680b4990afd40938e675f8c8cf2d2ad495050
---

# Does the reflected zeta residue cost leave a strict harmonic margin?

**Hypotheses.** Let $X=(A\log q)^2$, $D=\log X$, and
$H=X^{3/8}D$. Take the zeta residue contour, pole
$P(t)=X^{-it}/(1-it)^2$, and reflected $7/8$ strip as
inputs. Count zeros with multiplicity and put $u=\gamma-t$.
Work uniformly for real $t$ with
$\log(2+|t|)\le M\sqrt X$, for each fixed $M$. For the
consumer take the real endpoint setup, the prime weights of
mass $1+o(1)$, and the stated uniform failure inequality
$h_d(y)\ge (1+s)/A-o(1)$ with
$s=\log(2+|y|)/\log q=O(1)$. Use the stated allowance
$C X^{-1/8} B_\zeta(t;c)+o(1)$ for the other residues,
where $B_\zeta$ sums $(1+u^2)^{-1}$ over $|u|\le H$ and
$\beta>1/2+c/D$.

**Proposition to test.** For each fixed $c>0$, the sum of the
absolute residues on $|u|\le H$, $|\beta-1/2|\le c/D$ is
at most $\cosh(c)\log(2+|t|)/\sqrt X+o(1)$ uniformly.
With $A=3/2$, $c=1/2$, $J=50$, $Y=5$, this coefficient
in the truncated cosine envelope leaves a uniform positive
margin in the packet inequality for all failing twists
with $|y|\ge Y$ and sufficiently large $q$.

**Source and payoff.** [Bob, (1) and (2)](../../bob/endpoint-zero-packets.md)
at `e84c4f374513298b41b0ace82b4140ae8fe15595` feed
[Alice, “Spend the height term once”](../../alice/single-endpoint-harmonics.md)
at the evidence revision. A missing factor or nonuniform
error would invalidate this justification for a positive
packet threshold independent of twist and height.

**Discriminating test.** Subtract the two Hadamard log
derivatives and compare the exact positive Poisson terms
with absolute residues for one reflected pair and one
on-line zero, retaining multiplicity. Bound the comparison
error for every real $u$ and the completed derivative error
through the allowed height. Independently integrate the
cosine coefficients, telescope their absolute mass and
tail, and check the pole and height costs and the strict
budget at the specified parameters. Do not test the strip,
contour, or the occurrence of any failure.
