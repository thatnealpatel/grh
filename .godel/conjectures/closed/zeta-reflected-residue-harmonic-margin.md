---
evidence_revision: 2f8680b4990afd40938e675f8c8cf2d2ad495050
outcome: established
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

**Decision.** Both parts hold under the hypotheses above.

Let $F(z)=z(z-1)\pi^{-z/2}\Gamma(z/2)\zeta(z)/2$,
$z=\sigma+it$, $w=1-\bar z$, and $\sigma=1+1/D$. In
the difference of the two Hadamard log derivatives, the
constant and the regularizers cancel. By the functional
equation and reality, $F'/F(w)=-\overline{F'/F(z)}$.
For each $\rho=\beta+i\gamma$, the real kernel at $z$ is
$p_\rho=(\sigma-\beta)/((\sigma-\beta)^2+u^2)$; at $w$
the kernel of $1-\bar\rho$ is $-p_\rho$. Reflection
preserves multiplicity, and the real sums converge
absolutely (their tails are $O_z(\sum_\rho |\rho|^{-2})$
for the order-one completion). Thus the real difference is
$2\sum p_\rho=2\Re F'/F(z)$. In the latter log derivative,
$\tfrac12\Re(\Gamma'/\Gamma)(z/2)$ is
$\tfrac12\log(2+|t|)+O(1)$ by Stirling and boundedness
at small height. The two rational terms cost $O(1+D)$,
and $|\zeta'/\zeta(z)|\le\sum_{n\ge2}(\log n)n^{-\sigma}
=O(D^2)$. Hence the positive sum, *not twice the sum*,
is at most $\tfrac12\log(2+|t|)+O(1+D^2)$.

Write $K_0=(1/4+u^2)^{-1}$, $v=4u^2$, and
$G(x)=(1+v)/(x^2+v)$. The residue denominator factor
relative to $K_0$ is $G(2\beta)$; the Poisson term relative
to $K_0/2$ is $xG(x)$ for $x=2(\sigma-\beta)$. For every
$v\ge0$ these ratios are between $1$ and $(2\beta)^{-2}$,
and between $x$ and $1/x$, respectively. On the near-line
set, both arguments differ from $1$ by at most
$e=2(1+c)/D<1$ eventually. The first ratio is at most
$(1-e)^{-2}$ and the second at least $1-e$, independent
of the offset. At $\beta=1/2\pm\eta/D$ with $0<\eta\le c$,
the absolute numerators of a pair of multiplicity $m$ sum
to $2m\cosh(\eta)/\sqrt X$, versus a Poisson sum of at
least $m(1-e)K_0$. At $\beta=1/2$ these quantities are
$m/\sqrt X$ and at least $m(1-e)K_0/2$, counting each
copy once. Reflection keeps $\gamma$ fixed, so neither
the height window nor its boundary splits a pair. Summing
gives an absolute cost at most
$2\cosh(c)(1-e)^{-3}\sum_\rho p_\rho/\sqrt X$ by
positivity. The half-log bound cancels the $2$ and leaves
an additive $O_{c,M}(1/D+(1+D^2)/\sqrt X)=o(1)$.

For $K=2/\pi$, integrating $\cos u\cos(2ju)$ over
$[-\pi/2,\pi/2]$ with multiplier $2/\pi$ gives
$a_j=4(-1)^{j-1}/(\pi(4j^2-1))$. The mean is $K$.
Since $|a_j|/K=1/(2j-1)-1/(2j+1)$, the retained
mass is $100K/101$ and the tail costs at most
$(K/101)(1+o(1))$ after summing the prime weights.
At $|y|\ge5$ the weighted pole cost is at most
$\sum_{j=1}^{50}|a_j|/(1+100j^2)<K/101$.
The fixed modes have $\log(2+|2jy|)=s\log q+O(\log 100)$
and $s=O(1)$ uniformly. Multiplying their height bounds
by the retained mass costs at most $K\cosh(1/2)s/A+o(1)$,
not fifty height terms. Subtracting the constant, tail,
pole, and height bounds from the failure lower bound gives

$$
KC X^{-1/8}\max_{1\le j\le50} B_\zeta(2jy;1/2)
\ge \left(\tfrac23-K-2K/101\right)
 +\tfrac23(1-K\cosh(1/2))s-o(1).
$$

Using $\pi>3.14$ and $\cosh(1/2)\le\sum_{k\ge0}8^{-k}
=8/7$ (since $(2k)!\ge2^k$), the constant exceeds
$814/47571>0.017$ and the slope exceeds $598/3297>0$.
Since $s\ge0$, the uniform error leaves a fixed positive
margin. This proves the conditional packet implication,
not the contour, the strip, an occurrence of failure, or
an upper bound on the packet.
