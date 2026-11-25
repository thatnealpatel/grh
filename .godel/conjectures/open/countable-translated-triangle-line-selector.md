---
evidence_revision: 440840b2beadec23c287d91a93635905cef88b9c
---

# Test the countable translated-triangle line selector

**Proposition:** Fix known integer $q\ge2$, set
$G=(\mathbb Z/q\mathbb Z)^*$ and $d=|G|$. Use natural logs.
Let $A=\log 2$, $h=\mathbf1_{[0,A]}*\mathbf1_{[0,A]}$, and
$K(s)=((2^s-1)/s)^2$ with its removable value. For every
$(g,n,e)\in G\times\mathbb Z\times\{c,s\}$, put
$h_c(v)=h(v)\cos(nv)$ and $h_s(v)=h(v)\sin(nv)$, and set
$K_e(s)=\int h_e(v)e^{sv}\,dv$. The row is
$$
 H_{g,n,e}(X)=\frac{K_e(1)}d X-
 \sum_{\substack{\ell\text{ prime},\ \ell\nmid q\\
                  \ell\bmod q=g}}
 (\log\ell)h_e(\log(\ell/X)).
$$
Order $G$ by least-positive representative, enumerate $n$ as
$0,1,-1,2,-2,\ldots$, and for each $n$ list $g$ and then
$c,s$, retaining the zero sine rows. This gives a fixed
bijection with $j\ge0$. At prime $p$ with $P(p)\ge2$, report
only the one real row at $X=P(p)$ with index
$j=v_2(\operatorname{rank}(p))$. The one-based rank is among
all rational primes, including ineligible and erased ones.
Here $P$ is a known real polynomial of degree $D\ge1$ with
positive leading coefficient.

For known $\kappa>0$, allow an unknown combined
$O(N^{1-\kappa})$ arbitrary corruption and erasure budget
per late dyadic $[N,2N)$. For other readings assume uniform
tail limsup absolute error divided by $\sqrt{P(p)}$ at most
$\eta_q=(\sqrt2-1)^2/(8d)$. The indexed stream determines
for each named $\chi\bmod q$ and each $z$ in the open strip
its nontrivial zero order (zero for absence), with no height
bound, multiplicity cap, or supplied ordinates. Named orders
are those of the primitive inducer in the open strip.

**Source and payoff:** Replace the measurements in the line
selector of `single-scalar-coefficient-separation.md` at
`440840b2beadec23c287d91a93635905cef88b9c`, lines 181–228.
The comparison is with its finite band and shrinking radius,
not a claim of uniform separation for the original scalar.
Use the triangular contour and square term at
`6596fa6e00f481978d7f2792eec2b3dde99a8a29`, the finite
cycling at `836fa5e3174e0cb576774ac3660784748549cf1e`, and
the positive-noise median and selector at
`7e7144a3b79704b7233c880832296e381f49a701`. No raw-sign
criterion, GRH conclusion, optimal radius, or finite-work or
uniform-duration guarantee is proposed.

**Discriminating test:** Check the shifted contour at each
fixed $n$, including the principal multiplier and the square
prime root count in class $g$. Recheck the all-interval
prime bound in its primary source. Use consecutive full
ranks to compare each fixed row in every late cell against
the entire bad budget.
Check preservation of the noise bound by fresh medians. Peel
all right-of-line residues of the unmodulated cosine rows,
including intermediate strip edges; invert class Fourier
coefficients, then subtract all right-of-line terms
samplewise before each carrier's terminal medians. Test the
center with square bias removed and the signed line means
with no assumption that good noise averages converge. Test
nearest-integer carrier translation $K_c-iK_s=K(z-in)$ and
Fourier rounding with a joint cutoff, exercising $q=2$ and a
nonreal conjugate pair of unequal orders at high signed
height; check that omitting sine, reversing the shift, or
swapping labels is detectable. Verify same-label reflection
and the pointwise quantifier order without uniform carrier
onset. Contrast the pointwise separation for finitely many
fixed $L^1$ windows, not stream indistinguishability.
