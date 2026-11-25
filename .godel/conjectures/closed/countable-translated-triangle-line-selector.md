---
evidence_revision: 440840b2beadec23c287d91a93635905cef88b9c
outcome: established
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

## Adjudication

**The radius is independent of height; the onset is not.** We first
recover exact off-line orders from the unmodulated class rows. Only
then do we select a carrier for a queried line ordinate. The estimates
below apply to the one stream defined above, not to a stream that can
be queried again at previously used primes.

**Fixed-row expansion.** Put $K_\pm(s)=K(s\pm in)$. Then
$K_c=(K_++K_-)/2$ and $K_s=(K_+-K_-)/(2i)$. For each fixed $n$,
both are entire and $O_n((1+|\Im s|)^{-2})$ uniformly on
$-1/2\le\Re s\le2$. Thus the argument at `6596fa6e`, lines 69–123,
applies to these continuous windows, including inversion at the knots:
Complete using $\ell^k\bmod q=g$, expand the indicator with weights
$\overline{\chi(g)}/d$, and integrate $X^s K_e(s)(-L'/L)(s,\chi^*)$
on $\Re s=2$. Replacement by primitive inducers costs $O_q(1)$ since
only boundedly many powers of each omitted prime lie in $[X,4X]$.
On the separated horizontal contours the logarithmic derivative is
$O_q(\log^2(2+|\Im s|))$, so the shifted transforms still kill the
horizontals at fixed $X$. The left integral is $O_{q,n}(X^{-1/2})$;
the residue at zero is bounded. Subtraction cancels the principal
residue $X K_e(1)/d$, reverses the zero signs, and **adds** the
signed square sum. In each root class $u^2=g$ the fixed-class PNT
and partial summation against the BV function $a\mapsto h_e(2\log a)$
give a main term $\sqrt X\int_1^2 h_e(2\log a)\,da/d$ with error
$o_{q,n}(\sqrt X)$. Substitution $v=2\log a$ gives $K_e(1/2)/2$
for that integral before the division by $d$. The higher powers cost
$O_q(X^{1/3}\log^2(2X))$. Hence for row $r=(g,n,e)$,
$$
 H_r(X)=\sum_z c_r(z)X^z+C_r\sqrt X+o_{q,n}(\sqrt X),\qquad
 C_r=\frac{K_e(1/2)}{2d}\#\{u\in G:u^2=g\},
$$
$$
 c_r(z)=K_e(z)V_g(m(z)),\qquad
 V_g(m)=d^{-1}\sum_\chi\overline{\chi(g)}m_\chi .
$$
The unit-height count with multiplicities at the same pin gives
$\sum_z |c_r(z)|(1+|z|)^{1/2}<\infty$ by quadratic decay. Real
windows and $m_\chi(\bar z)=m_{\bar\chi}(z)$ pair conjugate terms,
so cutting by real part leaves a real series.

**Majorities in one stream.** Put $e_0=\min(\kappa/2,1/20)$ and
$h_0=e_0/(2D)$. Partition each late dyadic block into
$\lfloor N^{e_0}\rfloor$ equal cells. The Guth–Maynard corollary
[Count of primes in short intervals](https://arxiv.org/abs/2405.20552)
has $x^{17/30+\epsilon}\le y\le x^{0.99}$ and error
$O_\epsilon(y\exp(- (\log x)^{1/4}))$. Take $\epsilon=1/10$ and
pack consecutive intervals of length $x^{9/10}$, losing at most
$O(N^{9/10})$ length per cell. Thus every cell contains
$m\gg N^{1-e_0}/\log N$ consecutive full prime ranks. Of any such
run, $m/2^{j+1}+O(1)$ ranks equal $2^j\bmod 2^{j+1}$. For every
**fixed** row $j$ this exceeds twice the entire block budget in every
sufficiently late cell, since $N^{\kappa-e_0}/\log N\to\infty$.
All these primes are then eligible. Removing erasures leaves a strict
good majority even if all the damage is targeted.

At a cut $a$, subtract recovered terms with $\Re z>a$ at each original
nonerasure's own argument. Write $S_{r,a}$ for the remaining zero
series. Let $M_{r,a}$ equal the lower median of those residual reports
of row $r$ on each polynomial image cell (zero if empty); use only an
increasing tail of $P$. Its image log-width is $O(N^{-e_0})=
O(X^{-e_0/D})$ by $P'/P=O(1/N)$. For log-displacement $0\le v\le1$,
$|e^{vz}-1|\ll\min(1,v|z|)\le(v|z|)^{1/2}$ in the open strip.
Thus the half-moment bounds the variation of $S_{r,a}$ on the cell by
$O_r(X^{a-h_0})$. The square roots on the cell differ by a relative
$o(1)$. The median lies between the extremes allowed for the good
reports, giving throughout the cell
$$
 |M_{r,a}(X)-S_{r,a}(X)-C_r\sqrt X|
 \le O_r(X^{a-h_0})+(\eta_q+o_r(1))\sqrt X .
$$
There is no inverse row-density multiplier on the noise.

**Exact peeling before noisy line selection.** Start with $a=1$ and
use only the $d$ cosine rows at $n=0$. For any one of them, set
$b=\max(1/2,a-h_0)$. The median Mellin germ, formed on $[B,\infty)$
from a fixed increasing-tail cell endpoint $B$ with measure
$X^{-s}dX/X$, is known for $\Re s>a$. It continues to $\Re s>b$ as
the holomorphic transform of $M_{r,a}-S_{r,a}$ plus
$$
 \sum_{\Re z\le a}\frac{c_r(z)B^{z-s}}{s-z}.
$$
Indeed, the discrepancy bound gives local absolute convergence there,
and the pole sum is normal away from its locally finite poles by
absolute summability. A finite prefix causes no singularity. By
uniqueness of continuation of the data germ, all nonzero residues in
$b<\Re z\le a$ are exact, independent of the discrepancy. Reset
$a=b$, subtract from original reports, and repeat. An intermediate
lower edge is included at the next step; at most $\lceil D/e_0\rceil$
steps reach $1/2$.

Union the right-of-line pole sets across these rows, taking missing
residues as zero. Division by $K(z)\ne0$ in the open strip gives all
$V_g$ at each such point. Orthogonality gives
$m_\psi(z)=\sum_g\psi(g)V_g(m(z))$, so no nonzero vector was lost.
The functional equation and conjugation give the same named order at
$1-\bar z$, hence all strictly left orders. For **any** fixed carrier
we now know the exact $c_r(z)$ for all $\Re z>1/2$. Subtract their
absolutely convergent sum from its original reports, then form its
fresh terminal median. There is no propagation of earlier median
errors, and no need for all poles to be visible in this carrier.

**Line selection.** At $a=1/2$ the normalized variation tends to zero.
Strictly left terms after normalization vanish by domination by
$|c_r(z)|$. Hence $M_{r,1/2}(X)/\sqrt X-C_r$ is the absolutely
summable line series plus an error of tail limsup modulus at most
$\eta_q$. Call its mean against $X^{-it}dX/(X\log(U/B))$ on $[B,U]$
$A_{r,t}(U)$. For the line series only the matched frequency survives
in the limit, by integrating each exponential and using domination.
For the error the unit twist cannot enlarge the modulus, and any finite
prefix costs $o(1)$. Thus $\limsup_U|A_{r,t}(U)-c_r(1/2+it)|\le\eta_q$,
with coefficient zero at absence. Subtraction of $C_r$ matters at the
center. No convergence of the error means is assumed.

Fix $t$ and choose a nearest signed integer $n$. For $z=1/2+it$ we
have $|z-in|^2\le1/2$ and $|2^{z-in}-1|\ge\sqrt2-1$. Therefore
$|K(z-in)|\ge k_0=2(\sqrt2-1)^2$. At a common output cutoff $U$ set
$$
 E_\psi(U)=\frac{1}{K(z-in)}\sum_g\psi(g)
 \left(A_{(g,n,c),t}(U)-i A_{(g,n,s),t}(U)\right).
$$
The real windows give complex twisted means. Since $K_c-iK_s=K_-$,
orthogonality and the triangle inequality give
$\limsup_U |E_\psi(U)-m_\psi(z)|\le 2d\eta_q/k_0=1/8$. Rounding the
real part is eventually exact for every label, including zero. For
each fixed $t$ this uses only $2d$ terminal rows. The stream therefore
defines the order function on the entire line, without an ordinate
list. Universal quantification over $t$ takes place **after** the
pointwise assertion; no common onset over the carriers follows.

**Sign and label checks.** For $q=2$, $n=t=0$, the sine row is zero,
$K(1/2)=4(\sqrt2-1)^2$, and $C_c=K(1/2)/2$. Omitting the bias at
absence with error $+\eta_2$ gives $1/2+1/32$ instead of $1/32$.
For $q=5$, $g=4$, $n=1$, the two root classes give sine bias
$K_s(1/2)/4\simeq0.11035555$, not zero.

For an independent signed test take $g_k=2^k\bmod5$,
$\chi_l(g_k)=i^{kl}$, $t=-2048.5$, and $n=-2048$. Synthetic orders
$(0,6,0,2)$ and their conjugate-label word at $-t$ give
$V=(2,-i,-2,i)$ at $t$. Integrating the two real windows at $z$
(Simpson, 131072 panels on each linear piece) gives translated gain
$0.6794903983$ in modulus versus $3.26985\cdot10^{-8}$ for the other
shift. For nonconvergent mean errors put $L_0=0$, $L_b=2^{b^2}$ for
$b\ge1$. In log-time blocks ending at $L_b$ whole periods add the
real normalized error $(-1)^b\eta_q\Re(\phi e^{it\log X})$, with
$\phi=i^{-k}$ for cosine and $i^{1-k}$ for sine. Starting log-time
at zero, the twisted mean perturbation at endpoint $b$ is exactly
$\tfrac12\eta_q\phi\sum_{h=1}^b(-1)^h(L_h-L_{h-1})/L_b$ by
whole-period integration. The length ratio tends to opposite signs on
the two subsequences. Applying these perturbations to the exact row
coefficients yields real parts of $E_{\chi_1}$ of $6.02946$ and
$5.97053$ at endpoints 8 and 9. Both recover the word. At endpoint 8
dropping sine in this formula gives $(0,3,0,1)$; using the other
denominator gives a $\chi_1$ estimate greater than $10^8$ in real
part; conjugating the inversion characters gives $(0,2,0,6)$. These
are checks on the selector, not proposed Dirichlet zero data.

**Scope.** At the evidence target, lines 181–192 and 220–228 of the
single-scalar card use a finite-band gap. For finitely many fixed
windows here, Riemann–Lebesgue applied to $e^{v/2}h_e(v)$ sends every
transform to zero in both height tails. Even the coefficient vector
for a unit order approaches the absent vector. This concerns pointwise
coefficients, not indistinguishability of actual streams. Changing the
rows as above strengthens the consumer; it neither alters that scalar
result nor gives a raw-sign criterion, GRH, or a finite-time decoder.
