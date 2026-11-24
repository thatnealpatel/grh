---
evidence_revision: 6169a926323525cf7f02428e73cee7d63e68d694
outcome: established
---

# Test one triangular stream for signs and labelled divisors

Use natural logs. For each integer $q\ge2$, list the units as
$g_0=1,\ldots,g_{d-1}$ in least-positive order, $d=\varphi(q)$.
Let $\ell$ be the least prime greater than $d$,
$\alpha=2^{1/\ell}>0$, and $r=(10^6\lceil\log(2q)\rceil)^{-1}$.
Use the weight
$$w(g_j)=1-rv_j,\qquad v_j=\tfrac12\mathbf1_{j=0}
 +\alpha^{j+1}/(8d).$$
For $h=\mathbf1_{[0,\log2]}*\mathbf1_{[0,\log2]}$, put
$$H(X)=\bar wX-\sum_{p\nmid q}(\log p)w(p\bmod q)h(\log(p/X)),$$
with $\bar w=d^{-1}\sum_j w(g_j)$ and the sum over primes.

**Proposition:** On joint GRH for all primitive inducers
modulo $q$, including zeta, $H(X)>\sqrt X/25$ for every
real $X\ge2$, with no link between $q$ and $X$.
Fix known $q$, a known real polynomial $P$ of degree $D\ge1$
with positive leading coefficient, and known $\kappa>0$.
At primes $p$ with $P(p)\ge2$, receive an indexed real value
$y_p$ or an erasure. At most $O(N^{1-\kappa})$ entries per
late block $[N,2N)$ are erased or arbitrarily corrupted,
with unknown bad set. Uniformly on the good tail,
$y_p=H(P(p))+o(\sqrt{P(p)})$. Joint GRH is equivalent to the
count of reported raw negatives, omitting erasures, being
$O(N^{1-k})$ for some $k>0$. The same scalar data determine
every named primitive inducer's exact nontrivial zero divisor,
including shared and central orders. Use signs for the first
readout and scalar values for the second; do not synthesize
either old operator from the samples. No finite work or
stability is asserted.

**Source and payoff:** All four pins are accepted ancestors:

- `068a54ef817f1d9b6a9ce77a4a0f73db4bf7456a`,
  `order-two-discounted-onset-two.md`: Ordinary-prime floor
  and identity-class discrepancy.
- `6596fa6e00f481978d7f2792eec2b3dde99a8a29`,
  `triangular-weighted-character-zero-divisors.md`:
  Character expansion and Fourier label inversion.
- `2a477e0bed19c2a3cfb88cf77d82a22104d69272`,
  `order-two-prime-index-violation-phase.md`: Continuous
  Landau, half-moment propagation, and prime mass.
- `6169a926323525cf7f02428e73cee7d63e68d694`,
  `robust-prime-index-labelled-zero-divisors.md`:
  Residual medians, Mellin strips, and the center.

The last landing proves its consumer for a different weight.
The proposed joint use tests compatibility of its label
coordinates with a uniform sign margin and negative real
residues, rather than combining two older measurements.

**Discriminating test:** Insert $\overline{\chi(g)}$ in the
orthogonality bound for each class, removing powers selected
by $p^k\equiv g$, and compare the discounted total loss to
the three certified ordinary-prime floor bounds. Derive the
character expansion, grouped residue signs, and exact
coordinates of $dc(z)/K(z)$ in the powers starting at
$\alpha^1$, including $d=1$ and arbitrary shared orders.
Check Landau without attainment at the top edge, propagate
late excursions at thresholds above the noise, and test the
prime mass against the whole bad budget. Verify realness,
samplewise subtraction, the median strip error, same-label
reflection, and square-bias subtraction at zero frequency
for this weight, not just for the earlier operator.

## Adjudication

**One stream suffices.** The spike fixes a sign without occupying
any coordinate needed to decode a label. The first readout counts
raw reported signs; only the second readout uses the scalar values.

**All moduli and scales.** Put $Y=\sqrt X$, $L=\log(2q)$, and
let $P_g$ be the unweighted triangular prime sum in class $g$.
Write $H_{\rm all}=X-P_{\rm all}$ for the ordinary deficit and
$P_{\rm bad}$ for the sum over primes dividing $q$. Exactly,
$$H=H_{\rm all}+P_{\rm bad}-r\sum_j v_j(X/d-P_{g_j}).$$
Since $\alpha^d<2$, $\sum_jv_j<3/4$, and all weights lie
strictly between $1-3/(4\cdot10^6)$ and one. On joint GRH,
insert $\overline{\chi(g)}/d$ in the character sum at the onset
pin, lines 230–243. Only the principal pole contributes $X/d$.
The absolute coefficients sum to one, so the individual budgets
$108YL$, $10$, and $3\log q$ for nontrivial zeros, trivial zeros,
and omitted Euler factors still suffice. Orthogonality after
restriction selects $p^k\equiv g$. Removing proper powers costs
at most $2\log 2\,\vartheta(2Y)<4Y$, since each base is at most
$2Y$ and has at most two powers in the open support $(X,4X)$;
here $\vartheta(t)\le t\log4$ is the ordinary prime log sum.
Thus $|X/d-P_g|<200YL$ independently of $g$. As $P_{\rm bad}\ge0$
and $rL\le10^{-6}$, the loss from $H_{\rm all}/Y$ is less than
$0.00015$.

Use the ordinary bounds *before* the old discount (onset pin,
lines 206–228 and 247–276). For $Y\le256$ the floor is
$0.20(127/128)-7/64$ by the certified grid and interpolation.
For $256\le Y\le4096$ it is $0.312-0.27066$ by the square grid
and ordinary zero budget. For $Y\ge4096$ it is
$0.07248-1.84/64-2/(4096\cdot4095)$ by the full square formula.
The latter two use the favorable trivial-zero sign in the ordinary
deficit. Subtracting $0.00015$ from these floors gives, exactly,
$7113/80000$, $4119/100000$, and $228428303/5241600000$.
Even the smallest is $119/100000$ above $1/25$. This uses the
landed finite certificate, not a new sieve or a bound on $q/X$.

**What produces a pole.** Fix $q$ from here on, without GRH.
Set $K(s)=((2^s-1)/s)^2$ by continuity at zero and
$b_\chi=d^{-1}\sum_jw_j\overline{\chi(g_j)}$. Completing the
sum uses $w(p^k)$, not $w(p)$, so Fourier inversion gives the
Mangoldt sums of the characters with coefficients $b_\chi$.
Passing to primitive inducers costs $O_q(1)$ by the bounded number
of exponents per omitted base in the support. At the expansion pin,
lines 69–123, the contour shift applies to each primitive sum before
weighting: $K$ decays quadratically, the selected horizontal heights
cost $O_q(\log^2(2+|t|))$ for the log derivative, and the line at
$-1/2$ costs $O_q(X^{-1/2})$ after integration. The residue at one
cancels $\bar w X$; subtracting the completed sum gives the zeros
a plus sign. Adding back squares weighted by $w(g^2)$ uses the
fixed-class prime number theorem against $h(2\log u)$ on $[1,2]$,
whose integral is $K(1/2)/2$. Higher powers cost
$O_q(X^{1/3}\log^2(2X))$. Thus, with $m_\chi(z)$ the named order,
$$H(X)=\sum_z c(z)X^z+C\sqrt X+o_q(\sqrt X),\qquad
c(z)=K(z)\sum_\chi b_\chi m_\chi(z),\qquad
C=\frac{K(1/2)}{2d}\sum_g w(g^2).$$
The $O_q(\log(2+|t|))$ unit-height zero count and quadratic decay
give $\sum_z|c(z)|(1+|z|)^v<\infty$ for $0\le v<1$. Real weights
and conjugation of the primitive functions give
$c(\bar z)=\overline{c(z)}$ after grouping.

For nonprincipal $\chi$ the baseline vanishes, so
$$b_\chi=-\frac rd\left(\frac12+
 \sum_j\frac{\alpha^{j+1}}{8d}\overline{\chi(g_j)}\right).$$
The sum inside the parentheses after $1/2$ has modulus less than
$1/4$, hence $\Re b_\chi<-r/(4d)$. The principal coefficient is
$\bar w>0$. At any real zero $1/2<z<1$ the principal order is
zero (the alternating eta series is positive there). There is
at least one nonprincipal order, the grouped sum is real, and
$K(z)>0$, so $c(z)<0$, even at a shared real zero.

For arbitrary $z$, set $F_j=\sum_\chi\overline{\chi(g_j)}m_\chi(z)$.
The identity $d c(z)/K(z)=\sum_jw_j F_j$ is valid since $K$ is
nonzero throughout the open strip. All $F_j$ lie in
$F=\mathbb Q(\zeta_d)$. Eisenstein at two gives degree $\ell$ over
$\mathbb Q$ for $\alpha$; $\ell$ therefore divides $[F(\alpha):\mathbb Q]$
but not $[F:\mathbb Q]\le d$. The tower law and the polynomial
upper bound give $[F(\alpha):F]=\ell>d$. In particular the
coefficient of $\alpha^{j+1}$ is uniquely defined and equals
$-rF_j/(8d)$, since $r$ is nonzero and rational and neither the
baseline nor the spike enters a positive-power coordinate. Recover
$m_\psi(z)=d^{-1}\sum_j\psi(g_j)F_j$ by orthogonality. This is
injective on differences of order vectors and works for $d=1$:
The coefficient of $\sqrt2$ is then $-r m/8$. In particular no
zero disappears, on or off the line. No positivity assumption on
individual complex residues was needed for decoding.

**Why raw signs suffice for the criterion.** On joint GRH the
margin dominates the good errors eventually. Off joint GRH write
$\theta=\sup_z\Re z>1/2$ by reflection. For $1/2<u<\theta$ there
must be arbitrarily late $Y$ with $H(Y)<-Y^u$. Otherwise take
$H(X)+X^u\ge0$ on $[A,\infty)$, $A\ge2$. Its Mellin transform
with measure $X^{-s-1}dX$ converges for $\Re s>\theta$, and in
$\Re s>u$ continues with simple poles of residue $c(z)$ at every
zero there: The integrated zero terms are $c(z)A^{z-s}/(s-z)$,
normal off the locally finite pole set, and the $O_q(\sqrt X)$
remainder is integrable there. Its real convergence abscissa
cannot be above $u$: If regular there, the Taylor series centered
just to its right reaches left of it; the nonnegative logarithmic
moments and monotone convergence then imply convergence there.
If a pole, its negative residue contradicts nonnegativity from
the right. An abscissa at or below $u$ instead gives holomorphy
at a visible pole with $\Re z>u$. No top zero was assumed.

Fix $1/2<b<\theta$ and a proposed count saving $k>0$. Choose
$0<e<\epsilon<\min(k,\kappa,1/20)$ and
$\max(b,\theta-e/(2D))<u<\theta$. At a late peak take $P(T)=Y$
on the increasing branch. For $x\in[T,T+T^{1-e}]$ the log ratio
$t=\log(P(x)/Y)$ is $O(T^{-e})$. The bound
$|e^{tz}-1|\ll\min(1,t|z|)\ll(t|z|)^{1/2}$ for $0\le t\le1$
and the half-moment give variation of $H$ at most
$O(Y^{\theta-e/(2D)}+\sqrt Y)=o(Y^u)$. Thus all those operator
values are below $-P(x)^b$, a magnitude larger than good errors.
For prime mass the all-interval count corollary of
[Guth and Maynard](https://arxiv.org/abs/2405.20552) gives
$\gg x^{9/10}/\log x$ primes in $(x,x+x^{9/10}]$ for all large
$x$ (use $17/30+1/10<9/10<0.99$). Packing such intervals leaves
$O(T^{9/10})$ uncovered, so there are $\gg T^{1-e}/\log T$
consecutive primes with negative operator values. Even if the
excursion meets two power-of-two blocks, the larger piece by
count has $\gg T^{1-e}/\log T>N^{1-\epsilon}$ primes with
$N\asymp T$. Subtract the whole $O(N^{1-\kappa})$ bad budget;
the remaining count divided by $N^{1-k}$ is unbounded. Conversely
on joint GRH only the bad entries could report negative on the
late tail. This conclusion counts raw reported negatives, not a
consecutive run of corrupted signs or a test requiring magnitudes.

**Why the same values identify the divisors.** Take dyadic blocks
on the increasing tail of $P$ and split each $[M,2M)$ into
$\lfloor M^e\rfloor$ equal cells, now $e=\min(\kappa/2,1/20)$.
The same packing gives $\gg M^{1-e}/\log M$ primes per cell,
uniformly, more than twice the whole block budget eventually.
Hence a strict majority of nonerasures is good in every late cell.
Start at $a=1$. Given the already determined terms with $\Re z>a$,
subtract their sum at **each nonerased argument** $P(p)$ before
taking the lower median. These sums are real by conjugation and
absolutely convergent. Let $m_a(X)$ be this median on the image
cell (zero for an empty cell). Put $S_a=\sum_{\Re z\le a}c(z)X^z$,
$h_0=e/(2D)$. The log-width there is $O(M^{-e})=O(X^{-e/D})$.
The half-moment bounds the variation of $S_a$ by $O(X^{a-h_0})$,
and the known square term varies by $o(\sqrt X)$. Comparing every
good residual to the same $X$ and using the majority therefore gives
$$m_a(X)=S_a(X)+C\sqrt X+O(X^{a-h_0})+o(\sqrt X).$$

On $\Re s>a$ the Mellin germ of this data function equals the
integrated pole sum of $S_a$ from the initial image endpoint $A$
plus the transform of $m_a-S_a$. The latter is holomorphic on
$\Re s>b=\max(1/2,a-h_0)$; a bounded prefix adds an entire term.
Normal convergence off the poles and noncancellation identify every
$z,c(z)$ in $b<\Re z\le a$ by uniqueness of continuation. Reset
$a=b$ and recompute the samplewise residual medians, including an
intermediate cut in the next strip. After at most $\lceil D/e\rceil$
strips, $a=1/2$. Now $m_a/\sqrt X-C$ is the line series plus $o(1)$:
The left terms vanish by domination by $|c(z)|$. Its mean against
$X^{-it}dX/(X\log(R/A))$ from $A$ to $R$ tends to $c(1/2+it)$,
zero if absent. Each unmatched exponential has vanishing mean and
all means have modulus at most one. This also reads $t=0$ because
$C$ was subtracted. Decode the resulting residues by the coordinates
above; the functional equation and conjugation preserve the named
order at $1-\bar z$, filling the left half. No old observable is
reconstructed. This proves compatibility for the stated tail model,
not finite-work recovery, stability, or joint GRH.
