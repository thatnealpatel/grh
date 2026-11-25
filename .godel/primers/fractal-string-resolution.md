# Fractal strings: Where count error occurs matters

**Claim.** A bound on fundamental count error propagates to rounded note counts through
harmonic thresholds. For the reverse problem, calibrating an initial portion of the
entire note trace changes how many thresholds can amplify report error. These are
different statements with different hypotheses.

**Checked calculation.** For $T>0$, $x\ge0$, and $t>T$, the floor $\lfloor x/t\rfloor$
counts the intervals $(T,x/n]$ containing $t$, for $1\le n\le\lfloor x/T\rfloor$. In
particular, an atom at $x/n>T$ is counted and one at $T$ is not. For positive Stieltjes
measures with cumulatives $G,F$ and $E=G-F$, the difference of the two floor integrals
over $(T,\infty)$ is
$$
\sum_{1\le n\le\lfloor x/T\rfloor}\big(E(x/n)-E(T)\big).
$$
If $|E(t)|\le1$ for all $t\ge T$, the absolute difference is at most
$2\lfloor x/T\rfloor$. A threshold equal to $T$ contributes zero, and the sum is empty
if $x<T$.

**Exact suffix minimax on paper.** Fix $0<D<1$. Allow repeated fundamentals $f_j>0$,
with $\sum_j f_j^{-1}=1$ and $G(t)=\#\{j:f_j\le t\}\le10t^D$. The report $Y$ is the
entire cumulative note trace of another such string through $x$, at exact frequencies.
It equals the true $N(t)=\sum_j\lfloor t/f_j\rfloor$ for $0<t<x/H$, and
$|Y(t)-N(t)|\le q$ on $[x/H,x]$, **including tolerance at $x/H$**. For all sufficiently
large $x$ depending only on $D$, uniformly for integers $q,H\ge1$ with $qH^2\le x^D$,
the minimax absolute error for estimating $G(x)/x^D$ is
$$
\frac{q}{x^D}\sum_{n\le H}|\mu(n)|,
$$
where $\mu$ is the Möbius function. Since $f_j\ge1$, $N(t)=\sum_{m\le t}G(t/m)$; divisor
cancellation gives $G(x)=\sum_{n\le x}\mu(n)N(x/n)$. Substituting $Y$ incurs errors only
at $n\le H$, giving the upper bound.

For the lower bound, choose $\eta>0$ so that the pulses $[x/n,x/n+\eta)$ for
$1\le n\le H$ are disjoint. Prescribe the signed note gap and invert it into a signed
fundamental staircase:
$$
h(t)=2q\sum_{n\le H}\mu(n)\mathbf1_{[x/n,x/n+\eta)}(t),\qquad
B(t)=\sum_{k\le H}\mu(k)h(t/k).
$$
For $t\le x$ the harmonic sum of $B$ is $h$: Terms with product $mk>H$ see nothing, and
the remaining coefficients are divisor sums of $\mu$. The left endpoints are included,
so $B(x)=2q\sum_{k\le H}|\mu(k)|$. Place the positive and negative jumps of the
individual dilated pulses into two strings, keeping both endpoints, including those
past $x$. The multiplicities are even, so taking half of each multiset gives a physical
midpoint report. Each unsigned count, including the midpoint, is at most
$2qH^2\min(1,t/x)\le 2t^D$: A pair $(k,n)$ can contribute only when $kx/n\le t$. All
three counts vanish below $x/H$, so integrating against $dt/t^2$ gives lengths
$O_D((x/H)^{D-1})=o(1)$ uniformly since $H\le x^{D/2}$.

Shrink $\eta$ until the two lengths differ by less than $1/(4x)$, since the paired
reciprocal endpoints coalesce. Add one length in $[1/(4x),1/(2x)]$ to each to equalize
them, and the mean of those added lengths to the midpoint. These additions are invisible
through $x$. Append to all three the same tail of lengths $2^{-j/D}/16$ for $j\ge1$, and
a common positive filler to reach length one. The tail contributes at most $t^D$
fundamentals and the two added components at most two; hence the completed strings
satisfy the growth cap. The same report is now within $q$ notes of both truths on the
entire suffix and exact below it. Half their target separation forces the stated error
for any estimator.

**What it does not show.** No zero is used, and the minimax proof is not checked in
Lean. It does not cover errors on the whole prefix, other observation models, or
establish a sharp transition at $qH^2=x^D$. Any fixed pair with distinct fundamental
counts has some finite note-count disagreement by inversion. Once the calibration
interval contains that disagreement, the pair cannot share a report, regardless of $q$;
the sharpness construction instead varies with $x$. For example, at $D=1/2$,
$q\asymp x^{1/3}$ and $H=\lfloor x^{1/4}/\sqrt q\rfloor$ give loss $\asymp x^{-1/12}$ by
squarefree density. To extend the result past the stated budget, the next test is
whether a physical common report can still realize the adverse harmonic signs under the
growth cap.

**Source.**
[`FractalStringRounding.lean`](../../Proofs/Lemmas/FractalStringRounding.lean) checks
`FractalStringRounding.floor_div_eq_sum_indicator`,
`FractalStringRounding.stieltjes_tail_sub_eq_sum`, and
`FractalStringRounding.abs_stieltjes_tail_sub_le`. The suffix construction above is a
separate inverse problem.
