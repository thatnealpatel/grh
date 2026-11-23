---
evidence_revision: 5f22f5a60aef2da44527fee5b442065015202396
outcome: established
---

# Uniform unsigned prime-power row bound for the RH error

**Proposition:** Assume RH for the Riemann zeta function.
For real $D>0$, set $X=e^D$ and $E=\sqrt X$. Put
$\psi(t)=\sum_{n\le t}\Lambda(n)$ and
$h(z)=e^{-z/2}|\psi(e^z)-e^z|$ on the whole real line.
On the closed window $[0,D]$ put $r(x)=h(x)+h(D-x)$.
Let $T$ sum both translations by $\pm\log n$, with weight
$\Lambda(n)/\sqrt n$, over all $2\le n<X$, using the zero
extension of the window input. Do absolute $C,D_0$ exist
such that $(Tr)(x)\le CE$ for every $D\ge D_0$ and every
$x\in[0,D]$, including row and sample endpoints?

**Source and payoff:** [A corrected Schur weight under
RH](../../bob/unsigned-edge-rh.md) uses this bound to
absorb the residual for its weight $W$ without changing
the coefficient one on $D$ in $\|T\|\le E+D+O(1)$.

**Discriminating test:** Read the RH estimates and the
short-interval prime bound at source. Derive a one-sided
average for each sign of the error at scale $1/E$ and
check its validity across both window edges and at jumps.
Expand both translations and both reflections with the
actual row masks. For the large samples, bound the
weighted prime-power mass in every inverted sampling
interval, including clipped shells, then sum the shells
and the small-sample remainder. Check that the resulting
constant transfers through the stated $W$ without an
additional multiple of $D$.

**Proof under RH.** Write $\Delta(t)=\psi(t)-t$ and $\tau=1/E$.
[Brent, Platt, and Trudgian](https://arxiv.org/abs/2008.06140),
Theorem 1, gives $\int_Y^{2Y}\Delta(t)^2dt\ll Y^2$; the pointwise
bound $|\Delta(t)|\ll\sqrt t(1+\log^2 t)$ also follows from
[Lee and Nosal](https://arxiv.org/abs/2312.05628), Theorem 1.2.
Both use $n\le t$; bounded initial ranges down to 1 are harmless.
On a positive log-dyadic interval the integral of $h^2$ is the
integral of $\Delta(t)^2/t^2$, hence is $O(1)$. Below zero,
$h(s)=e^{s/2}$. Covering and Cauchy–Schwarz thus give
$\int_J h\ll1$ whenever $|J|\le3$.

At $z\in[0,D]$, if $\Delta(e^z)\ge0$, take $s\in[z,z+\tau]$;
otherwise take $s\in[z-\tau,z]$. Monotonicity in the chosen direction
gives $|\Delta(e^z)|\le |\Delta(e^s)|+|e^s-e^z|$, also at jumps.
After normalization the drift is at most $E(e^\tau-1)=O(1)$ and
the error term at most $e^{\tau/2}h(s)$. Averaging on that side gives
$h(z)\ll1+\tau^{-1}\int_{z-\tau}^{z+\tau}h(s)ds$. This uses the
true $h$ outside the window, not a truncated $\psi$.

For every $2\le n<X$, the positive shift samples $x+\log n$ and
$D-x-\log n$ when $n\le e^{D-x}$; the negative shift samples
$x-\log n$ and $D-x+\log n$ when $n\le e^x$. At either edge
only one pair remains, with arguments $\log n,D-\log n$. Inside,
equality in a row mask retains the sample. Partial summation of
$\psi(t)\ll t$ gives $\sum_{n\le y}\Lambda(n)/\sqrt n\ll\sqrt y$.
Thus $n<X^{2/3}$ costs $O((1+D^2)X^{1/3})=o(E)$ by the pointwise bound.

Fix a remaining dyadic shell $[K,2K)$ and one sample type
$z=a\pm\log n$. At each integration point $s$, the atoms with
$|s-z|\le\tau$ have log-diameter at most $2\tau$, hence diameter
at most $4K\tau$ by the mean-value theorem. If nonempty, enclose
them in $(n_{\min}-1,n_{\min}-1+L]$ with $L=8K/E$.
This padding works even for a singleton: $X^{2/3}/2\le K\le X$,
so $L\gg X^{1/6}$ and $L\le8\sqrt K$. [Yamada](https://arxiv.org/abs/2312.16090),
Theorem 2 with modulus one, bounds the prime count by $O(L/\log L)$;
the sampled primes thus have total weight $\sum\log p\ll L$, since
$\log(2K)/\log L=O(1)$. For fixed $m\ge2$, distinct $m$-th powers
in the shell are separated by at least $mK^{1-1/m}$. All higher
powers together therefore cost $O((1+L/\sqrt K)\log^2(2K))=O(L)$,
counting exponents and weight per atom. Row and shell clipping
can only decrease these masses.

After interchanging sum and integral the normalized mass at $s$
is $O(L/\sqrt K)$. Its support lies in an interval of length at
most $\log2+2\tau$. The integral term costs $O(L/(\tau\sqrt K))$
and the constant term costs $O(\sqrt K)$, both $O(\sqrt K)$.
Summing geometrically to $K\le X$ and over the four types gives
$Tr\le cE$, uniformly as asserted.

**Transfer to the upper bound.** With $f(x)=e^{-x/2}$,
$w=f+f(D-\cdot)$, and $U(s)=\sum_{n\le e^s}\Lambda(n)/n$,
$Tf\le f[U(D-x)+\psi(e^x)]$: Restoring any excluded $n=X$
at an endpoint only increases the sum. Partial summation gives
$U(s)=s+O(1)$ since $\int_1^\infty |\Delta(t)|dt/t^2<\infty$.
Adding the reflection, the two $\psi$ main terms give $Ew$,
their errors are at most $r$, and the $U$ terms are at most
$(D+C_0)w$. The weighted mass bound also gives
$T1\le C_T(e^{x/2}+e^{(D-x)/2})=C_TEw$. Hence
$W=w+(r+c)/E>0$ satisfies

$$
TW\le(E+D+C_0+cC_T)w+r+c\le(E+D+C_1)W
$$

for fixed $C_1\ge\max(0,C_0+cC_T)$. Weighted Schur applies to
the paired translations by symmetry. Thus $\|T\|\le E+D+O(1)$
under RH, with no extra multiple of $D$.
