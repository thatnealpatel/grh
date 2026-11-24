---
evidence_revision: 068a54ef817f1d9b6a9ce77a4a0f73db4bf7456a
outcome: established
---

# Test the prime-index violation phase diagram

**Hypotheses and proposition:** Fix an integer $q\ge2$ and
a real polynomial $P$ of degree $d\ge1$ with positive
leading coefficient. Use natural logs and put
$h=\mathbf1_{[0,\log 2]}*\mathbf1_{[0,\log 2]}$ and
$\delta_q=1/(\sqrt2\,10^6\lceil\log(2q)\rceil)$. Use the
unchanged deficit
$$H_q(X)=(1-\delta_q/\varphi(q))X-\sum_{\ell\nmid q}
(\log\ell)(1-\delta_q\mathbf1_{\ell\equiv1\bmod q})
h(\log(\ell/X)),$$
where $\ell$ runs over primes. Let $\theta$ be the supremum
of the real parts of all nontrivial zeros of the primitive
inducers modulo $q$, including zeta. For $1/2\le b<1$ and
integers $N\ge2$, let $V_b(N)$ count primes $p\in[N,2N)$
with $P(p)\ge2$ and $H_q(P(p))<-P(p)^b$.

* If $b>\theta$, then $V_b(N)=0$ eventually. If $b<\theta$,
  then for each $\epsilon>0$ there are arbitrarily large
  $N$ with a run of at least $N^{1-\epsilon}$ consecutive
  primes in $[N,2N)$, every one counted by $V_b$.
* Consequently $L_b=\limsup_{N\to\infty}\log(1+V_b(N))/
  \log N$ is one below $\theta$ and zero above it, and
  $\theta=\sup(\{1/2\}\cup\{b\in[1/2,1):L_b=1\})$.
  No general assertion is made at $b=\theta$, and no
  attainment or strict upper bound $\theta<1$ is assumed.
* Joint GRH holds if and only if the number of raw negative
  signs on the eligible primes is $O(N^{1-k})$ for some
  fixed $k>0$. On joint GRH there are no true violations.
  The equivalence persists for the reported negative count
  after arbitrary erasures or corruptions of at most
  $O(N^{1-k_0})$ eligible signs per block for any fixed
  $k_0>0$, with erased signs omitted. There is no claim of
  a surviving consecutive run after corruption.

**Source and payoff:** The [onset-two landing](../closed/order-two-discounted-onset-two.md)
at the evidence revision provides the fixed discount and
joint-GRH margin on every real $X\ge2$. Its consumer is the
forward all-$n^B$ sign implication. The [triangle expansion](../closed/order-two-log-discount-sampled-sign.md)
at `69d5d30993da9b1de65d9d7930f06a86664cfa0b`, lines
153–167, supplies the unconditional grouped coefficients,
negative real residues, and sub-first moments.
The [older excess criterion](../closed/fixed-baseline-sampled-positive-excess.md)
at `8e0f45864088cc246d66567c2b83ccb84f553fd0` uses a
different, higher-order differentiable window on all
$n^B$. The current claim is a proposed use, not an
assertion of those landings. It would recover the zero
supremum and tolerate power-saving sign losses from
prime-only samples, without a prime-sample Mellin series,
a density claim, or a finite certification of GRH.

**Discriminating test:** For $1/2<u<\theta$, test the
nonnegative-tail Mellin obstruction for $H_q(X)+X^u$:
Verify normal convergence, visibility, and the sign of
any real abscissa pole, including when $\theta$ is not
attained. For $u=\theta-\eta>b$, test propagation of the
negative peaks using the half-moment of the zero sum and
the separate size bound on the remainder. Invert $P$ on
its large increasing branch, fit a right interval of
length $T^{1-e}$ inside both the excursion and the
integer dyadic block, and count consecutive sample primes
using the unconditional short-interval PNT for one
fixed exponent. Check exponent slack against $\epsilon$,
dyadic rounding, the strict upper phase, and survival
against the power-saving error budget.

## Proof

**Obtain late peaks on the continuous axis.** Write
$D=\varphi(q)$. The pinned unconditional expansion is
$$
H_q(X)=\sum_z c_zX^z+R_q(X),\qquad R_q(X)=O_q(\sqrt X),
$$
where equal zeros are grouped. The coefficients are
$K(z)(m_\zeta(z)-\delta_q S(z)/D)$ with $S(z)$ the total
family order. They are nonzero: $K(z)=((2^z-1)/z)^2$ does
not vanish in the strip, and $D m_\zeta(z)/S(z)$ is
rational whereas the exact discount is irrational. At a
real zero above $1/2$, zeta has no zero, so $c_z<0$.
The moment of order zero and $\theta\ge1/2$ give
$H_q(X)=O_q(X^\theta)$.

Fix $1/2<u<\theta$. If there were no arbitrarily late
$Y$ with $H_q(Y)<-Y^u$, then $g(X)=H_q(X)+X^u$ would
be nonnegative on some $[A,\infty)$ with $A\ge2$.
For $\Re s>\theta$ its Mellin integral is
$$
\int_A^\infty g(X)X^{-s-1}\,dX
=\sum_z\frac{c_z A^{z-s}}{s-z}+\frac{A^{u-s}}{s-u}
 +\int_A^\infty R_q(X)X^{-s-1}\,dX.
$$
Absolute summability justifies integration. The last
integral is holomorphic for $\Re s>1/2$. On compact
sets avoiding the locally finite set of zeros, the
numerators divided by $c_z$ are bounded and the
denominators bounded away from zero. Thus in $\Re s>u$
the continuation has a simple pole of residue $c_z$ at
every zero there.

The nonnegative integral converges on a right half-plane
with abscissa $\alpha\le\theta$. If $\alpha>u$, its
continuation cannot have a pole at real $\alpha$: A
negative residue would make the integral negative just
to its right. Nor can it be regular there. In that case
choose a real center $r>\alpha$ so close that its Taylor
disk reaches a real $v<\alpha$. The coefficients in
powers of $r-s$ are the integrals against
$g(X)X^{-r-1}\,dX$ of $(\log X)^j/j!$, by convergence
a little to the left of $r$. They are nonnegative, and
summing at $v$ by monotone convergence gives a finite
integral at $v$, contradicting its abscissa. Therefore
$\alpha\le u$ (possibly $-\infty$). The integral is then
holomorphic throughout $\Re s>u$, impossible since at
least one zero lies there. This proves the peak claim
without a zero at $\theta$.

**Keep a whole prime interval below threshold.** Take
$\lambda=9/10$. For $b<\theta$ and $\epsilon>0$ set
$$
e=\tfrac12\min(\epsilon,1-\lambda),\qquad
\eta=\min\big((\theta-b)/2,e/(4d)\big),\qquad
u=\theta-\eta.
$$
In particular $u>b\ge1/2$. For $0\le t\le1$ the bounds
$|e^{tz}-1|\le 1+\exp(1)$ and
$|e^{tz}-1|\le \exp(1)t|z|$ give, by taking their
geometric mean, a bound $O(t^{1/2}(1+|z|)^{1/2})$.
The half-moment from the pin therefore gives
$$
|H_q(Ye^t)-H_q(Y)|\ll_q Y^\theta t^{1/2}+\sqrt Y.
$$
Here the two remainder values were bounded separately.

At each sufficiently late peak $Y$ take $T$ on the large
increasing branch of $P$ with $P(T)=Y\asymp_P T^d$.
For $T\le x\le T+T^{1-e}$ the bound $P'=O_P(T^{d-1})$
gives $0\le t=\log(P(x)/Y)\ll_P T^{-e}\ll_P Y^{-e/d}$.
The propagated error is thus
$O_{q,P}(Y^{\theta-e/(2d)}+Y^{1/2})=o(Y^u)$: The first
exponent is at most $u-\eta$. Consequently throughout
this interval $H_q(P(x))<-Y^u/2<-P(x)^b$, since
$P(x)/Y\to1$ uniformly and $u>b$. All images exceed
$2$ at sufficiently late peaks. With $N=\lfloor T\rfloor$
the interval lies in $[N,2N)$ since $T^{1-e}=o(T)$.

Use the unconditional short-interval prime number theorem
in the Huxley range, only at the fixed exponent
$\lambda=9/10>7/12$: For all sufficiently large real
$x$, $(x,x+x^\lambda]$ contains at least
$x^\lambda/(2\log x)$ primes. This is the prime-mass
consequence of the classical density estimate, not an
inference from a prime-gap bound. Reference: M. N. Huxley,
[On the Difference between Consecutive Primes](https://doi.org/10.1007/BF01418933),
*Inventiones Mathematicae* **15** (1972), 164–170,
especially the density estimate on p. 164.

Starting at $T$, pack adjacent such half-open intervals
inside $(T,T+T^{1-e}]$ until the next does not fit. All
starts are between $T$ and $2T$, so the uncovered tail
is at most $(2T)^\lambda=o(T^{1-e})$. Summing the lower
bounds gives $\gg T^{1-e}/\log(2T)$ primes. This exceeds
$N^{1-\epsilon}$ eventually since $N\sim T$ and
$e<\epsilon$. Every prime in the entire interval is
counted, so these give a consecutive run in prime order.
The peaks give unbounded $N$.

**Read off the two criteria.** Above $\theta$ the bound
$O_q(X^\theta)=o(X^b)$ rules out every sufficiently late
violation. Below $\theta$ the run bound for every
$\epsilon>0$, together with $V_b(N)\le N$, gives $L_b=1$.
These strict phases imply the stated supremum formula:
The base point covers $\theta=1/2$, and thresholds can
approach $\theta>1/2$ from below even when $\theta=1$.
Nothing requires deciding the equality case.

On joint GRH the pinned margin $H_q(X)\ge\sqrt X/25$
excludes every raw negative at eligible primes. Otherwise
family reflection gives $\theta>1/2$, and the clean run
at $b=1/2$ consists of raw negatives. Changing or erasing
one eligible sign changes their count by at most one.
Thus on joint GRH the reported count is $O(N^{1-k_0})$.
Off joint GRH, for any proposed $k>0$ choose
$0<\epsilon<\min(k,k_0)$. The reported count on the
constructed blocks is at least
$N^{1-\epsilon}-O(N^{1-k_0})$, whose ratio to $N^{1-k}$
is unbounded. This preserves the count criterion, not a
consecutive run after errors. The supremum uses threshold
comparisons, not raw signs alone.
