---
evidence_revision: 068a54ef817f1d9b6a9ce77a4a0f73db4bf7456a
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
