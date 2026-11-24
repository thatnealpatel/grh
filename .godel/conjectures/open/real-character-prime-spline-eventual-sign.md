---
evidence_revision: 78373235736b7eb16ce70384763b67bdce8cc9d8
---

# Eventual local prime spline signs for fixed real characters

Fix any primitive nonprincipal real Dirichlet character
$\chi$ with $L(u,\chi)\ne 0$ for every real $1/2<u\le 1$.
Set $h=\mathbf{1}_{[0,\log 2]}$ and $h_m=h^{*m}$ using
ordinary convolution on $\mathbb R$, for integers $m\ge2$.
For real $X\ge1$ let

$$W_m(X)=\sum_p\chi(p)\log p\,h_m(\log(p/X)).$$

**Proposition to test:** Every nontrivial zero of
$L(s,\chi)$ has real part $1/2$ if and only if there exist
an integer $m\ge2$ and a real $X_0\ge1$ such that
$W_m(X)\le0$ for every real $X\ge X_0$. The order may
depend on $\chi$, not on $X$. The weight uses only genuine
primes in the fixed-ratio interval $[X,2^mX]$ once $m$
is chosen. No uniform or effective choice is requested.

**Source and payoff:** The pinned [mod-four tent proof](../closed/mod-four-prime-tent-eventual-sign.md)
uses a two-box convolution of width $\log 4$ and a
conductor-specific absolute residue budget. Bob's
[endpoint equation (1)](../../bob/fixed-strip-endpoints.md#the-product-mean-at-the-original-endpoint-weight)
at `bbca37033019090f6f40e6223b5054d382c9d789` uses the
unnormalized log ramp, before division by the cutoff, at
$v=0$ for an individual real quadratic character. Neither
landing asserts this extension. It asks whether increased
smoothing order replaces the small residue budget while
retaining a fixed-ratio comparison of actual primes.

**Discriminating test:** Derive the multiplier $K(s)^m$,
where $K(s)=(2^s-1)/s$, and an explicit formula with a
uniform-in-$X$ remainder for each fixed $m$, including
both parities, trivial zeros, and boundary terms. Remove
prime powers, checking the sign and normalization of the
square term and the exclusions at primes dividing the
conductor. On the critical-line hypothesis test strict
contraction of $|K(1/2+it)|/K(1/2)$ for every $t\ne0$
and summable domination over zeros as $m$ grows. Keep any
central zero with its multiplicity and actual sign. In
the converse for a single order, transform the eventual
nonnegative tail of $-W_m$, isolate entire endpoint
terms, and check real regularity and noncancellation of
zero poles before applying Landau and reflection. Test
precisely where real-axis nonvanishing is needed.
