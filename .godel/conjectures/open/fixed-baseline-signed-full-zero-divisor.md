---
evidence_revision: 645200463f434bd285a45f71442650202427aa5b
---

# Recover the noncentral zero divisor from signed samples

**Proposition to test:** For every fixed choice of integers $q\ge2$,
$m\ge8$, and $B\ge1$, the constants $q,m,B$ and the exact sequence
$H(n^B)$ for integers $n\ge1$ determine all distinct nontrivial zeros
$\rho\ne1/2$ of the primitive inducers of characters modulo $q$,
including zeta. Recover $m_\zeta(\rho)$ and the total multiplicity
$S(\rho)=\sum_{\chi\bmod q}m_{\chi^*}(\rho)$, not individual
characters or nonprincipal central multiplicities. Use at most
$\lceil B/2\rceil$ successive meromorphic strip continuations and
one critical-line logarithmic averaging step, without a line,
spacing, or rightmost-zero attainment hypothesis. This is exact
analytic determination, not a finite-data or stable algorithm.

**Source and payoff:** Put $M=10^{15}$, $h_m=\mathbf1_{[0,\log 2]}^{*m}$,
$k_m=4h_m^{(4)}-5h_m''+h_m$, and $v_p=\log(p/X)$. Use
$$H(X)=MX-\sum_{p\nmid q}(\log p)
  [Mh_m(v_p)+\mathbf1_{p\equiv1\bmod q}k_m(v_p)].$$
The [edge card](../closed/fixed-baseline-signed-edge-ordinates.md)
at the evidence revision supplies the full signed expansion, square
bias, visibility of grouped coefficients, and edge harmonic selector.
The [window card](../closed/fixed-baseline-variable-order-prime-density.md)
at `f5fbeb09e9b972565848e25ac295f3341a537afd` supplies the windows
and the continuous-deficit residues. The extension would recover
interior divisors even when no zero lies at the supremum, which
neither the unsigned envelope nor the edge selector alone does.

**Discriminating test:** With $a=1$ initially, let $r_n$ be the
samples minus all terms $c(\rho)n^{B\rho}$ already recovered to
the right of $a$. For $b=\max(1/2,a-1/B)$, form
$$D_a(s)=B\sum_{n\ge1}r_n n^{-1-Bs},\qquad \Re s>a.$$
Test that it continues to $\Re s>b$ with precisely the remaining
zero poles in $b<\Re s\le a$, and residue $c(\rho)$ at each.
Use the unit-cell sum-minus-integral for each power: Check its
holomorphic extension and uniform height bound on compacts, the
first absolute coefficient moment at $m=8$, and normal convergence
of the pole sum off its locally finite pole set. Check visibility
and separation of the two multiplicities even on $\Im Q=0$ and
at real zeros, with $Q(s)=(4s^2-1)(s^2-1)$. Check that uniqueness
of the continuation and absolute convergence of the next
subtraction avoid any input of zero locations. Iterate with
$a=b$, including upper boundaries and deferring the lower ones;
check $B=1$ and odd $B$. At $a=1/2$, test domination for the
strictly left terms without a gap, and harmonic selection on
$n^B$ with the correct square bias. Check that reflection
preserves the two multiplicities. Only the residual in each
round is asserted to continue across that round's strip.
