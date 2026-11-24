---
evidence_revision: 1730648dc8b4e56903937bcef70dfa857183cec2
---

# One explicit baseline with variable spline order

Fix $M=10^{15}$, $a=\log 2$, and an integer $q\ge2$. For
each integer $m\ge8$, let $h_m=\mathbf 1_{[0,a]}^{*m}$,
$k_m=4h_m^{(4)}-5h_m''+h_m$, and $t_p=\log(p/X)$, with
ordinary log derivatives. For every real $X>0$ let

$$W_{q,m}(X)=\sum_{p\nmid q}(\log p)
  [Mh_m(t_p)+\mathbf1_{p\equiv1\bmod q}k_m(t_p)].$$

**Proposition to test:** For every fixed $q\ge2$, joint
GRH for the primitive functions inducing the characters
modulo $q$, including zeta, is equivalent to existence of
one integer $m\ge8$ and real $A\ge1$ such that $W_{q,m}/X$
is nondecreasing on the entire real interval $[A,\infty)$.
For all the specified orders the two windows $Mh_m$ and
$Mh_m+k_m$ should be nonnegative everywhere and the
unconditional mean should be $M$. Seek strictly positive
forward derivative on the tail. The same formula applies
at $q=2$; order and onset may depend on $q$.

**Source and payoff:** This is an operator proposal, not
the [order-six criterion](../closed/fixed-modulus-neutral-order-six-prime-density.md)
at the evidence pin, which fixes the order and enlarges
the baseline depending on $q$. Inputs are the
[quartic derivative margin](../closed/zeta-prime-only-continuous-density.md)
at `a08d9dfe9adc87383319f9e970b60bd443cfcca2` and the
[unconditional low-zero certificate](../closed/zeta-prime-only-doubling-density.md)
at `d5301e8af8a5b4a76db76248f3264d9c9b5a394c`.
The payoff is to replace the modulus-dependent baseline
with this one explicit integer, not to prove joint GRH
or obtain a modulus-uniform order or onset.

**Discriminating test:** Bound the interior and end
pieces of the order-eight windows and propagate by
positive convolution. Apply the derivative formula to
$g_m=-k_m'-k_m$, with multiplier $(s-1)Q(s)\Phi(s)^m$,
$Q(s)=(4s^2-1)(s^2-1)$ and $\Phi(s)=\int_0^a e^{st}dt$.
Check exact central-zero cancellation and evaluate squares
using PNT on precisely the reduced classes with $b^2=1$.
Test summable domination of noncentral zeros by the
order-eight bound: First choose $m$ at fixed $q$, then
absorb the fixed-order errors as $X$ grows, comparing with
the transported quartic margin. In the converse, check
pole cancellation at one, noncancellation at coincident
zeta zeros using the unconditional certificate, negative
real residues, and the nonnegative-tail abscissa argument.
