---
evidence_revision: 1f653917b9a8d55a730e17252832825d03236891
---

# One neutral order-six prime density and fixed-modulus GRH

Fix an integer $q\ge2$ and write $d=\varphi(q)$,
$a=\log 2$, $h=\mathbf 1_{[0,a]}^{*6}$, and $t_p=\log(p/X)$.
Derivatives of $h$ are ordinary derivatives in its log
argument. For an integer $M\ge1$ define
$$W_M(X)=\sum_{p\nmid q}(\log p)
 \left[Mh(t_p)+\mathbf1_{p\equiv1\bmod q}
               (h''(t_p)-h(t_p))\right].$$

**Proposition to test:** All nontrivial zeros of every
primitive Dirichlet $L$-function inducing a character modulo
$q$, including $\zeta$, lie on $\Re s=1/2$ if and only if
some integer $M\ge1$ makes both windows $Mh$ and
$(M-1)h+h''$ nonnegative everywhere and makes $W_M(X)/X$
nondecreasing for all real $X$ on a full tail. Seek strict
positivity of the derivative on the forward tail. The claim
includes $q=2$ and permits $M$ and the tail to depend on $q$.

**Source and payoff:** This is an operator proposal, not a
claim of the [irrational quartic criterion](../closed/fixed-modulus-single-quartic-prime-density.md)
at the evidence revision. The [class derivative estimate](../closed/fixed-modulus-one-extra-vote-prime-density.md)
at `76d66112fa30b3a9cc28d24759ac6f8fe78f9e94` and the
[positive zeta derivative margin](../closed/zeta-prime-only-continuous-density.md)
at `a08d9dfe9adc87383319f9e970b60bd443cfcca2` provide inputs.
The proposed payoff is an integer differential polynomial
in one window, and a single density with limit $M$ without
a residue-class correction. It does not assert a criterion
with two integer multipliers of the same unchanged kernel.

**Discriminating test:** Check the support ends and a finite
bound for the negative part of $h''/h$. Transport the
quartic derivative margin by exact convolution and chain
rule; use the fixed-character contour calculation on the
actual derivative kernel $-(h''-h)'-(h''-h)$ with the pole,
zero sum, and prime powers treated separately. For the
converse, derive the Mellin transform of $MX-W_M$ on the
nonnegative tail, checking the lower endpoint, higher
powers, removed Euler factors, and the residue at one.
Determine whether $(s^2-1)$ prevents cancellation at every
coincident nonreal zero, and whether the sign at a real
zero suffices for the nonnegative-tail abscissa argument.
