---
evidence_revision: 9328b646effbe6e2cc0559c62e40521bab600b48
---

# The fixed order-three ordinary RH prime comparison

Put $a=\log 2$ and $h_3=\mathbf{1}_{[0,a]}^{*3}$, with
convolution in the log variable and support $[0,3a]$.
For real $X>0$, sum over all rational primes and set

$$B_3(X)=\sum_p(\log p)h_3(\log(p/X))-X,\qquad
S_3(X)=\sum_p(\log p)h_3(\log(p^2/X)).$$

**Proposition to test:** Ordinary RH is equivalent to the
existence of a real $A\ge1$ such that for every real $X\ge A$,

$$\sqrt2 B_3(X)-B_3(2X)\le S_3(X).$$

**Source and payoff:** This is an operator strengthening of
the linear case of the [Dedekind prime root comparison](../closed/dedekind-prime-root-critical-dilation.md)
at `e29848af48be97061090219fcb2ea99e27079367`, which permits
a choice of order in the forward implication. The pinned
[signed order-two obstruction](zeta-order-two-prime-comparison.md)
concerns only order two. Order three would identify the
least working order under RH, with the same centering and
square allowance, without deciding the literal order-two
biconditional.

**Discriminating test:** On RH let $D(s)=\sqrt2-2^s$,
$\Phi(s)=(2^s-1)/s$, and $k=\Phi(1/2)$. Verify the
completed-zeta product identity for $C=\sum_\rho|\rho|^{-2}$
with multiplicities on RH. Drop any central term in the
dilated zero sum and use nonreal conjugate pairs to test
whether $2\sqrt2((\sqrt2+1)/k)^3 C\sqrt{C/2}<1/2$, with
rigorous constants independent of a zero table. A strict
margin would suffice by the linear-case asymptotic. Verify
that the fixed-order converse applies at $m=3$, checking the
centering, undilated allowance, and Mellin tail endpoints.
