---
evidence_revision: e29848af48be97061090219fcb2ea99e27079367
---

# The fixed order-two ordinary RH prime comparison

Let $h_2(t)=\max(0,\log 2-|t-\log 2|)$, and let the sums
run over all rational primes. For real $X>0$ set

$$B_2(X)=\sum_p (\log p)h_2(\log(p/X))-X,\qquad
S_2(X)=\sum_p (\log p)h_2(\log(p^2/X)).$$

**Proposition to test:** RH for ordinary zeta holds if and
only if there exists a real $A\ge1$ such that, for every
real $X\ge A$,

$$\sqrt2 B_2(X)-B_2(2X)\le S_2(X).$$

**Source and payoff:** This is an operator sharpening of the
linear case of the [Dedekind root-count comparison](../closed/dedekind-prime-root-critical-dilation.md)
at the evidence revision. The landing allows a choice of
order $m\ge2$ in its forward proof. Its fixed-order converse
already applies at $m=2$. A forward proof at order two would
give the exact log-tent criterion, with unchanged centering
and square allowance.

**Discriminating test:** Under RH, write $D(s)=\sqrt2-2^s$,
$\Phi(s)=(2^s-1)/s$, and $k=\Phi(1/2)$. Compare the
absolute zero sum $\sum_\rho |D(\rho)\Phi(\rho)^2|$, with
both signs and multiplicities, against $k^2/2$. First try
the bound $|D|\le2\sqrt2$ with the exact weighted sum of
$|2^\rho-1|^2/|\rho|^2$. If needed, use a trigonometric
majorant and explicit-formula cosine sums, or certified
low-zero savings from the exact inverse-square total. A
strict margin suffices by the landing's asymptotic; failure
of a sufficient bound does not refute the proposition.
