---
evidence_revision: 022676f32fb32118354a025cb57b7c48d5dac9cf
outcome: parked
---

# Mean-square cancellation on the Möbius transition interval

For integers $X\ge1$, take $a_n=\mu(n)$ through $X$, constants $\lambda_X,\nu_X$ on $(X,2X],(2X,3X]$ respectively, and zero thereafter. Choose the constants so that $\sum a_n/n=0$ and $\sum a_n=-2$. For $R_X(k)=1-\sum a_n\lfloor k/n\rfloor$, the claim is that for every $\varepsilon>0$,
$$\sum_{X<k\le X^{3/2}} |R_X(k)|^2/k^2\ll_\varepsilon X^\varepsilon.$$

**Parked:** The first correction block alone requires cancellation strong enough to imply rational RH. Reopen with a new bound on that block, not a better estimate beyond $X^{3/2}$.

In the isolated output `02e8bde4a6978bfa774b60389d6d8da9e9463080`, the reported Lean build checked `oneSidedFloorResidual_eq_zero` through $X$ and `oneSidedFloorResidual_firstBlock`: For $X<k\le2X$, the residual is $M(k)-M(X)-\lambda_X(k-X)$, where $M$ sums the Möbius function. Neither theorem is a cancellation estimate. Overlapping affine fits would bound $M(4t)-3M(2t)+2M(t)$ at square-root scale up to $t^\varepsilon$; its Mellin transform has denominator $s\zeta(s)$ and numerator $(2^s-1)(2^s-2)$, nonzero in $1/2<\Re s<1$. This implication and the large-sieve tail estimate were paper arguments, not Lean results. No proof or disproof of the displayed bound was found.
