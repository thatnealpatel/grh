---
evidence_revision: a684299f2b54e602be826969b35b7c1f30742700
outcome: established
---

# Valuation layers give a trace-class prime-power sum at fixed position cutoff

Let $H_s=L^2(\mathbb R,(1+x^2)^{s/2}dx)$, $s>1$, $L=\log p$, $S_du(x)=u(x+d)$, and $A_f u(x)=\int f(x-y)u(y)\,dy$. For $f\in C_c^\infty((0,\infty))$ and $\rho\in C_c^\infty(\mathbb R)$, the operators $T_N=M_\rho A_f\sum_{k=1}^N S_{kL}$ converge in trace norm to an operator of trace $(\int\rho)\sum_{k\ge1}f(kL)$.

**Established by a paper estimate, not Lean:** Each layer counts the multiples of $p^k$ on the standard unramified lift. Summing the first $N$ layers counts the truncated valuation, not the [Boolean nonunit shell](common-lift-boolean-shell-orbital-comb.md).

Write $w(x)=(1+x^2)^{s/2}$. After conjugating to ordinary $L^2$, the $k$th kernel is $\rho(x)\sqrt{w(x)/w(y)}\,f(x+kL-y)$. On a fixed bounded interval containing the output support, $y=kL+O(1)$ and the supports overlap only boundedly in $k$. The squared $L^2(dx\,dy)$ norms of the tail kernel and its first $x$-derivative are each at most $C\sum_{N<k\le M}(1+kL)^{-s}$. Hence the tail is Hilbert–Schmidt into $H^1$ of that interval. The inclusion from $H^1$ to $L^2$ there is Hilbert–Schmidt too, so the trace norm is bounded by a constant times the square root of the sum. It tends to zero. Integrating each smooth compact kernel on the diagonal gives the claimed trace by continuity.

For $\int\rho=L$ this gives the above-one orbital scalar per period. Widening the window instead multiplies the scalar by its mass. Nothing in this estimate supplies the valuation multiplicities, the half twist, or the one-period normalization from the manuscript's actual indentation; it gives no residual global diagonal.
