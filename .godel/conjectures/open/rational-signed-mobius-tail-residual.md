---
evidence_revision: 3bb6ee946da123925f643a3f5d31f3a8e6c7e35e
---

# Does the signed rational Möbius-tail trace bound the translated residual at one width?

**Open target:** Over $\mathbb Q$ in the trivial compact isotype, find one admissible $0<\alpha<1/2$ and independently prove
$$
\left|\lim_{I\uparrow\mathbb R}K_{I,L,N(I,L)}+S_\phi(L)\right|\le C_{\alpha,\phi,r}e^{\alpha L}
\qquad(L\ge L_0).
$$
Here the band limit is taken first at each fixed position window $I$. The constant must not depend on $I$, $N$, or $L$ after the limits. This is narrower than the [whole geometric trace comparison](rational-normalized-global-geometric-trace.md): One translated test family and one width, not every test or arbitrarily small widths. For a bump seeing every zero, the [pole-exclusion argument](translated-residual-pole-exclusion.md) would give the corresponding closed zero strip, not RH.

**The two quantities to compare.** Use the weight $w(x)=e^{2\alpha|x|}(1+x^2)^r$, integer $r\ge2$, and choose a good width for the [rational theta closure](../../obligations/trace-theta-density-q.md). In $L^2(w\,dx)$ let $P$ be its orthogonal projector, $J=1-P$, $E=1_I$, and $A_h$ convolution by $h$ against $dx$. Take $\phi=\partial(\partial^2-1/4)\psi$ real and supported in $[-d,d]$, with the dilation fixed to see every nontrivial zero as in the [edge calculation](../../primers/weil-complements.md). The extra derivative kills the mass and loses no ordinary zeta zero. Put $\check\phi(x)=\phi(-x)$, $C=\phi*\check\phi$, $f_L(x)=C(x-L)$, and $S_\phi(L)=\sum_n\Lambda(n)n^{-1/2}C(\log n-L)$. For $L>2d$ the real-place term is $O_\phi(e^{-5L/2})$, since the polar moments vanish. It does not affect the target exponent.

**Fixed-cutoff conjecture (paper argument, not Lean-checked).** Write $\tau_a u(x)=u(x-a)$ and form the genuine theta generator and finite inverse
$$
t(x)=\sum_{m\ge1}m^{-1/2}\phi(x+\log m),\quad R_N=\sum_{n\le N}\mu(n)n^{-1/2}\tau_{-\log n},\quad h=\tau_L[(R_Nt-\phi)*\check\phi].
$$
The divisor identity $\sum_{n\mid k}\mu(n)=1_{k=1}$ puts $\operatorname{supp}h$ in $(-\infty,L+2d-\log N]$. Translates of $t$ lie in the theta closure, so $JA_h=-JA_{f_L}$. For $I=[u,v]$, choose $\log N>L+|I|+2d$ and put $F=1_{(-\infty,v+L+2d-\log N]}$. Then $A_hE=FA_hE$ and $EF=0$. Thus the separated block satisfies
$$
K_{I,L,N}:=\operatorname{Tr}(EPFA_hE)=\operatorname{Tr}(EJA_{f_L}E).
$$
Indeed $EPF=-EJF$. Compact input localization and the two convolution factors make $A_hE$ trace class. The expression on the right is independent of separated $N$. In the [repaired cutoff order](../../obligations/trace-hardy-diagonal-q.md), the finite-band error $\operatorname{Tr}(EA_{f_L}(P-P_Y))$ tends to zero at fixed $I$. The off-diagonal term $\operatorname{Tr}(EPA_{f_L}J)$ then tends to zero in position exhaustion. This gives the displayed target with its **plus** sign; it does not identify $K$ with the unprojected arithmetic diagonal or bound their difference.

**Tail-norm obstruction (paper conjecture):** A visible critical-line zero $1/2+i\gamma$ forces $M_h(i\gamma)=-e^{i\gamma L}M_C(i\gamma)\ne0$, where $M_h(z)=\int h(x)e^{zx}\,dx$. If $T=\log N-2d-L$, Cauchy–Schwarz on $x\le-T$ costs at most $(2\alpha)^{-1/2}e^{-\alpha T}(1+T^2)^{-r/2}$ in the dual norm. For fixed $I$, the identity $\|A_hE\|_{\rm HS}^2=\int |h(s)|^2\int_I w(y+s)/w(y)\,dy\,ds$ bounds the squared norm below by a positive multiple of $\|h\|_{L^2(w\,dx)}^2$ when $|I|>0$. Hence at fixed $L$ and $I$ the unprojected $\|A_hE\|_{\rm HS}\gg_{L,I,\alpha,\phi,r}N^\alpha(\log N)^r$. Moving the tail away does not make it small in norm. This lower bound is **not** a lower bound on the signed residual. At fixed $I$, $N\asymp_I e^L$ already involves $\asymp_I e^L/L$ primes, and taking absolute values in the prime window costs $\asymp_\phi e^{L/2}$ by the prime number theorem.

**Discriminating test:** Use $d=1/32$, $\psi(x)=\exp[-1/(1-(x/d)^2)]$ on $|x|<d$ and zero elsewhere, $I=[-1/8,1/8]$, and $L=\log 5$. For $N=8,16,32$ only $5$ contributes to the arithmetic sample. With $Xt(x)=xt(x)$, the kernel $[R_N(Xt)*\check\phi](-L)$ equals $-C(0)\log(5)/\sqrt5$ by $\sum_{n\mid k}\mu(n)\log n=-\Lambda(k)$ for $k>1$. This exact calibration, checked by quadrature at $N=8$, has **no projection**. For a separate check of $K$, take the orthogonal projection $J_s$ onto the Mellin jet representers of a finite set of interior zeros, using their Gram matrix in the original weight. Compare $-\operatorname{Tr}(EJ_sFA_hE)$ with $\operatorname{Tr}(EJ_sA_{f_L}E)$ at the three cutoffs, first on one conjugate pair, then on two. These expressions must agree; their agreement tests the calculation, not the conjecture. Progress on the growth bound requires control of the signed comparison as $L$ grows, including the section remainder or a direct estimate for the full projector. Neither a finite Gram section nor a finite theta band is the full projection. See the [delayed-shift conjecture](delayed-shift-finite-jet-erasure.md) for a proposed obstruction to recovering the arithmetic sample from finite jets alone on a larger family of shifts.
