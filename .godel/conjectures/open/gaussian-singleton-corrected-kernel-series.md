---
evidence_revision: fd9b420ec415046d03028c1929d0b349ac0f7426
---

# Does the corrected Gaussian singleton kernel series give the actual operator?

Work on the weight-four Gaussian block of $G=C_{\mathbb Q(i)}$ at $a=1/2$, $I=\{0\}$, and $s=4$. Write $r=\log|\cdot|_F$, $w=(1+r^2)^2$, and $\mu$ for quotient Haar. Fix $\varphi=b_0(r)\eta$ with the [prescribed positive-log bump](../../../Proofs/Lemmas/PositiveLogBumpDecay.lean) and weight-four angular character; use the surviving input and output block from the [angular calculation](../../obligations/trace-spectral-angular-qi.md). Put $A=A(\varphi)$ and $P=P_a^{\rm spec}$. The target is $PA$, not $AP$.

**Claim to test:** Use the rectangular right-hand side of (10.4.3.14) in [Masullo](../../sources/masullo/README.md), pp. 466–467. This choice matters: A lexicographic prefix in (10.4.3.21) need not be a finite rectangle before restriction to one character. Use the explicit rectangles, without assuming equivalence of the two global limits. On the single surviving character it retains ordinates $t_0,\ldots,t_N$ in nondecreasing absolute height and **all** allowed jets at each retained ordinate. Fix any enumeration allowed there, including its tie order; a prefix can split a pair at equal absolute height. For $0\le m<\min(\operatorname{ord}_{t_j} Z,2)$ let $u_{jm}=S_a\psi_{\chi,t_j,m}$ be the lift of the full quotient biorthogonal vector, and $d_{jm}=A'\eta_{\chi,t_j,m}$ its transposed input density as in (10.4.3.21). The corrected output-first kernels

$$K_N(x,y)=\sum_{j=0}^{N}\sum_m u_{jm}(x)d_{jm}(y)$$

converge in $L^2(w(x)w(y)^{-1}\,d\mu(x)d\mu(y))$ to the Haar-relative kernel of $PA$ on that block. Here one integrates $K_N(x,y)f(y)$ against $d\mu(y)$, with no extra factor of $1/w(y)$. The [singleton tensor audit](../../obligations/trace-spectral-singleton-kernel-qi.md) checks this correction on one term, not the limit.

**Discriminating test:** On the quotient write $B_N v=\sum_{j\le N,m}\ell_{jm}(v)\psi_{\chi,t_j,m}$ for the coordinate truncation, with $\ell_{jm}$ the defining jet functionals. Test whether $\|(I-B_N)\bar A\|_{\rm HS}\to0$ for the induced convolution $\bar A$. Pullback by the quotient map and the isometric lift identify this error with the ambient Hilbert–Schmidt error. In particular, inspect prefixes that split nearby ordinates: The lift norm alone does not decide the smoothed error. The [finite jet trace calculation](../../obligations/trace-spectral-sum-qi.md#finite-jet-matrices-and-trace-norm-limit) uses orthogonal projections onto finite spans, not these coordinate truncations. Trace class of $PA$ and agreement of finite traces do not settle the claim.

A concrete obstruction to look for uses two distinct same-sign ordinates $p,q$ on opposite sides of the prefix, with $p$ retained and $q$ omitted. Write $h$ for the actual convolution multiplier in the log-Fourier coordinate. Test the error on a translate of a fixed smooth frequency bump with value one at $q$; its ambient $H^2$ norm is independent of $q$. Every representative of the output error has value zero at $p$ and $h(q)$ at $q$. Since $\|f'\|_\infty\lesssim\|f\|_{H^2}$, its quotient norm is at least a fixed constant times $|h(q)|/|p-q|$. Thus a sequence of actual straddling pairs on which this ratio stays bounded below would disprove convergence. Neither small gaps alone nor fast decay of $h$ alone decides this test.

Success would repair the kernel representation in the stated square-integrable topology only, not prove the manuscript’s stronger projective-norm convergence or justify a diagonal limit. A counterexample must concern these partial sums for the actual Gaussian data; poor conditioning in a model or another isotype is not one.
