# The endpoint list at the limiting strip exponent

Use the notation, hypotheses on the twists, and individual-cutoff endpoint quotient of the [fixed-strip result](fixed-strip-endpoints.md). Assume the primitive nonprincipal quadratic $L$-functions have no zero in $\Re s>\beta_0$, with $1/2\le\beta_0<1$ fixed. Write $\delta=1-\beta_0$. For $1<A<2$ there is a **fixed** $\lambda=\lambda(A,\beta_0)>0$ such that for every fixed $\theta>0$ and all sufficiently large $q$, at most one twist of a real primitive base fails anywhere in the centered band

$$ |y|\le T=\exp(\lambda X^\delta),\qquad X=(A\log q)^2,\quad |d|\le X^\theta. $$

In particular $\delta=1/8$ uses precisely the external theorem identified in the linked note. This is not the substitution $\sigma=\beta_0$ in its bound for $L'/L$: There can be zeros on that line. Cross the zeros and pay for their residues instead. The constant in $\log T$ matters.

## A uniform residue bound on the original weight

For two distinct twists let $\psi$ be their product modulo $m=[|d_i|,|d_j|]\le X^{2\theta}$. Its primitive inducer $\chi$ has conductor $f\mid m$ and is nonprincipal. For a primitive real character the functional equation reflects the nontrivial zeros across the center of the strip, so every such zero $\rho=\beta+i\gamma$ has $\delta\le\beta\le\beta_0$. Count zeros with multiplicity. Uniformly for $U\ge3$ and $v\in\mathbb R$, we claim

$$ \frac1U\left|\sum_{p<U}(\log p)\psi(p)p^{iv}\log(U/p)\right|\le C_{\beta_0}U^{-\delta}\log(2m(2+|v|))+O\left(U^{-1/2}\log^3(2U)+U^{-1}\log m\log U\right). \tag{1} $$

Start with all von Mangoldt coefficients of $\chi$. In their Mellin integral shift $-(L'/L)(s-iv,\chi) U^s/s^2$ from $\Re s=2$ to $\alpha=\delta/2$. Only nontrivial zeros are crossed; neither the kernel pole nor any trivial zero is crossed. The residue sum is

$$ -\sum_\rho\frac{U^{\rho+iv}}{(\rho+iv)^2}. $$

Here are details of the two uniform estimates in this shift. Write $\mathcal L$ for the entire order-one completed primitive $L$-function. Subtract its Hadamard logarithmic derivatives at $2+iu$ and $-1+iu$. The real part of the difference equals $2\Re(\mathcal L'/\mathcal L)(2+iu)$ by the functional equation; the Euler product, conductor factor, and Stirling bound it by $O(\log(2f(2+|u|)))$. In the Hadamard difference the unknown constant cancels, and each zero contributes

$$ \frac{2-\beta}{(2-\beta)^2+(u-\gamma)^2}+\frac{1+\beta}{(1+\beta)^2+(u-\gamma)^2}\gg \frac{1}{1+(u-\gamma)^2}. $$

Thus $\sum_\rho(1+(u-\gamma)^2)^{-1}\ll\log(2f(2+|u|))$, which also bounds the unit-interval count. Take $u=-v$. Since $|\rho+iv|^2\ge\delta^2+(\gamma+v)^2$, the absolute residue sum is $O_{\beta_0}(U^{\beta_0}\log(2f(2+|v|)))$. In particular no separation of $v$ from the zeros, simple-zero assumption, or depletion of zeros near $\beta_0$ is needed.

On the new vertical, the functional equation, the logarithmic Gamma derivative, and the [fixed-margin logarithmic derivative bound](fixed-strip-endpoints.md#the-product-mean-at-the-original-endpoint-weight) at $1-\alpha=\beta_0+\alpha$ give $|(L'/L)(\alpha+iu)|\ll_{\beta_0}\log(2f(2+|u|))$. Stirling suffices at large ordinates, and the Gamma arguments stay away from their poles on this line. The integral thus costs $O_{\beta_0}(U^\alpha\log(2f(2+|v|)))$ before normalization, by integration against $1/(\alpha^2+t^2)$ with $u=t-v$.

For the horizontal contours, on $\alpha\le\Re z\le2$ subtract the Hadamard logarithmic derivative at $2+i\Im z$ from the one at $z$. Roots with $|\gamma-\Im z|>1$ cost $O(\log(2f(2+|\Im z|)))$ in the difference by the unit count and inverse-square decay. After stripping the Gamma factor, $L'/L(z)$ is therefore $\sum_{|\gamma-\Im z|\le1}(z-\rho)^{-1}$ up to the same log bound with an $\alpha$-dependent constant. For each fixed $v$, choose upper and lower heights tending to infinity in absolute value, with shifted ordinate at distance $\gg 1/\log(2f(2+|\Im z|))$ from every zero ordinate. The unit count permits such a point in each far unit interval by deleting small neighborhoods. Then the horizontal cost tends to zero by the kernel's inverse square. The resulting vertical and residue bounds are uniform in $v$.

Removing higher prime powers costs $O(\sqrt U\log^3(2U))$. Erasing primes dividing $m$ to recover $\psi$ costs at most $\log U\sum_{p\mid m}\log p\le\log U\log m$. Dividing by $U$ proves (1).

## Spend a fixed margin, not an $o(1)$ estimate

At $U=X$ and $|v|\le2T$, (1) gives $C_{\beta_0}\lambda+o(1)$ for the normalized product mean, uniformly over the twist pairs. Apply this at **both** $v=y_i+y_j$ and $v=y_i-y_j$. The [real signed-pair inequality](fixed-strip-endpoints.md#signed-pairs-versus-the-gram-bound) then gives $h_i(y_i)+h_j(y_j)\le1+C_{\beta_0}\lambda+o(1)$. Two failures at their respective cutoffs would give at least $2/A-o(1)$. Take $C_{\beta_0}\lambda<2/A-1$. This proves the count; it still permits an exceptional base character. For $\log T=o(X^\delta)$ the errors are $o(1)$ and the original $2-A-o(1)$ margin for the other twists after one failure is retained. At fixed $\lambda>0$ this argument loses $O_{A,\beta_0}(\lambda)$ in that margin.

**Remaining height test.** For $\beta_0=7/8$, start the unresolved one-sided pair test above this small fixed multiple of $X^{1/8}$ in $\log T$, not below every fixed exponent $a<1/8$. The remaining range is not covered by this estimate: At a $q$-power ordinate its first term in (1) is of order $X^{\beta_0-1/2}$, before any one-sided improvement. This does not settle those heights, all constants at the limiting scale, or the unrestricted compact/Pick problem.
