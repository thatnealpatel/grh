# Delete 33: One common law on the entire first lattice

At $c=39/20$ in the $(10,2)$ comparison, no finite real first masks at $t$ and $3t$ on **any** sites of $\mathbb Z/25$ and no real second mask at $3t$ on $S/25$, $S=(-7,6,19)$, give a positive priced margin. One law matches all first indices simultaneously, all three second replies vanish, and its failure mean exceeds $8/9$ by more than $1.683\cdot10^{-5}$. The conclusion includes the finite $L=2048,8192$ prices on their recoverable frequencies. The [minus320 result](minus320-deletion-33.md) gives a larger surplus on a smaller span. Its cell traces were not continued here.

## Derive the entire first traces from the prime law

The [integer table](deletion-laws/delete-33-full.txt) specifies 330 successive prime laws using the [bilateral table conventions](bilateral-deletion-33.md): On each slab normalize the nonnegative integer weights, set $X=2u^2-1$ at the listed atoms, and compute $A=\mathbb E X$, $B=\mathbb E(4X^3-3X)$, and $U=\mathbb E u$. Use $X=0$ before the first row at $-112/25$ and extend the last row at $110/25$ to infinity. The failure mean is $\int z_+e^{-z}U(z)\,dz$.

Write $h=1/25$, $r=e^{-h/2}$, $\varphi=h x$, $C=\cosh(c)/3$, and $C_t=C/(2\cos(\pi/12))$. For $(Y,D)=(A,C_t)$ or $(B,C)$ let $f_k=p_k(Y)/D$ with

$$p_k(Y)=\int e^{-z-kh/2}(z+kh)_+Y(z)\,dz.$$

At each jump $z$ the step integral contributing to $p_k$ is $(1+s)e^{kh/2-s}\Delta Y(z)$, $s=(z+kh)_+$. For $k\le-110$, $f_k=r^{-k}Y(110/25)/D$. For $k\ge112$, $f_k=r^k(a+bk)$ for constants $a,b$ with $b=(h/D)\sum_z e^{-z}\Delta Y(z)$. In particular the positive slope term need not be removed by a repair.

Use the **bilateral** inverse of the Poisson moment kernel:

$$a_k=\frac{(1+r^2)f_k-r(f_{k-1}+f_{k+1})}{1-r^2},\qquad v(\varphi)=\sum_{k\in\mathbb Z}a_k e^{-ik\varphi}.$$

Indeed $g_j=r^{|j|}$ satisfies $((1+r^2)g_j-r(g_{j-1}+g_{j+1}))/(1-r^2)=\mathbf1_{j=0}$. Both sequences are summable. The folded probability measure for $\varphi$ has density $P_r=(1-r^2)/|1-re^{i\varphi}|^2$ relative to uniform measure, with moments $g_j$. Hence $L_k(v)=\Re\int e^{ik\varphi}vP_r\,d\varphi/(2\pi)=(g*a)_k=f_k$ for **every integer** $k$. This is an identity of the constructed law, not a residual check. The tail formulas for $f$ give $a_k=0$ for $k<-110$ and $a_k=br^k$ for $k>112$. Thus $v$ is a Laurent polynomial plus $b(re^{-i\varphi})^{113}/(1-re^{-i\varphi})$. Call its two instances $v_t,m$.

## Exact second replies and admissibility on the whole circle

The second section of the table gives real Laurent coefficients for $n^0$ in the same negative-exponent convention. Define $d_j=L_j(n^0)$, $G_{ij}=r^{|i-j|}$ on $S$, and subtract $\sum_{j\in S}(G^{-1}d)_je^{-ij\varphi}$ from $n^0$ to get $n$. This makes $L_S(n)=0$ exactly. The checker uses the tridiagonal three-site inverse with correlation $r^{13}$; the correction costs less than $1.52\cdot10^{-12}$ in coefficient $\ell^1$ norm.

The uniform tests are $|v_t|\le1$ and $|m|^2+|n-m^2|\le1$. At $3t$ the second inequality realizes both moments in a *single* circle law: The chord through $m$ in direction $\omega$, $|\omega|=1$, with endpoint probabilities giving mean $m$, has second moment $m^2+(1-|m|^2)\omega^2$. This follows by taking the product of the two signed chord distances, $|m|^2-1$. Mix the chords with directions $\omega$ and $i\omega$ to obtain any point of the disk, with a measurable choice of angle. Rotation by $\pi$ gives the negative first sign without changing $n$. At $t$ use the [twelve-angle law](single-shift-10-2.md) with first mean $-v_t/(2\cos(\pi/12))$ and orders two through ten zero. Evaluating the prime infimum and averaging the trace maxima on these laws gives a priced margin at most $8/9-\int z_+e^{-z}U(z)\,dz$, by the [bilateral price argument](bilateral-deletion-33.md). The finite positive-mask cost at $t$ dominates the ideal one wherever it recovers the first mask.

**Replay:** From the repository root with SageMath 10.9 and assertions enabled:

```sh
/opt/sage-10.9/bin/python .godel/bob/check-full-deletion-33.py
```

The checker uses original step integrals, exact rational atom coordinates and weights, and 128-bit outward real and complex balls. It evaluates all fields at $N=131072$ equally spaced nodes by the ball FFT, using reflection symmetry. It truncates each first trace at $J=1536$ *only for evaluation*, bounding the omitted sup norm by $|b|r^{J+1}/(1-r)$. For derivative bounds $M_i$ use $\sum_k|k|^i|a_k|$, including the full geometric tail. For each fixed unit phase the real projection of $v_t$ exceeds its endpoint chord by at most $(2\pi/N)^2 M_{2,t}/8$. For the second test, apply the same chord estimate to $|m|^2+\Re(\omega(n-m^2))$ for each fixed unit $\omega$, bounding its absolute second derivative by

$$\sum_j j^2|n_j|+4M_{1,m}^2+4M_{0,m}M_{2,m}.$$

Maximize over phase *after* interpolation. The two nodal square terms each incur at most $e(2M_{0,m}+e)$ error for omitted first tail norm $e$. Outward lower bounds on the all-angle slacks are $6.90\cdot10^{-5}$ at $t$ and $4.01\cdot10^{-5}$ for the actual second disk at $3t$. The failure surplus is $1.68361204370\ldots\cdot10^{-5}$. The table was nominated by refitting the minus320 atom weights on a shorter slab range, with first traces derived from them and quadratic cuts for second-disk feasibility. Neither solver optimality nor sampled feasibility enters the proof.

## Decision beyond the lattice

Merely adding more first indices on $\mathbb Z/25$ cannot reopen this triple. The finer lattice $\mathbb Z/50$ **does** distinguish this particular prime law in the ideal first test. Repeat the same step and stencil formulas with $h=1/50$, endpoints $-220,224$ in first-index space, and the same prime table and $D$. Direct ball evaluation of the exact rational tail and finite Laurent sum gives normalized first moduli $>1.012$ at $t$ and $>1.0015$ at $3t$, at $\varphi/(2\pi)=2734/65536,923/65536$ respectively. For a conjugation-reflected trace all moments are real; their values on the whole lattice determine $P_r v$ by Fourier uniqueness. Any nonperiodic admissible competitor may first be conditionally averaged modulo the period and symmetrized by conjugation without increasing the first cap. Thus neither finer-lattice ideal disk can match *these* primes. This does not exhibit a positive finite priced margin or preclude a joint refit. Next test a common law for the same triple on the half-step first lattice, keeping the original physical second shifts (indices $-14,12,38$ there). The unrestricted minimum, arbitrary real first translates, and the signed arithmetic lower bound remain open.
