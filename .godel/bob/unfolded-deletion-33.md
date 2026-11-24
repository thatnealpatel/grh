# Delete-33 with real first shifts

At $c=39/20$ the three second sites $s_j=(6+13j)/25$, $j=-1,0,1$, do not separate even if **every real first shift at $3t$** is available, provided the first shifts at $t$ are on $\mathbb Z/50$. At $c=39001/20000=1.95005$ neither height needs the lattice restriction. In each row one common prime law, and one conditional circle law per height, work for the entire indicated span. These are obstructions in the $(10,2)$ priced comparison, not arithmetic examples.

| Depth | First shifts at $t$ | First shifts at $3t$ | Failure mean minus $8/9$, lower bound |
|---|---|---|---:|
| $39/20$ | $\mathbb Z/50$ | $\mathbb R$ | $2.5008\cdot10^{-7}$ |
| $39001/20000$ | $\mathbb R$ | $\mathbb R$ | $6.5501\cdot10^{-8}$ |

All three second replies at $3t$ vanish simultaneously, as do orders two through ten at $t$. Thus the negative of the tabulated surplus bounds the priced margin from above for every finite real mask in the indicated class. The [half-step certificate](half-step-deletion-33.md) gives a stronger surplus when *both* first masks lie on the half-step lattice at $39/20$.

## Prime laws and first replies

Use the [seed](deletion-laws/delete-33-unfolded-seed.txt) and [half-step](deletion-laws/delete-33-half-step.txt) prime tables on the same 426 slabs. In a row, normalize the integer weights, put $u=i/10^9$ at atom index $i$, and set $X=2u^2-1$, $A=\mathbb E X$, $B=\mathbb E(4X^3-3X)$, and $U=\mathbb E u$. Use $X=0$ left of the first knot and continue the final slab to infinity. At $39/20$ mix the seed and half-step laws in proportions $3/20$ and $17/20$ slab by slab. At $39001/20000$ use the seed alone, replacing a fraction $3/100000$ of its law by $u=1$ on each nonnegative slab. In both cases the failure mean is integrated directly against $z_+e^{-z}\,dz$.

Write $w=1/2+ix$, $d\mu=dx/(2\pi|w|^2)$, $C=\cosh(c)/3$, and $C_t=C/(2\cos(\pi/12))$. The [translate identity](single-shift-10-2.md) gives the normalized field

$$V_Y(x)=\frac1w\sum_l b_l e^{ixz_l},\qquad b_l=e^{-z_l/2}\Delta Y_l/D,$$

with $(Y,D)=(A,C_t)$ or $(B,C)$. At $3t$ use $m=-V_B$. In both rows $\|m\|_\infty<.99999$. In the second row $\|V_A\|_\infty<.999999$. At $t$ take the twelve-angle law with first mean $-V_A/(2\cos(\pi/12))$ and higher moments through order ten zero. For the first row only, mix the seed's $t$ law (its unfolded cap is $<.999999$ at $39/20$) with the accepted half-step $t$ law evaluated at $x/50\bmod 2\pi$. The pushforward of $\mu$ has the required Poisson density, so all the lattice replies match by linearity. This argument does **not** unfold the half-step $t$ field. For the mixed primes at $x=9.1$, the unfolded normalized $t$ field has modulus $>1.00210$; for the second row's primes at $x=0$ it would exceed $1.0000457$ if the depth were reset to $39/20$.

The checker bounds $|wV_Y|^2-\beta^2|w|^2$ on adaptive intervals by its Taylor polynomial through degree three, using $D_k=\sum_l |b_l||z_l|^k$ and fourth derivative bound $\sum_{k=0}^4{4\choose k}D_kD_{4-k}$. For the outside rays it uses $|V_Y|\le D_0/|x|$; reflection halves the compact interval. No maximum on a frequency grid is used as a continuous cap.

## Exact three-site completion

Set $h=13/25$, $s_0=6/25$, and $\theta=h x$. With the $3t$ jumps $b_l$, compute $T_j=\Re\int e^{is_jx}m^2\,d\mu$ and $R_j=\int\cos(j\theta)(1-|m|^2)\,d\mu$ by the [sum and difference kernels](single-shift-10-2.md):

$$T_j=\sum_{l,k}b_lb_k(1+v_++v_+^2/2)e^{-|v|/2},\quad v=s_j+z_l+z_k,$$
$$R_j=e^{-|jh|/2}-\sum_{l,k}b_lb_k(2+|v|)e^{-|v|/2},\quad v=jh+z_l-z_k.$$

The checker convolves the jumps in integer units of $1/400$. For $jh$ beyond the knot span the difference sum is exactly an affine function times an exponential; no high-frequency cutoff in $\mu$ is involved.

Take $g=e^{-is_0 x}\sum_{|k|\le192}v_ke^{-ik\theta}$ with real coefficients. Then $n=m^2-(1-|m|^2)g$ has the three required zero replies precisely when $\sum_k R_{j-k}v_k=T_j$ on $j=-1,0,1$. To construct $v^0$, sample $\bar H/\sqrt{1+|H|^2}$ on the 2048 roots of unity, where $H=\lambda_-e^{-i\theta}+\lambda_0+\lambda_+e^{i\theta}$ and the three decimal inputs for each law are specified in the checker. Retain the real negative-exponent Laurent coefficients of this *finite transform* up to degree 192. This nominates a polynomial, not an approximation whose discarded coefficients need to be bounded. Correct just its central three coefficients by $G^{-1}(T-R*v^0)$ on these sites with $G_{ji}=R_{j-i}$. The positive antisymmetric eigenvalue and the positive definite symmetric block are checked before inversion. The corrected coefficients are defined by this exact solve, not by a residual tolerance.

After correction, evaluate the polynomial on 16384 equidistant nodes. For each real projection the possible excess above its endpoint chord is at most $(2\pi/16384)^2\sum k^2|v_k|/8$. Maximizing over projection angles gives $1-\|g\|_\infty>1.9071\cdot10^{-5}$ and $>3.6093\cdot10^{-4}$ in the two rows. Hence $|n-m^2|\le1-|m|^2$ pointwise. The [two-chord realization](full-lattice-deletion-33.md) now gives one circle law realizing both moments. The prime infimum and trace maxima can be tested on these laws as in the [bilateral price argument](bilateral-deletion-33.md).

## Why the half-step primes alone do not suffice

These primes pass the **unfolded** $3t$ first cap ($\|m\|_\infty<.9985$), but fail the simultaneous second test even if the $t$ first mask remains on the old lattice. Use $L=.74e^{-i\theta}+.90+e^{i\theta}$ and $H=e^{is_0x}L$. The least possible real reply on $H$ is the center $\sum\lambda_j T_j$ minus the radius $\int |L|(1-|m|^2)\,d\mu$. For a uniform upper bound on the radius form a real even degree-144 Laurent polynomial $p$ from the 1024-node transform of $|L|$. Bound $\|p^2-|L|^2\|_\infty$ by the coefficient $\ell^1$ norm $e$ of the difference. Since $|L|>.1$ (use its real part for $|\cos\theta|>.9$, otherwise its imaginary part), $e<.01$ and $p(0)>0$ in angle coordinates imply $p>0$. In particular $|L|\le p+\sqrt e$. Integrating the majorant uses the $R_j$ above. The center exceeds this **upper** radius by more than $2.2712\cdot10^{-5}$.

The same primes already fail at $3t$ with first shifts on $\mathbb Z/100$: The price of the same $H$ is $>2.9471\cdot10^{-6}$. For this test fold by $\varphi=x/100$ and use the unique conjugation-symmetric folded first mean determined by all first replies. It is also the conditional expectation of the unfolded mean, so its modulus stays below $.9985$. With $r=e^{-1/200}$ let $f_i$ and $a_i$ be the [bilateral replies and stencil coefficients](full-lattice-deletion-33.md) for $B/C$ (omit the common minus sign before squaring). Then the center at folded index $s$ is $\sum_i a_i f_{s-i}$ and the Fourier moment of the radius weight at index $s\ge0$ is $r^s-\sum_i a_i f_{s+i}$. These follow by inserting just one Laurent expansion in the defining integral. The checker sums the tails using $a_i=b r^i$ beyond the right endpoint, $f_i=r^i(a+bi)$ there, and $f_i=r^{-i}B_{\rm last}/C$ on the left. Here use $s=100s_j$ for the centers and $s=52|j|$ for $R_j$. Folding and conjugation preserve all the measured real responses for any competitor (average the reflected circle laws, not merely their first moments). Thus the fixed-prime rejection applies even to nonperiodic competitors. Neither price excludes a joint prime refit.

**Replay** with SageMath 10.9 and assertions enabled:

```sh
/opt/sage-10.9/bin/python .godel/bob/check-full-deletion-33.py --denominator 50
/opt/sage-10.9/bin/python .godel/bob/check-unfolded-deletion-33.py
```

**What a moment-preserving polish can buy.** For the unmixed seed, the failure deficit at $39/20$ is about $3.26793\cdot10^{-6}$. Even allowing *all* real atom sites $u\in[0,1]$, no slabwise refit preserving $A,B$ can reduce that deficit below $3.2574\cdot10^{-6}$. On each nonnegative slab the [dual table](deletion-laws/delete-33-unfolded-Udual.txt) gives an affine majorant $(a+I+bX+cT_3(X))/10^{12}$ of $u$. To verify the inequality substitute $X=2u^2-1$, convert the degree-six difference polynomial to Bernstein coefficients, and bisect by de Casteljau until every piece has the correct coefficient sign. Integrate the affine majorants using the exact seed moments and the positive slab masses. This rules out moment-preserving polish of this seed, not a change of its trace inputs.

**Decision.** At $39/20$, refining only the $3t$ first mask cannot separate delete-33; a separating first-mask extension must use new $t$ shifts as well. The mixed and nearby witnesses do not settle the all-real comparison at $39/20$. A reason to revisit the continuous refit is a change to the available prime profiles, not a denser angular check of either law above. In particular the seed uses constant laws on each of the 426 fixed slabs. Splitting slabs at *movable* boundaries changes the moment profiles without forcing the $u$ coordinates to change; assess that freedom against the active first caps and the three-site disk before further atom refinement. The unrestricted three-versus-four minimum and the signed arithmetic lower bound remain open.

**After Work:** The [priced refit](priced-deletion-33.md) preserves just the third harmonic and reaches $1.95001720$ on the original mesh. Its six-row alternative and priced one-atom obstruction narrow the proposed boundary experiment at $39/20$; the exact-depth target is still open.
