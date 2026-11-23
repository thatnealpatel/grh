# Does a detector-sized interval force a higher harmonic?

Not by positivity or by the power relation between phases. There is a control with one shared phase per prime, a base contribution exponentially above the unit budget on each of $\gg D$ shifts, and **no** higher harmonic at the high cutoff at any admissible integer image of the contributing interval. It can even run on a single perturbed height curve. At the **genuine** prime logarithms there is a separate finite certificate, not an asymptotic counterexample.

Use the [frozen high branch](balanced-height-reconstruction.md): $t=2q^{3/5}$, $X=(3\log(t/2))^2$, $D=\log X$, $L=X/D$, $n=2\lceil(2+\gamma)\log t/D\rceil$, $0<\gamma<1/2$, $r=D^2$, $m=X^{-1/10}$, and $B_{\rm unit}=L16^{-n}/t$. For $1\le d\le5D$ take the actual edges $p,p+d$ prime in $[e^{-8}X,X]$, frequencies $\lambda_{d,p}=\log(1+d/p)$, weights $w_p=X^{-1}\log(X/p)\log p\log(p+d)$, and total mass $A_d=\sum w_p$. For complex edge terms $c_p$ let $Z=\sum c_p$. On $|Z|\ge m$ use the original

$$W_2=|Z|^n\exp\left[-\tfrac12n^2\sum_{|p-p'|\le r}\Re(c_p/Z)\Re(c_{p'}/Z)\right],\qquad K_t(v)=t^{-1}\operatorname{sinc}^2(\pi(v/t-1)).$$

Here the pair sum is ordered, including the diagonal, and $\operatorname{sinc}(x)=\sin(x)/x$.

## One choice of phases across all the shifts

For a circle probability law, first moment $a\le1/2$, $a\ge0$, is compatible with *every* higher moment zero: Take density $1+2a\cos\theta$ against normalized arc length. The relevant moment for an edge sum is $Z/A_d$, not $Z$ or $B_{\rm unit}$. The issue with using the law edge by edge is that many edges share prime endpoints. Here is a simultaneous realization that respects this constraint.

At each sufficiently large $t$ use the [consecutive-prime matching](matched-prime-overlap.md#a-matching-large-enough-for-a-full-support-control). One parity, chosen once for the whole band, supplies matching mass $B_d>1/4$ on $\gg D$ shifts with $A_d\le M$ for a fixed $M$. Call these shifts eligible; this is not a selection by a genuine peak. Draw independent groups of vertex phases $z_p$: Use $(\xi,\xi\eta)$ in increasing-prime order on a matched edge, with $\xi$ Haar and $\eta$ independent of density $1+\cos\theta$, and Haar on a singleton. Consider the frozen sums

$$F_{k,d}(v)=\sum_p w_p(z_{p+d}/z_p)^k e^{ik(v-t)\lambda_{d,p}}.$$

At $k=1,v=t$ the matched ratio has mean $1/2$, and all other edges join different groups with mean-zero ratio. Thus $\mathbb E\Re F_{1,d}(t)=B_d/2>1/8$ on the eligible shifts. For fixed $d$, a group meets at most four edges, and changing it changes the real sum by at most twice their total weight. Squaring and summing these replacement bounds over groups costs at most $32\sum w_p^2\le32 w_*A_d$, $w_*=8D^2/X$. Bounded differences at deviation $1/64$, followed by a union over shifts, show that with probability $1-o(1)$ **all** eligible shifts exceed $7/64$ in real part. The derivative of $F_{1,d}$ there is bounded in modulus by $5Me^8/L$. Thus on $J=[t,t+bL]$, $b=(640Me^8)^{-1}$, the real parts stay at least $13/128>3/32$.

For each integer $k\ge2$, $\eta^k$ is Haar because all its nonconstant Fourier coefficients vanish. Hence $(\xi^k,\xi^k\eta^k)$ is product Haar, and the powered vertex phases are iid Haar. For fixed $d$ the graph of edges of step $d$ is a forest. Its root phases and edge ratios are independent Haar coordinates (remove leaves successively). Hoeffding applied to the real and imaginary sums therefore gives, at fixed $k,d,v$ on nonempty support,

$$\Pr\{|F_{k,d}(v)|\ge m/2\}\le 4\exp[-m^2/(16\sum w_p^2)]\le 4\exp[-cX^{4/5}/D^4].$$

The last inequality uses $A_d\ll D^2$ even on ineligible shifts. Put $T=t^{13/8}$. Uniformly for $k\le\lceil T\rceil$ the derivative is bounded by $H=1+C\lceil T\rceil D^3/X$ for a fixed sufficiently large $C$. Test a mesh of $[-T,T]$ of spacing at most $m/(4H)$, all $1\le d\le5D$, and all $2\le k\le\lceil T\rceil$. The log of the number of tests is $O(\log t)=O(\sqrt X)$, smaller than the tail exponent. Off the mesh the loss is at most $m/4$. Intersecting the two probability bounds gives a single draw with $|F_{k,d}(v)|\le3m/4$ throughout the higher tests, without assuming independence between tests. Empty support is automatic.

On $J$, for each eligible base sum, $K_t\ge1/(2t)$ and the absolute quadratic exponent in $W_2$ is at most $n^2(1+2r)w_*M/(2(3/32)^2)=O_{M,\gamma}(D^2)=o(n)$. Thus the integral on $J$ alone is at least $B_{\rm unit}(b/2)(3/2)^n e^{-O(D^2)}$. This is an exponential excess on the same shifts throughout one common shell interval. It does not require an $O(1)$ correction on every shift. If a test first trims by $n^2 C_d(r)\le K$, the [summed collision bound](detection-radius.md) on the eligible range costs $O(D/K)$ shifts, so a sufficiently large fixed $K$ still leaves $\gg D$.

**Which curve is being tested?** Writing $z_p=\chi(p)p^{it}$, the sum at index $k$ uses $\chi^k$ at $kv$, not the unchanged twist $\chi$ there. There is an alternative with a *single* height curve per shift, retaining common vertex labels. Choose $|\epsilon_p|\le\pi$ so that $\exp(i t\log p+i\epsilon_p)=z_p$, and put $a_p=\log p+\epsilon_p/t$. Evaluate $\sum w_p e^{iu(a_{p+d}-a_p)}$ with the same labels at every $u$. At $u=kv$, $v\in J$, this differs from $F_{k,d}(v)$ by at most $2\pi A_d k bL/t$, since only the phase increment from $t$ to $v$ was perturbed in the powered comparison. For $kv\le T$ one has $k\le t^{5/8}$, so the uniform error is $t^{-3/8+o(1)}=o(m)$. The base retains $>3/32$ and the same lower integral bound, and **every** in-band integer image $k\ge2$ is below $m$. The perturbations preserve endpoint sharing but change the logarithms by up to $\pi/t$. They do not realize an untwisted arithmetic example. The conclusion is one assignment per frozen center, not recurrence of a given assignment at named centers.

## What the images would cost in the genuine kernel

Even if amplitudes replicated perfectly, images of this short $J$ would not amplify the original integral. For $v=t+x\in J$, $k\ge2$, the sine in $K_t(kv)$ has modulus $|\sin(\pi kx/t)|\le\pi kx/t$, while the sinc denominator is at least $\pi(k-1)$. Hence $K_t(kv)\ll x^2/t^3$. The [high-branch bound](genuine-high-shell.md) is $W_2\le t^{o(1)}$ at the genuine retained points. Charging all images, even with multiplicity, costs at most

$$t^{o(1)}(bL)^3t^{-3}\sum_{2\le k\le t^{5/8}}k\le t^{-7/4+o(1)}=o(B_{\rm unit}).$$

The factor $k$ is the Jacobian. Recentring instead gives $kK_{kt}(kv)=K_t(v)$, but this is a different test; at unchanged arithmetic cutoff its signed triangular multiplier is now supported on $|\nu|\le2\pi/(kt)$, with phase $kt\nu$. Nothing in this calculation compares the two signed sums. Nor does the short-interval charge apply to all of $[t,5t/4]$.

## A genuine finite test

Run `sage -python .godel/bob/check-shell-dilations.py` without `-O` (tested with Sage 10.9's Python). Take the unmodified logarithms at $q=100000007$, $d=26$, $\gamma=1/4$, so $n=8$. On the union of

$$[132304.65395,132304.65485],\qquad [133638.09295,133638.09355]$$

one has $t<v<5t/4$, $|Z(v)|>m$, and $|Z(kv)|<m$ for **all integers** $k\ge2$ with $kv\le t^{13/8}$. The two source intervals together contribute between $1.1704$ and $1.2123$ times $B_{\rm unit}$ to the corrected high-branch integral. These are outward decimal bounds. The checker encloses the base integrand over each entire interval with 100-bit interval arithmetic. For the images it covers every multiplier through an upper bound for $\lfloor T/\inf v\rfloor$ (1470 and 1456, respectively), bisecting the rational source interval when needed. The grid that located these intervals is not used to certify them.

This rules out charging *every* detector-sized set to images of its own points at the same high cutoff in this fixture. It does not assert that the rest of the finite shell has no images, that a weaker harmonic floor fails, or that $X^{-1/10}$ is near $1/16$ at this $X$. In fact $X^{-1/10}\approx0.49646$ here. Reopening an asymptotic dilation argument requires a property of the exact logarithms at the coupled heights, not just a common phase per prime, a bandwidth bound, or a circle moment. The weighted count in the [genuine upper sum](genuine-high-shell.md) remains open.
