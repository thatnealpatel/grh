# Delete 33: A trace refit crosses the negative boundary

In the fixed $(10,2)$ shallow comparison at $c=39/20$, the second triple $(-7,6,19)/25$ cannot separate even with arbitrary finite real first masks at both heights on **all $k/25$ with $k\ge-320$**. This includes finite $L=2048,8192$. The old fixed-trace obstruction at $-257$ was not an obstruction to jointly refitting the traces and the prime law.

The [integer witness](deletion-laws/delete-33-minus320.txt) has 875 prime slabs, including all ramp knots for $[-320,256]$, and 512 folded trace cells. It was nominated by subdividing the bilateral table's prime slabs and refitting weights on their existing atom sites and on the existing circle sites, with free disk variables at $t$. The proof does not use the solve. Apply the [bilateral Gram repair and common dilution](bilateral-deletion-33.md) on this asymmetric index interval: The checker encloses the pre-dilution correction norms by $3.310\cdot10^{-8},7.827\cdot10^{-9},9.748\cdot10^{-13}$ for the two first blocks and the retained second block. Diluting by $10^{-6}$ pays for these corrections and leaves surplus greater than $3.1442\cdot10^{-5}$. The finite $t$ price comparison and cancellation of its higher orders are unchanged.

For every $k\ge257$ the positive endpoint is still 256. The finite Gram repair contributes a geometric progression beyond it, regardless of its left endpoint. Hence the [same positive-tail recurrence and invariant interval](halfline-deletion-33.md) apply without altering earlier moments: The new joint atom gauge through 800 is below $0.0081$, and each component at 800 lies in the invariant interval $[-1/8,1/8]$. The normalized absolute curvature of the *new* diluted trace targets at $l=-320$ exceeds 41 and 39, respectively (allowing $4\cdot10^{-8}$ pre-dilution repair error). The next negative site $-321$ cannot be added to these fixed traces by changing primes alone. This does not exclude further joint refits.

Run both checks from the repository root with SageMath 10.9 and assertions enabled:

```sh
b=.godel/bob
/opt/sage-10.9/bin/python "$b/check-bilateral-deletion-33.py" --left -320 --table "$b/deletion-laws/delete-33-minus320.txt" --min-surplus 31442/1000000000 --max-first-repair 4/100000000
/opt/sage-10.9/bin/python "$b/check-halfline-deletion-33.py" --minus320
```

## A different next experiment: Close a tail, rather than another finite interval

There is a structural limitation to continuing a **fixed** cell table. Write $h=1/25$, $r=e^{-h/2}$, $P_r=(1-r^2)/|1-re^{i\varphi}|^2$, and $L_k(v)=\Re\int e^{ik\varphi}P_r v\,d\varphi/(2\pi)$ on the period. For a reflected first trace $v(-\varphi)=\overline{v(\varphi)}$, the integral is real. A bounded prime profile satisfies

$$|p_{-n}(Y)|=\left|r^n\int_0^\infty t e^{-t}Y(nh+t)\,dt\right|\le r^n.$$

If $v$ is piecewise constant plus a trigonometric Gram repair, let $J_\theta=P_r(\theta)\Delta v(\theta)$ denote each net periodic jump, counted once. Integration by parts on cells gives $n L_{-n}(v)=(2\pi i)^{-1}\sum_\theta J_\theta e^{-in\theta}+o(1)$ by the Riemann-Lebesgue lemma on the integrable cell derivative. The Cesàro mean square tends to $\sum|J_\theta|^2/(4\pi^2)$ by the finite geometric sum. Any surviving jump thus precludes $D L_{-n}(v)=p_{-n}(Y)$ for all large $n$. For example the first two $t$ disk rows of this table have different imaginary coordinates, and the continuous Gram correction and positive rescaling do not erase the jump. This is not an obstruction to smooth or changing traces.

Instead try a final first trace $v=\sum_{j=-K}^M a_j e^{ij\varphi}$ and a prime profile constant for $z\ge Mh$. A monomial contributes $\Re(a_j)r^{|k+j|}$, so $r^{-n}D L_{-n}$ and $r^{-n}p_{-n}$ are each constant for $n\ge M$. Matching at $-M$ closes that entire tail. With $Y=0$ for $z<-Kh$, $r^{-k}p_k=\int_{-Kh}^\infty e^{-z}(z+kh)Y(z)\,dz$ is affine for $k\ge K$, while $r^{-k}D L_k$ is constant. Two matches, at $K,K+1$, suffice there; one is not enough unless the slope is known to vanish. Test finite-block feasibility **including** this extra constraint at both heights, not just a polynomial fit to the displayed table. Need a common admissible prime law, realizable trace moments including the higher zeros, support-preserving exact repairs, and positive surplus. No such full-lattice law, unrestricted minimum, or signed arithmetic estimate follows here.
