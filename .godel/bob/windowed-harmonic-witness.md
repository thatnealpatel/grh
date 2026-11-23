# A single harmonic witness on the actual kernel window

The [broad-window square](distant-frequency-differences.md) retains a count of *unwrapped* small differences, but its positive part exceeds the squared detection scale by a power of $t$. An alternative is to keep **both original frequencies inside the detector window** and wrap their difference. A flat density on this finite window then gives exactly zero, not a boundary energy. More particularly a detected excess forces a single nonzero harmonic of the weighted distant-pair count to be large; the index need not be fixed across shifts.

Use that note's $t,d,n,L,\gamma,R_*,s$, product weights, separation radius, and completed-tuple gate. Let $\sigma$ count the scaled frequencies $z=t\nu$ on $[-2\pi,2\pi]$ with those weights and no taper. The omitted slot is recovered throughout this interval. The cut is on the original log frequency, not the rounded linearization. Write $G(z)=(1-|z|/(2\pi))_+\cos z$. We have $S=\int G\,d\sigma=J_R+O(t^{-1-\gamma/8+o(1)})$ by the private-slot bound (no loss at the power radius). All claims below concern this one center and shift.

**The witness.** Suppose $J_R\ge B$, $B=t^{-1+o(1)}>0$. Fix $0<\epsilon<1/10$. There is an index $1\le j\le t^{3/5+\epsilon}$, either odd or equal to 2, such that

$$ \int\cos(jz/2)\,d\sigma(z)\gg \frac{jB}{\log t},\qquad
 \iint_{\rm distant}\cos(j(z-z')/2)\,d\sigma(z)\,d\sigma(z')\gg\frac{j^2 B^2}{(\log t)^2}. \tag{1} $$

In the second integral use the *tuple* measure underlying $\sigma$ to decide distance: In each direction fewer than $s=\lceil(3+\gamma)L\rceil$ starts may be within $R_*$ of the opposing support. No additional cut on $z-z'$ is made. In particular pairs near opposite ends of the window are not interchangeable with pairs absent from the count. In arithmetic coordinates the phase is $\tfrac{jt}{2}\log(UW'/(WU'))$, with both balanced endpoint selections and both dependent rounded primes retained. All estimates use absolute unnormalized weights, not a probability conditioned on reaching the window.

**Compute the coefficients.** On the circle of length $4\pi$, periodize $G$ from this window. At $|z|=2\pi$ the two definitions agree. The circular Fourier coefficients (in the basis $e^{ijz/2}$) are

$$ c_j=\tfrac14\left[\operatorname{sinc}^2(\pi(j-2)/2)+\operatorname{sinc}^2(\pi(j+2)/2)\right],\qquad \operatorname{sinc}(y)=\sin(y)/y . $$

This follows by integrating the triangle against each shifted frequency. In particular $c_0=0$, $c_{\pm2}=1/4$, all other even coefficients vanish, and for odd $j$ one has $c_j=\pi^{-2}[(j-2)^{-2}+(j+2)^{-2}]$. They are nonnegative and sum to $G(0)=1$, by absolute Fourier convergence. The one-copy observable is thus exactly $\sum_{j>0}2c_j\int\cos(jz/2)d\sigma$. An arbitrary constant density on the detector window is invisible *on every retained mode*. This feature depends on wrapping: The same density tested by an unwrapped difference kernel need not have zero self-energy.

**Price the infinite tail on the actual starts.** Let $H=\lfloor t^{3/5+\epsilon}\rfloor$ and $r(z)=\operatorname{dist}(z,2\pi\mathbb Z)$. Since the odd coefficients beyond $H$ decrease, summation by parts on the step-two progression, using $|1-e^{iz}|^{-1}\ll1/r(z)$, and the absolute tail bound give

$$ \left|\sum_{|j|>H}c_j e^{ijz/2}\right|\ll H^{-1}\min(1,(Hr(z))^{-1}). $$

For $H^{-1}\le v\le1$ the original mass at $r(z)\le v$ is $\ll (v/t)^{1/4}t^{o(1)}$, uniformly. Indeed in this window there are just three possible centers $0,\pm2\pi$. Restore all original slots, dropping all gates for the upper bound but imposing the selected interval on $t\nu$. Leave $k=\lfloor\log(t/(8v))/(2D)\rfloor$ positive slots unrevealed; $k<h$ throughout. Distinct hidden log sums are separated by at least $X^{-2k}$ by integer cross-product spacing, and a sum fixes the multiset of starts by prime valuations. An interval of width $2v/t$ thus allows at most $k!$ assignments. With the original one-slot probability bound $b_0\ll D^2/X$, the unnormalized price is $A^n k! b_0^k\le (v/t)^{1/4}t^{o(1)}$. The same argument at constant width gives $\sigma(\mathbb R)\le t^{-1/4+o(1)}$. Summing the tail bound over $r\le1/H$, the shells $2^k/H<r\le2^{k+1}/H$ up to 1, and the remainder costs

$$ \ll t^{-1/4+o(1)}H^{-5/4}=t^{-1-5\epsilon/4+o(1)}. $$

The geometric series here is $\sum 2^{-3k/4}$, not a uniform bound times the whole window mass. In particular no truncation at a fixed number of circle harmonics is proved. The finite sum is now $\ge (1-o(1))B$. Since $\sum_{j=1}^H 2jc_j\ll\log t$, some index of nonzero coefficient satisfies the *positive*, not merely absolute, first inequality of (1).

**Square the one mode, then remove nearby supports.** Before the distance cut the pair integral equals $|\int e^{ijz/2}\,d\sigma|^2$, at least the square of the first integral. The absolute mass of nondistant pairs on this compact product of windows is at most $t^{-b'+o(1)}$, $b'=1/2+(3+\gamma)(1/2-\xi)>2+\gamma/4$, $R_*=X^\xi$. As in the broad-window proof, price the first window by hiding $\lfloor\log(t/32)/(2D)\rfloor$ positive labels, then mark $s$ second labels approaching the first support. They cost $(n(2R_*+1)b_0)^s$ for a fixed mask. Price the *second original window* by hiding a further $\lfloor\log(t/32)/(2D)\rfloor$ unmarked second labels, possibly of mixed signs. Their starts are distinct in a separated completion, so the signed sum fixes them up to ordering and gives the same factorial saving. Sum over masks and both directions. Each window contributes $t^{-1/4+o(1)}$ independently of the disclosed labels in its bound. This price is uniform in $j$ since $|\cos|\le1$, and is negligible compared to $B^2/(\log t)^2$. This proves (1).

**Decision.** One may try to exclude the positive harmonic witnesses (1) on actual, doubly windowed distant pairs instead of comparing the broad-window central and negative annuli to power-relative precision. Upper bounds $o(j^2 B^2/(\log t)^2)$ uniformly on these modes would suffice. The circular calculation provides a necessary witness, not such an upper bound; a large squared harmonic alone does not imply large $J_R$. Removing the two original windows, taking absolute values of the oscillating terms, or enforcing $|z-z'|\le2\pi$ after wrapping would test a different count.
