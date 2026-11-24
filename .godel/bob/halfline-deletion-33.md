# Delete 33: every positive first shift on the lattice is free

In the [bilateral deletion comparison](bilateral-deletion-33.md) with $c=39/20$ and second triple $(-7,6,19)/25$, one common prime law and the same two repaired trace laws match **all** first indices $k\ge-256$, at both heights. The surplus is unchanged, greater than $3.146\cdot10^{-5}$. Hence no real, finitely supported first masks on this half-lattice separate, including at finite $L=2048,8192$. This extends the range of the first shifts $k/25$, not their resolution. The lattice is asymmetric: for the next negative index, $-257$, even replacing the *entire* prime law cannot match these traces while keeping the two adjacent index matches.

## Half-line construction

Use the notation, prime table, and exact repairs of the bilateral proof. Write $h=1/25$, $r=e^{-h/2}$, $d_+=e^h-1-h$, $d_-=e^{-h}-1+h$. Work before the common dilution. Let $Y=A$ or $B$, with corresponding multiplier $D=C_t$ or $C$, tabulated first profile $v$, and repair $q$. The new primes occupy only $z<-256h$. All previously matched ramps and the failure integral vanish there. On $[-jh,-(j-1)h)$ set the corresponding mean equal to $s_j$ for $j>256$.

For the original zero extension let $p^0$ be its prime moments. The response of slab 257 to the first new index is $r^{-255}d_+s_{257}$. Since $L_k(q)=r^{k-256}L_{256}(q)$ for $k\ge256$ and the endpoint already matches, set

$$s_{257}=\frac{r^{255}}{d_+}\left[D(L_{257}(v)-r L_{256}(v))-(p^0_{257}-r p^0_{256})\right].$$

The prime increment in parentheses is $hr^{257}\int_{-256h}^\infty e^{-z}Y(z)\,dz$. For subsequent slabs use

$$d_+s_{l+1}+d_-s_l=D r^l[L_{l+1}(v)/r-2L_l(v)+rL_{l-1}(v)],\qquad l\ge257.$$

Indeed $r^l(p_{l+1}/r-2p_l+r p_{l-1})$ integrates $e^{-z}r^{2l}Y(z)$ against the triangular hat $(h-|z+lh|)_+$. Its two half-integrals without $Y$ are $d_+,d_-$, in increasing $z$ order. The geometric repair drops out. Thus starting with two consecutive matches gives every subsequent match exactly. No infinite matrix inversion or exchange with a divergent prime integral is involved: each fixed index sees only finitely many new slabs.

The checker encloses both sequences up to $j=800$; the largest joint atom gauge $(|2a+b|+2|a-b|)/3$ is below $0.122$. For both sequences $|s_{800}|<1/8$. Since $|L_k(v)|\le1$ and $0<d_-<d_+$, the checked inequality

$$D r^{800}(r^{-1}+2+r)<(d_+-d_-)/8$$

makes $[-1/8,1/8]$ invariant under every remaining step. There the joint gauge is at most $7/24$. The [signed atom construction](free-slab-extensions.md) therefore realizes each pair by a common probability law. Apply the original dilution everywhere. The second matches and the surplus do not change, so the same price argument works for arbitrary finite masks on the claimed span.

## Why the next negative site requires new traces

The triangular hat identity also gives a universal necessary bound, on *any* prime law with $|Y|\le1$ (after dilution or without it):

$$\big|r^l(p_{l+1}/r-2p_l+r p_{l-1})\big|\le d_++d_-.$$

At $l=-256$ the checker applies the left side to the **repaired and diluted** trace targets. After division by $d_++d_-$ the absolute values exceed $40$ at $t$ and $190$ at $3t$. The check allows $2.1\cdot10^{-8}$ uniform pre-dilution first repair error in each factor, using the bilateral certificate. Consequently changing only primes, including on the positive-$z$ side, cannot match either fixed trace on these three sites.

There is a minimum required displacement even if both primes and traces change. For a change $w$ of the normalized first trace profile, the absolute change in the left-side linear functional is at most

$$D r^l\,(1-r^2)r^{-1}\int_{-\pi}^\pi |w(\varphi)|\,\frac{d\varphi}{2\pi}.$$

Indeed the multiplier $e^{i\varphi}/r-2+r e^{-i\varphi}$ has modulus $|1-r e^{i\varphi}|^2/r$, cancelling the folded Poisson denominator. Thus a refit matching these three coordinates must change the diluted normalized first trace by more than $0.015$ at $t$ and $0.037$ at $3t$ in **flat mean absolute distance**. This is necessary, not a rejection of all refits. In particular additive positive indices alone cannot solve the separator problem, and adding the single negative site does not by itself prove separation.

**Replay:** Run both ball checkers from the repository root with SageMath 10.9 and assertions enabled:

```sh
/opt/sage-10.9/bin/python .godel/bob/check-bilateral-deletion-33.py
/opt/sage-10.9/bin/python .godel/bob/check-halfline-deletion-33.py
```

The second checker integrates the tabulated profiles on whole cells by the folded character recurrence at 1280 bits. The finite calculations feed the analytic tail induction; the infinite conclusion is not extrapolated from sampled slabs. The next finite comparison that tests a genuinely new coordinate is $[-257,256]$ with both traces and the prime law free. Start with the three-site necessary bound above; do not constrain the traces to small uniform repairs of this table. The unrestricted three-versus-four minimum and the signed arithmetic estimate are still open.
