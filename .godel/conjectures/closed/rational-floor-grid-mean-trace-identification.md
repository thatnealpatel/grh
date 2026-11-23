---
evidence_revision: 9ebc9f0daa56d26428df5084b1afa98711671881
outcome: established
---

# Identify the finite two-leg mean of the physical floor-grid trace

**Proposition:** Fix $0\le a<1/2$, a smooth compact position cutoff $\rho$, and $f=b'$ with $b$ smooth and compactly supported in $(0,\log 2)$. Use the real whole-line metric $w_a(x)\,dx=e^{2a|x|}(1+x^2)^2\,dx$. At level $j\ge1$, let $Q_j$ project onto the span of $2e^{-x/2}\lfloor k\{2^{-j}e^x\}\rfloor$, $2\le k\le4^j$. For every finite physical orthonormal basis of $\operatorname{ran}(Q_{j+1}-Q_j)$, split each physical profile $p$ as $c(p)2e^{-x/2}$ plus its centered part, where $c(p)$ is the flat unit-period mean of the phase factor after division by $2e^{-x/2}$. The mean–mean term of $\operatorname{Tr}(M_\rho A_{b'}(Q_{j+1}-Q_j))$, with ordinary $x-z$ convolution, is
$$
-2\left(\int \rho(x)w_a(x)e^{-x}\,dx\right)
\left(\int b(z)e^{z/2}\,dz\right)(E_{j+1}-E_j),
$$
where $E_j$ is the squared norm of the flat phase mean restricted to level $j$ in the whole-line metric.

**Source and payoff:** The original setup is `cmd/ffring/graph.go` (`problem`). The Lean definition chain is `FloorGridPhysical`, `FloorGridLevels`, `FloorGridPhaseMean`, `FloorGridMeanKernel`, and `FloorGridLocalSplit` from `b94932515fa376b18419217beb940a248ffe6edc`, with `Masullo.floorGridDetail_trace_split` and `floorGridMeanPartial_eq` in `Proofs/Theorems/FloorGridMeanObstruction.lean` from `1ac7e41bd8d353968bfaae498f99526d9c84d203`. This is the finite identification used by the [closed separate-convergence card](../closed/rational-floor-grid-two-leg-mean.md); it is not a second separate-convergence claim or a claim about the limit of the recombined trace.

**Discriminating test:** Reconstruct the weighted finite-rank diagonal from the original cutoff and convolution, independently expressing the physical legs by division by $\sqrt{w_a}$ and the fine-shell mean by the Jacobian $2^{-j-1}e^x\,dx$. In a scratch Lean client of the exact revision, test the public trace split against the resulting explicit integral and the three literal remaining pairings, and test the literal mean–mean integral against the signed energy increment for an arbitrary detail basis. An uncompensated weight, phase-period factor, convolution shift, or exponential normalization should prevent that application.

**Proof at fixed cutoff.** Multiplication by $\sqrt{w_a}$ is an onto isometry from the physical space to $L^2(dx)$. It sends the specified columns to `floorGridColumn` and takes the physical detail projector to the fine projector minus the coarse projector (`floorGridDetail_projection`). Write $v_i=\sqrt{w_a}\,p_i$ for the transported basis. The finite-rank trace is the sum of the detail diagonals: The projector kills the orthogonal complement. Its $i$th diagonal is
$$
\int \rho(x)w_a(x)p_i(x)\int b'(z)p_i(x-z)\,dz\,dx.
$$
There is no weight at $x-z$. The cutoff and bump localize both variables, so splitting the legs does not require the mean profile to belong to the whole-line Hilbert space.

Set $J=j+1$. With $t=2^{-J}e^x$, integrate $p_i(x)/g(x)$ against $dt$ over $1\le t\le2$, where $g(x)=2e^{-x/2}$. This gives the flat fine mean $c_i$. On the old span the phase factor is periodic in $2t$, so the two coarse periods counted on this shell are exactly compensated by $dt=d(2t)/2$. Thus the projection of the fine mean's Riesz vector onto the old level represents the old mean. Pythagoras and Parseval on the orthogonal detail give $\sum_i c_i^2=E_J-E_j$ for the chosen basis. In the diagonal with both legs replaced by $c_i g$, their product is $4c_i^2 e^{-x}e^{z/2}$. Integration by parts against $b'$ contributes the factor $-1/2$, with no boundary term. Summing proves the displayed identity.

**Independent application.** A scratch Lean 4.36.0 client of the pinned six modules defined $p=v/\sqrt{w_a}$, the shell integral, and $A_{b'}$ directly. For a symbolic orthonormal basis of the fine level intersected with the old orthogonal complement, `floorGridDetail_meanPair_sum` gave the claimed scalar for the literal two-mean integral. `floorGridDetail_trace_split` gave that scalar plus the two mixed pairings and the centered–centered pairing for the diagonal with outer factor $v_i(x)\sqrt{w_a(x)}\rho(x)$. Both client lemmas reported only `propext`, `Classical.choice`, and `Quot.sound`. This identifies the terms telescoped by the separate-convergence card; it gives no limit for their recombination with the remainder.
