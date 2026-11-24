# A common short vector recovers every split in a filter

Keep the exceptional splits and dyadic bins of the [two-minor count](normal-factor-minors.md) on one actual list. Write $n=(a,b,c)$ for the primitive, untransformed normal. Let $\rho(n)$ be the minimum Euclidean length of a nonzero vector of the **saturated** integral plane $n^\perp\cap\mathbb Z^3$ after coordinatewise division by $(V,H,H)$. All exceptional triples with

$$\rho(n)\le q^{-.229}$$

together cost at most $q^{1.1355+o(1)}$, without a bound on $a/(F,a)$. This is a charge over all their occupied splits. A short vector need not itself represent an input or have a smooth first coordinate.

**An annihilator identity.** Use $A=(P,g)$, $B=(Q,g)$, $AB=g$, with $(A,B)=1$ and $(a,g)=1$. Since $A\mid c$, $B\mid b$, and $g\mid qa+F(b+c)$, for *every* integral vector $u=(m,x,y)$,

$$F(n\cdot u)\equiv a(Fm-qx)\pmod A,\qquad F(n\cdot u)\equiv a(Fm-qy)\pmod B.$$

In particular the saturated plane satisfies the two primal congruences modulo $A,B$, even if it does not satisfy them modulo $P,Q$. Conversely, choose filters $f_A\mid A$, $f_B\mid B$, $d=f_A f_B$. Every vector satisfying the primal congruences modulo these filters pairs to a multiple of $d$ with **every** represented normal in the filter, since $(F,d)=1$. This conclusion concerns the untransformed normal, not $(a/(F,a),b,c)$.

**Freeze one witness before counting the fiber.** In bins $R\le R_0<2R$, $J\le\lambda<2J$, group planes with $\rho(n)\le U$. For the claimed bound use $U=q^{-.229}$. Each rescaled dual normal has length

$$\|(Va,Hb,Hc)\|_2=VH^2/(\lambda R_0)\le VH^2/(JR).$$

Set $D=\max(1,2VH^2 U/(JR))$. For each split take divisors $f_A,f_B$ by first strictly crossing $\sqrt D$ in $A,B$ separately. They are available: Here $r=\log_q R\ge .446-o(1)$, $0\le j=\log_q J\le .334+o(1)$, and each side has exponent at least $1.212-j-o(1)$, greater than $(2.271-r-j)/2+o(1)$. The ordered filters cost $q^{o(1)}\sqrt D$ by the smooth half-power bound, overshooting $D$ in the product only by a subpower.

Within each occupied filter, fix one *actual represented split*, and take one shortest vector $u$ in its scaled saturated plane, written in the original integral coordinates. The identity puts $u$ in the primal congruences modulo the filters. For every other represented $n$ in the bin, Cauchy-Schwarz now gives

$$d\mid n\cdot u,\qquad |n\cdot u|\le VH^2 U/(JR)<d.$$

Thus $u$ lies in **all** these planes. No count of independent shortest vectors, their span in the filtered lattice, or reference choices is needed. Applying the identity with each full $A,B$, we have $A\mid Fm-qx$, $B\mid Fm-qy$. Both recovery integers are nonzero: $|x|,|y|\le HU<F$, and $Fm=qx$ would give $F\mid x$, hence $x=m=0$; the reference plane then gives $cy=0$. Here $c\ne0$ since otherwise $B\mid qa$ (use $B\mid b$), contradicting $(qa,B)=1$ and $B>1$. The other case uses $b\ne0$ in the same way. The two integers have polynomial height, so there are only divisor-many full pairs $A,B$ in the fiber. This charges the fiber once, not one outgoing count per choice of reference.

Enumerate smooth $\lambda<2J$, recover the ordered $P,Q$ from $PQ=AB\lambda$ by divisors, and use the actual per-split price $q^{o(1)}\sqrt R$ from the [divided projection](global-double-ratio.md). Thus the total per bin is at most

$$q^{o(1)}\sqrt{DRJ}\ll q^{o(1)}\big(\sqrt{RJ}+\sqrt{VH^2U}\big).$$

Here $RJ\le H^2/a\le H^2$, and $VH^2=q^{2.500+o(1)}$. Summing dyadic bins proves the assertion. Taking one reference per filter is legitimate for this upper bound; the argument does not give the same total for all ordered pairs of references and targets.

**What remains near the cutoff.** The scaled saturated plane has covolume $1/(\lambda R_0)$, not $1/R_0$. The area bound for a shortest disk (disjoint disks of radius $\rho/2$ modulo the lattice) gives $\rho\ll(RJ)^{-1/2}$. Using that upper bound for $U$ above is affordable on each side ($\sqrt D$ has exponent at most $1.25-.75(r+j)+o(1)$) but yields only $1.25-(r+j)/4$ in the second term, or $1.1385$ at $r+j=.446$. Thus a generic shortest-vector theorem alone does not pass the budget. Combining the two *proved* cuts leaves $a/(F,a)>q^{.323}$ and $q^{-.229}<\rho\ll q^{-.223+o(1)}$ in the difficult bins. Neither necessity proves occupancy.

At the cheaper filter size $d\asymp q^{2.271+o(1)}/(RJ)$, the same frozen shortest vector in the remaining family gives integer layers $k=(n\cdot u)/d$ of size $\ll q^{.229+o(1)}\rho\le q^{.006+o(1)}$. The zero layer is recovered by the two nonzero divisors above. The nonzero layers are **not** central planes of normals. For them the identity gives $A\mid a(Fm-qx)-Fdk$ and $B\mid a(Fm-qy)-Fdk$ with varying $a$; fixing $k$ does not fix either integer. An average of at most $q^{.0005-\eta}$ represented image indices per potential filter, counting all the nonzero layers together for some fixed $\eta>0$, would suffice at this filter size. Counting layers alone does not establish it. The ordinary labels outside the exceptional class still need a separate estimate.

For the nonzero-layer handoff see [the primal witness price](primal-witness-price.md): The whole-fiber multiplicity at the cheap height costs at most $q^{.006+o(1)}$ even though one layer does not fix the recovery integers. A sufficient remaining test concerns the frequency of filters with independent witnesses; its required saving is not proved.
