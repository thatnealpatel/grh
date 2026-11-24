# Delete-33 with all real first shifts at depth 1.95001720

In the [(10,2) comparison](unfolded-deletion-33.md), keep the three second shifts $(-7,6,19)/25$ at $3t$. One common prime law at $c=1.95001720$ matches **every real first translate at both heights**, gives zero on all three second replies simultaneously and on orders two through ten at $t$, and has failure mean greater than $8/9+2\cdot10^{-8}$. Thus every finite real-coefficient refit in this class has priced margin less than $-2\cdot10^{-8}$. This improves the depth from $1.95005$, not to $1.95$. It is an obstruction to separation in the comparison, not a statement about the existence of arithmetic failures.

All changes below start from the same [426-slab law](deletion-laws/delete-33-unfolded-seed.txt). Write $X=2u^2-1$, $T(X)=4X^3-3X$, and $(A,B,U)=(\mathbb E X,\mathbb E T(X),\mathbb E u)$ on each slab. Extend the last row to infinity. The failure mean is $M=\int z_+ e^{-z}U(z)\,dz$. Keep the seed convention $X=0$ to the left of the first knot.

| Depth | Change to seed | Surplus over $8/9$ | Upper bound on the all-real $t$ norm |
|---:|---|---:|---:|
| 1.950025 | Local $u=1$ mixture on eight slabs | $>3.1431\cdot10^{-8}$ | $<.9999997$ |
| 1.950020 | [Six fixed-$B$ replacements](deletion-laws/delete-33-six.pairs) | $>5.9999\cdot10^{-8}$ | $<.999999775$ |
| 1.95001720 | [66 fixed-$B$ replacements](deletion-laws/delete-33-front.pairs) | $>2\cdot10^{-8}$ | $<.999999775$ |

## Price the one-atom repair before widening the search

Let $G_A(0)=\int e^{-z/2}A(z)\,dz$, and $C_t(c)=\cosh(c)/(6\cos(\pi/12))$. The seed has deficit $d=8/9-M\approx3.26793\cdot10^{-6}$. Replacing a uniform fraction $e$ of every nonnegative slab by $u=1$ gains $e(1-M)$, so $e\ge d/(1-M)$. Substituting even this least fraction in $G_{A'}(0)\le C_t(c)$ forces $c>1.95004662$.

Now allow an arbitrary measurable fraction $0\le e(z)\le1$ on $z\ge0$. The gain and cost densities are $e(z)z e^{-z}(1-U)$ and $e(z)e^{-z/2}(1-A)$. Where $A=1$, $U=1$ too. Else their ratio (with the common factor removed) is at most

$$\eta=\max_I\sup_{z\in I,\ z\ge0} z e^{-z/2}\frac{1-U_I}{1-A_I}<.194884.$$

The maximum of $z e^{-z/2}$ occurs at $2$ clipped to the slab, including the infinite last slab. Therefore $C_t(c)\ge G_A(0)+d/\eta$ is necessary for this entire family under the unfolded cap. This forces $c>1.95002400$; a finer subdivision alone cannot overcome this price. The first row of the table nearly attains it: Replace fraction $37/100000$ by $u=1$ on $47/25\le z<11/5$ and nowhere else. This changes $B$ too. The full check at this depth gives $\|V_B\|_\infty<.99999$ and repaired multiplier slack $> .00031$. The floor is **not** a lower bound for arbitrary prime laws, or even for mixtures with other atoms on this mesh.

## Preserve the input to the three-site problem, not both first fields

Each row $(400z,i,j,q)$ of a `.pairs` file replaces fraction $q/10^{12}$ of the original row by a two-point law on $u=i/10^9,j/10^9$. Let $b_i=T(2(i/10^9)^2-1)$ and similarly for $j$. Put mass $(B-b_j)/(b_i-b_j)$ on the first atom and the complement on the second. The checker verifies nonnegativity, normalization by construction, and exact rational equality to the original $B$. The six-row law changes just one nonnegative slab, the infinite slab starting at $4.4$. The five negative slabs contribute nothing to $M$ but change the whole $t$ field. The search used linear cuts of the $t$ cap and exchanged frequencies; it did not solve a new three-site problem in each iteration. Some early candidates passed at the old maxima but failed between them. The certificates use the actual rational mixture, not the LP objective.

At $c_0=39/20$ the checker verifies the **unmixed seed** $3t$ first field has norm $<.99990$. It applies the [exact three-site completion](unfolded-deletion-33.md#exact-three-site-completion) to that field: The degree-192 polynomial, corrected by the inverse weighted Gram matrix, has slack $> .000059$. Thus there is one conditional circle law with the specified first moment and all three integrated second moments zero. For $c\ge c_0$ mix this law at every frequency with Haar measure, retaining fraction $\cosh(c_0)/\cosh(c)$. The first moment scales exactly as $1/C(c)$, and each zero second reply stays zero. This is why we need only one $3t$ check for both fixed-$B$ refits. It does not transfer a certificate from a larger depth to a smaller one.

At $t$, bound $|V_A|$ on the full frequency line using the cubic Taylor test on intervals, reflection, and the analytic outer-ray bound; then use the twelve-angle construction as in the unfolded proof. For the six- and 66-row recipes the positive tails begin at 74 and 73 respectively. Computing $M$ includes the infinite last slab. Replay with SageMath 10.9, assertions enabled, from the repository root:

```sh
/opt/sage-10.9/bin/python .godel/bob/check-priced-deletion-33.py
```

**Next experiment at exactly $39/20$.** Start from the six-row recipe, not the uniform one-atom repair. Insert an interior knot (for example one unit beyond the start on the infinite slab), and vary the *replacement fraction* separately on the two pieces while keeping the same $B$-preserving atom pair. The two half-slab Fourier responses differ although $B$ stays constant. Price their signed difference against the active $t$ cuts and the failure deficit, with both fractions in $[0,1]$. A candidate needs the full $t$ cap and positive surplus; if the directions cannot pay, widen the law or release $B$ rather than certifying more intermediate depths. Neither the fixed-$B$ target nor the unrestricted comparison at $39/20$ has been decided. The unrestricted three-versus-four minimum and the signed arithmetic lower bound remain open.
