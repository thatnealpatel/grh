# Count the normals on the common component

For the $1.1354$ parent budget, use the
[smaller-filter upgrade](exceptional-visible-filters.md): It pays all
exceptional splits at $q^{1.1345+o(1)}$, not just those in a sub-bin.

On one actual two-label list, the residual ordered triples on **all exceptional visible splits** of the [two-minor count](normal-factor-minors.md) cost at most $q^{1.1355+o(1)}$, below the $q^{1.136}$ budget. On the cheap filters where a population bound was missing, each filter represents only $q^{o(1)}$ distinct image indices, counting all pairing layers together. This is a pointwise upper bound, not a density hypothesis on filters.

The [two independent sextics](cheap-filter-kernel.md) matter: Their common factor has degree at most five. We show that an irreducible factor of degree $2\le e\le5$ through both specified points contains at most $9e$ distinct actual projective points. The two known roots on the joining line give an integral divisor of the **first nonzero coefficient** of the restriction, even if its other roots and its content are unknown. To make this useful for a quintic we first bound the size of its equation in the metric of the normal box.

## Inputs and bins

Use $T=RJ=q^\sigma$, $s=(F,a)$ fixed, $a'=a/s$, $F'=F/s$, $X=H^2/T$, and $Y=VH/T$. Write $x=(a',b,c)$ and scale it by $S=\operatorname{diag}(1/X,1/Y,1/Y)$ so actual normals have bounded norm. In a cheap filter let $d=f_A f_B=Yq^{.161+o(1)}$, with $f_A,f_B$ coprime, of equal exponent, and prime to $q$. Take the **entire** lattice

$$L_d=\{x\in\mathbb Z^3:f_B\mid b,\ f_A\mid c,\ d\mid qa'+F'(b+c)\}.$$

Its index is $d^2$. Put $\Gamma=SL_d$ and $\delta=\det\Gamma=d^2/(XY^2)$. Thus $\delta^{-1}=q^{\psi+o(1)}$, where $\psi=.458-\sigma$. The rational projective coordinates on the unsized lattice are $w=(K,C,B_0)=((qa'+F'(b+c))/d,c/f_A,b/f_B)$. The specified points are the $B_0$- and $C$-axes. Their joining line is $K=0$ in characteristic zero, not the line used in the bad-reduction test.

It suffices to take $.446-o(1)\le\sigma\le.458$. For $\sigma\ge.458$ the existing two-minor price is $q^{1.055+o(1)}X^{1/4}\le q^{1.1355+o(1)}$. For clarity the sextic-kernel input extends from $.457$ up to $.458$ without a cut on $a'$: Here $j=\log_q J\le.012+o(1)$, so both first crossings are available and each omitted factor has exponent at least $1.212-.012-(2.271-.446)/2-o(1)>.28$. Their product still has exponent at least $.153+\log_q R-o(1)\ge.599-o(1)$. The bounds $|K|\le q^{.619+o(1)}$, $|K'|=q|a'|/d\le q^{-.491+o(1)}$, and $|B_0|,|C|\le q^{.9745-\sigma/2+o(1)}$ follow from $X,Y$ as before. The degree-six completion exponent $E_6(25;\sigma)$ decreases with $\sigma$, starting at $-.111+o(1)$. Thus the same pair of independent sextics applies whenever the represented points span three dimensions. Components missing either specified point are payable by the omitted-divisor test ($6XY^2/d^2\le q^{.012+o(1)}$), and lines or rank at most two by the two nonzero minors ($dF'>2XY$ since $F'\ge q^{.760-o(1)}$). Off the common factor there are only boundedly many points by Bézout. We need no reduction hypothesis on the remaining factor.

## A small equation if there are many actual points

Fix one rationally irreducible component of degree $2\le e\le5$ through the two points. Use any lattice basis of $\Gamma$ to give coordinates $z$ on scaled real space; the changes from $w$ to $z$ are rational since the scaling cancels. Let $G$ be the primitive integral equation in $z$. When taking real coefficient norms below, use **orthonormal scaled box coordinates** $\xi=Sx$, not the lattice basis. We bound this norm of the same equation (no further rescaling of its scalar).

Let $\mathcal P_n$ be the coefficient lattice of homogeneous forms of degree $n$ integral in the $z$-basis, expressed in the ordinary monomials in $\xi$. Its Euclidean covolume is $\delta^{-\binom{n+2}{3}}$: The determinant of the degree-$n$ monomial substitution is the determinant of the linear substitution to the power $\binom{n+2}{3}$. For diagonal substitutions this is the sum of the exponents of one variable; triangular shears have determinant one and permutations preserve absolute determinant.

Take $n=9$. Evaluate at a maximal independent set of evaluation rows of actual points **on the component**, using their bounded representatives in $\Gamma$, and call the map $J$ of rank $k$. Its image on $\mathcal P_9$ is a full-rank sublattice of $\mathbb Z^k$, hence has covolume at least one. As a real map in the $\xi$ monomials, its $k$-dimensional Jacobian on $(\ker J)^\perp$ is $O(1)$, since each row is bounded and the degree is fixed. Consequently

$$\det(\mathcal P_9\cap\ker J)
=\frac{\det\mathcal P_9\; |\det(J|_{(\ker J)^\perp})|}{\det J(\mathcal P_9)}
\ll \delta^{-165}.$$

Indeed, extend a basis of the kernel lattice by lifts of an image basis; their perpendicular projections give the complementary volume. The kernel dimension is at least $\binom{9-e+2}{2}\ge15$, by multiples of $G$. Minkowski's first theorem in the kernel gives a nonzero form $A$ annihilating **all** actual points on the component, with real coefficient norm $\ll\max(1,\delta^{-11})$.

If there are more than $9e$ distinct projective points there, then $G\mid A$ by Bézout. For rational forms a common geometric factor of $G$ and $A$ would give its whole conjugacy orbit in both, so rational irreducibility suffices. By Gauss's lemma write $A=GB$ with $B$ integral in lattice coordinates. The real coefficient norm of $B$ is bounded below by a fixed positive constant: Evaluate on the grid of combinations of **three independent actual points in the filter** with coefficients $0,\ldots,9$. All are bounded lattice points. Some evaluation of $B$ is nonzero by successive interpolation, and then its absolute value is at least one by integrality. Finally $\|GB\|\gg\|G\|\,\|B\|$ in ordinary real coefficient norms: On the product of the two fixed-degree unit spheres multiplication has positive minimum norm since there are no zero divisors. Thus the primitive equation itself satisfies

$$\|G\|_{\xi}\le q^{11\psi+o(1)}.$$

Using maximal minors just in degree $e$ does not give this uniform quintic price. We used the volume of the whole lattice of possible degree-nine equations and divided out a factor of controlled *lower* norm.

## The integral binary factor on the joining line

In unscaled coordinates, a basis of $L_d\cap\{K=0\}$ is

$$v_1=(0,d,-d),\qquad v_2=(F',b_2,c_2),\qquad b_2+c_2=-q.$$

Choose $f_B\mid b_2$, $b_2\equiv-q\pmod{f_A}$ with $|b_2|\le d$, and set $c_2=-q-b_2$. Indeed $qa'+F'(b+c)=0$ implies $F'\mid a'$; after subtracting $(a'/F')v_2$ only a multiple of $v_1$ remains. These vectors have scaled norms at most $q^{.161+o(1)}$ and $q^{\sigma+o(1)}$, respectively, since $F'/X\le q^{\sigma+o(1)}$ and $(q+d)/Y\ll q^{.161+o(1)}$.

Restrict $G$ to $S(x_1v_1+x_2v_2)$, obtaining an integral binary form $D_e(x_1,x_2)$. It is not identically zero by irreducibility and $e\ge2$. The restrictions of $C$ and $B_0$ are

$$U=-f_B x_1+(c_2/f_A)x_2,\qquad W=f_A x_1+(b_2/f_B)x_2.$$

Both are primitive: $c_2\equiv-q\pmod{f_B}$ and $b_2\equiv-q\pmod{f_A}$. Their coefficient determinant is $q$, so they are distinct in characteristic zero, though proportional modulo $q$. Their zeros are the two specified points. Consequently $D_e=UW D_{e-2}$ with $D_{e-2}$ **integral and nonzero**, including any content of the restriction. If $i$ is the smallest $x_2$-degree with nonzero coefficient in $D_{e-2}$, the coefficient of $x_1^{e-i}x_2^i$ in $D_e$ is $-d$ times that nonzero integer. In particular $i\le e-2$ and its magnitude is at least $d$. For a cubic this prices the third root without a height assumption: If the residual linear form is $m(ux_1+vx_2)$ with $(u,v)=1$, the first coefficient costs $d|mu|$ when $u\ne0$, or $d|mv|$ in the next slot when $u=0$. A large content or a repeated root cannot lower the price.

On the many-points hypothesis, expansion in the scaled coordinates bounds the same coefficient by

$$O(\|G\|_\xi\,\|Sv_1\|^{e-i}\|Sv_2\|^i)
\le q^{11(.458-\sigma)+2(.161)+3\sigma+o(1)}.$$

Here $i\le e-2$ and $e\le5$, with $\sigma>.161$. At $\sigma=.446$ the exponent is $1.792$, whereas $\log_q d=2.271-\sigma+o(1)=1.825+o(1)$. The difference (upper bound minus divisor exponent) decreases with slope $-7$ as $\sigma$ increases. This contradiction proves the $9e$ point cap. For the cubic alone, take $n=e=3$: The coefficient covolume is $\delta^{-10}$, and kernel dimension at least one suffices. More than nine points would force the same divisibility by Bézout, with the smaller norm exponent $10\psi$, so **nine points suffice as an upper bound**. The determinant $q$ of the two roots alone would not give the coefficient bound; it is their product $-d$ in the **short direction of the integral line lattice** that is large.

## Charge and next decision

Each fixed projective point fixes at most one primitive oriented $(a',b,c)$, and $g$ divides its fixed nonzero $qa'+F'(b+c)$. Together with the payable factors and the points off the common component this gives divisor-many distinct $g$ on every filter. The $q^{o(1)}\sqrt{Yq^{.161}}$ potential filters, the $q^{o(1)}\sqrt J$ smooth complementary indices per $g$, the divisor choices for ordered $P,Q$, and the $q^{o(1)}\sqrt R$ actual triples per split give $q^{1.1355+o(1)}$ in total after summing the subpower many bins. No choice of an auxiliary equation, lattice basis, or reference is charged to a separate copy of the fiber.

The [ordinary global labels](global-double-ratio.md) are not counted by this result. A next test is to split their occupancy by $J_0=C_+C_-\asymp q^t$, $0\le t\le.466+o(1)$. If $N_t$ counts distinct ordinary global $L$ in a bin, the known pointwise multiplicity there is at most $q^{\min(t/2,.223)+o(1)}$: One can recover the hidden factors at the first price or use the ordinary visible split at the second. Thus $N_t\le q^{1.136-\min(t/2,.223)-\eta}$ uniformly for some fixed $\eta>0$ suffices, with threshold $.913-\eta$ at the large-$t$ end. The existing signed-pivot estimate on one prescribed valuation space is not such a count over all labels. Test this on ordinary splits using both actual rows before returning to the unrestricted $q^{.998}$ incidence target. The [ordinary outside-product count](ordinary-outside-product.md) now pays for labels with bounded product off a prescribed pool and gives a two-row necessary condition on any over-budget bin. The complementary labels remain uncounted.
