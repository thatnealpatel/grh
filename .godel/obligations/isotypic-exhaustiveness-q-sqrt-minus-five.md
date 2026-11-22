# Archimedean exhaustiveness on one ideal-class isotype

**Result (ordinary mathematics, not Lean):** For $F=\mathbb Q(\sqrt{-5})$,
$S=S_\infty$, $S'=S\cup\{\mathfrak p\}$ with $\mathfrak p$ the prime over
$2$, and $\chi$ the nontrivial unramified ideal-class character, the
projected insertion $f\mapsto f\otimes 1_{O_{\mathfrak p}}$ is a linear
topological isomorphism from the trivial $S$-isotype to the $\chi$-isotype
at $S'$. Here $\operatorname{Pic}(\mathcal O_{F,S})$ is nontrivial. This also
supplies the isotypic identification (6.3.2.9) at $S$ for this character,
by composing with the manuscript's theorem at the principalizing stage
$S'$; a direct global check below does not require that theorem. This is
not a generalization of the unprojected Fourth Structure Theorem.

## What the manuscript uses

Source locations below are from layout extraction of the [pinned
edition](../sources/masullo/README.md), not independent visual review.
Theorem 6.2.1.1(1), p. 295, assumes $\operatorname{Pic}(\mathcal O_{F,S})=1$.
Its proof, pp. 296–297, passes through the unit-invariant range of the
Fourth Structure Theorem, 6.1.2.1(1), p. 288. In that proof (6.1.2.11),
pp. 290–291, identifies the whole new local valuation lattice with the
relative $S$-unit group. The Fifth Structure Theorem also uses the group
identification (6.2.1.1) on p. 297. In the case below those identifications
cannot be used: The relative units see only even valuations, and the
norm-one quotient by the new local units has a second component.

The isotypic insertion to test is instead the quotient map of (5.2.3.1),
pp. 233–234, with the Euler multiplier in (5.2.3.4). In terms of projected
functions it means **project after insertion**, not restrict the
unprojected map and assume that it lands in the single target isotype.
This is the distinction in the diagram (5.2.3.15), p. 236. The Mellin
kernel statement needed is Lemma 5.1.2.2(2), pp. 225–226, on the one
character component, not faithfulness of a single component on the
unprojected space. The earlier rational stage and Mellin work, including
[`RationalAdeleStageTransition`](../../Proofs/Props/RationalAdeleStageTransition.lean)
and [`RationalThetaMellin`](../../Proofs/Theorems/RationalThetaMellin.lean),
does not test this class-character distinction. The main program's
subsequent [number-field right-line majorant](hecke-right-line-majorant.md)
concerns absolute convergence of prime-power sums, not insertion.

## The missing valuations and the target character

The ring of integers is $\mathbb Z[\sqrt{-5}]$, with discriminant $-20$.
The ideal $\mathfrak p=(2,1+\sqrt{-5})$ is the unique prime over $2$, has
norm $2$, and $\mathfrak p^2=(2)$. It is not principal: The equation
$a^2+5b^2=2$ has no integral solution. The imaginary quadratic Minkowski
bound $(2/\pi)\sqrt{20}<3$ shows that every class is represented by an
integral ideal of norm $1$ or $2$, so the class group has order two and
$\mathfrak p$ generates it. Thus $\mathcal O_{F,S}^\times=\{\pm1\}$,
$\mathcal O_{F,S'}^\times=\{\pm2^n:n\in\mathbb Z\}$, and the image of
$v_{\mathfrak p}$ on the relative units is $2\mathbb Z$. Inverting
$\mathfrak p$ kills the class group.

View $\chi$ as a character on idèles via the fractional ideal of the
finite valuations. It is trivial at the complex place and on all finite
unit groups, and $\chi_{\mathfrak p}(\varpi)=-1$ for a uniformizer $\varpi$.
It is nontrivial on the norm-one idèle classes: The $\mathfrak p$-uniformizer
idèle can be adjusted to norm one at infinity without changing $\chi$.
At $S'$, after quotienting by the finite units, the variables are
$(z,n)\in\mathbb C^\times\times\mathbb Z$ modulo $(\pm1,0)$ and $(2,2)$.
The norm is $|z|^2 2^{-n}$ and $\chi(z,n)=(-1)^n$. At norm one the quotient
is $(U(1)/\{\pm1\})\times \mathbb Z/2$: Record the argument of $z$ and
parity of $n$. The natural archimedean inclusion lands in the even
component, on which $\chi$ restricts trivially. Triviality on local units
does not make the two components identical.

## The transform and its actual span

Write $B_m=\varpi^m O_{\mathfrak p}$ and $b_m=1_{B_m}$ for $m\in\mathbb Z$.
Use $c_s=\chi|\cdot|^s$, with $|z|_\infty=|z|^2$ and
$|\varpi|_{\mathfrak p}=2^{-1}$. Put $u=\mu_{\mathfrak p}(O_{\mathfrak p}^\times)>0$
for multiplicative Haar measure. For $\Re s>0$, summing the valuation
shells gives

$$
Z_{\mathfrak p}(b_m,c_s)
 = u\sum_{n\ge m}(-2^{-s})^n
 = \frac{u(-1)^m2^{-ms}}{1+2^{-s}}.
$$

For every $f\in\mathcal S(\mathbb C)$, set
$D_m f(z)=(-1)^m f(2^{m/2}z)$. Multiplicative Haar invariance and the
squared complex norm give $Z_S(D_m f,s)=(-1)^m2^{-ms}Z_S(f,s)$.
Consequently, with the same archimedean Haar measure at both stages,

$$
Z_{S'}(f\otimes b_m,c_s)=Z_{S'}(D_m f\otimes b_0,c_s).
$$

This is exact for every integral $m$, including odd and negative $m$.
The sign is essential for odd $m$: They are precisely the valuations
missing from the relative units.

The algebraic Schwartz–Bruhat tensor description (2.1.4.1), p. 71,
gives finite sums of tensors at $S'$, not just a dense subspace. In
particular, a fixed compact support and local-constancy level in the
finite variable give a finite tuple of complex Schwartz profiles. Haar
probability averaging over $O_{\mathfrak p}^\times$ does not change the
$\chi$-projected class or its transform: The character and norm are
trivial there. A radial locally constant compact test vanishes for
valuations sufficiently negative and is constant for valuations
sufficiently positive, so its successive differences are finitely
supported, and it is a finite linear combination of the $b_m$. Thus
these tensors really do span the projected target.

If “ball translate” means an **additive** translate, it need not match
one signed dilation. For $a+B_m$ with $k=v_{\mathfrak p}(a)<m$, unit
averaging gives $(b_k-b_{k+1})/2^{m-k-1}$: The unit group acts transitively
on the $2^{m-k-1}$ balls of that radius in the shell. This is matched
by $(D_k-D_{k+1})f/2^{m-k-1}$ in the insertion. For example,
$1_{1+B_1}=b_0-b_1$ has multiplier $1+2^{-s}$ relative to $b_0$, not a
single dilation multiplier. If $a\in B_m$, the ball is just $B_m$.

## Why Mellin equality suffices, and the topology

At either stage $T=S,S'$, periodize a test by $\mathcal O_{F,T}^\times$
on the multiplicative group, then project by Haar probability on the
compact norm-one group $J_{F,T}^1$ with the character $\chi_T$. Its image
is the isotype, and the projected Schwartz quotient is defined by the
kernel of this periodization and projection. This is the setup of
Definition 2.3.1.1, pp. 99–100, and Proposition 5.2.3.2, pp. 236–237.
For $\sigma>0$ the local test integral weighted by $|\cdot|^\sigma$ is
absolutely convergent (complex Schwartz decay, boundedness at zero, and
a geometric finite-place tail). Unfolding against $c_s$ gives the same
integral of the projected periodization on $J_{F,T}$: The character is
trivial on the diagonal units, and the projection preserves this
character integral. The absolute weighted $L^1$ bound follows by
unfolding the absolute value bound before projecting, since norm-one
translations do not affect the weight.

The norm section $t\mapsto(\sqrt t,1)$, omitting the finite entry at
$S$, has $\chi_T=1$. The isotypic periodization $H$ is determined by its
profile there. With $x=\log t$, its transform on $s=\sigma+i\tau$ is,
up to a nonzero Haar constant, the ordinary Fourier transform of
$x\mapsto e^{\sigma x}H(\sqrt{e^x},1)\in L^1(dx)$. Vanishing on that
line forces this profile to vanish everywhere by Fourier uniqueness
and continuity. This checks the exact faithfulness required by
(5.1.2.4) here without meromorphic continuation or a class-number-one
assumption.

On the source quotient the insertion therefore descends, and the
factor $u/(1+2^{-s})$ shows it is injective. The lifts above show it is
surjective. It is continuous for the Schwartz quotient topologies, and
so is its inverse: On each fixed finite test level, average units,
expand in the finitely many $b_m$, and apply the finite sum of $D_m$ to
the archimedean profiles. This is continuous on the finite tuple of
Schwartz spaces and hence on their locally convex inductive limit.
Mellin faithfulness and the nonzero Euler multiplier show that the
resulting map to the source quotient kills the target kernel. Thus it
descends continuously and is the inverse of the projected insertion.

## Scope and next check

The projected finite-stage result is new here, not a reading of a
Picard-free statement in 6.2.1.1. The unprojected range need not follow:
For example, $f\otimes b_1$ with a nonzero archimedean Mellin transform
is unit-invariant but cannot have the same unprojected theta class as
$h\otimes b_0$. Testing at the trivial and sign components would force
$Z_S(h,s)=2^{-s}Z_S(f,s)$ and $Z_S(h,s)=-2^{-s}Z_S(f,s)$ simultaneously.
This is only a scoped failure of dropping the hypothesis in the
unprojected range statement, not a counterexample to either printed
structure theorem with its hypotheses.

The independent review also checked that (6.2.1.1) cannot be replaced by
unprojected inclusion of homogeneous functions. If a radial bump $f$ is
supported in $3/4<|z|^2<5/4$ with $f(1)\ne0$, the inserted unprojected
theta takes values $2f(1)$ at $1$ and zero at the norm-one odd class
$(\sqrt2,\varpi)$. It is not $\chi$-homogeneous. This failure is distinct
from non-surjectivity of the unprojected range illustrated above.

Because $\operatorname{Pic}(\mathcal O_{F,S'})=1$ and $\chi$ is unramified
outside $S'$, Theorem 6.2.1.1(2) at $S'$ supplies the cited map from there
to the global $\chi|_{C_F^1}$-isotype. The projected insertions compose
(they are induced by the same tensor insertions on representatives), so
(6.3.2.9), p. 305, is already an isomorphism at $S$. The norm section can
also be chosen to lie in the image of $S$.

The same conclusion can be checked directly on the global quotient.
Take the product multiplicative Haar normalized to give the local units
mass one at almost all finite places. The global archimedean
insertion has Mellin multiplier the product of the omitted local
$b_0$ integrals. On $\Re s>1$ this product converges absolutely and is
nonzero: At most two places lie over each rational prime $p$, each with
$q_v\ge p$, so $\sum_v q_v^{-\Re s}<\infty$, and the unit masses differ
from one at only finitely many places. The absolute unfolded integral
for any fixed adelic test is finite on this line by the same product
bound and the finite-stage estimates. The norm-section Fourier argument
then gives faithfulness on the global projected quotient as well.

Every adelic test belongs to some finite stage. Unit averaging and the
finite ball expansion at that stage reduce it to terms with valuation
tuple $(m_v)_v$ at finitely many finite places. For such a term the
multiplier relative to the global archimedean insertion is
$\prod_v \chi_v(\varpi_v)^{m_v}q_v^{-m_v s}$. This is exactly the Mellin
multiplier of scaling the argument of the complex Schwartz profile by
$(\prod_v q_v^{m_v})^{1/2}$ and multiplying the profile by
$\prod_v \chi_v(\varpi_v)^{m_v}$. This lift is compatible with stage
enlargement, which appends valuation index zero. It is continuous on
each block and descends as before, giving a continuous global inverse.
This independent check confirms the identification but does not identify
$C_{F,S}$ with $C_F$ or supply the subsequent converse-theorem range
calculation.

**Next consequential check:** At $S=S_\infty$, compare the two-component
Mellin and Fourier lift in (6.3.2.10)–(6.3.2.13) with the one at $S'$.
The local isotype is trivial, but the global projector has nontrivial
character and the global polar correction in (6.3.2.11) is absent.
Check the omitted Euler factors and the two local residue functionals
at $s=0,1$ before substituting this smaller stage in the range proof.
The isotypic isomorphism above alone does not do this.
