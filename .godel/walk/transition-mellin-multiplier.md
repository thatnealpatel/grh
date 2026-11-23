# The Mellin multiplier of finite-stage insertion

**Printed passage.** Masullo, *The Music of the Primes*, §1.4.7,
printed p. 30, claim beginning “For example, assume S” and ending
with the definition of the local Euler factor at $v\in S_f$. The only
stated size constraint on $S$ is that it is finite and contains the
Archimedean places. The transition operator $p_S$ on the full $S$-unit
and global continuous theta coinvariant spaces is induced by
$f_S\mapsto f_S\otimes\bigotimes_{v\notin S}1_{\mathcal O_{F_v}}$. The
Mellin multiplier is printed as
$L^S(s,\chi)=L_f(s,\chi)\prod_{v\in S_f}L_v(\chi_v|\cdot|_v^s)^{-1}$.
This is the omitted product, not the retained product, and the passage
is not restricted to tests with two zero moments. Coverage stops before
the proposed use of its reciprocal to propagate the orbital bases.

Chapter Markdown and layout extraction located the passage. Raster OCR
checked the prose, and rendered pixel crops checked the source and
target, the tensor index, and the multiplier display in the
[digest-verified edition](../sources/masullo/README.md). The Haar choices
in (3.2.2.1), p. 124, and (3.3.1.1), p. 129, and the unit mass and
product displays (A.3.2.2), (A.3.2.5), and (A.3.4.2), pp. 560–561,
were checked separately in rendered pixel crops.

**Absolute-convergence calculation.** Let $u_v=\mu_v(\mathcal O_{F_v}^\times)$
and use the global restricted product $\mu$ and the local product
$\mu_S=\bigotimes_{v\in S}\mu_v$. For unitary $\chi$ unramified outside
$S$, let $\chi_S$ be its restriction to the $S$-idèles, which is trivial
on the $S$-units: The character is trivial on diagonal elements, and
an $S$-unit has unit components outside $S$. On $\Re s>1$, partition the
outside-$S$ integral support by finite-support nonnegative valuation
vectors. Each valuation shell at $v$ has multiplicative mass $u_v$.
The local geometric series integrates the unit-ball test to
$u_v(1-\chi_v(\pi_v)q_v^{-s})^{-1}$. Absolute convergence justifies the
factorization, since the off-$S$ unit masses differ from one only at
finitely many places and the absolute shell sums are bounded by the
finite zeta product in that half-plane. Thus on representatives the
identity with the indicated Haar measures is

$$
Z(f_S\otimes\mathbf 1_{\mathrm{out}},\chi|\cdot|_F^s)
= Z_S(f_S,\chi_S|\cdot|_{F,S}^s)\,L^S(s,\chi)
  \prod_{v\notin S}u_v.
$$

Here $\mathbf 1_{\mathrm{out}}$ is the tensor of the integral-ring
indicators, not the indicator of the unit groups. A character ramified
at even one outside place instead gives zero on the inserted test by
local unit invariance; the local $L$-factor $1$ at a ramified character
does not encode that zero. On the unramified components the identity
continues meromorphically wherever the two transforms and the factor
have meromorphic continuations, by uniqueness. This is not a boundary
Lebesgue integral calculation or an inversion result.

**Normalization check.** The mass in (A.3.2.2) is
$|\operatorname{disc}(\mathcal O_{F_v}/\mathbf Z_p)|_p^{1/2}$, which
may differ from one even when $\chi_v$ is unramified. For instance,
$F=\mathbf Q(i)$, $S=S_\infty$, and $\chi=1$ leave a unique place over
$2$ with local integer basis $1,i$ of discriminant $-4$ and unit mass
$1/2$. All other finite places have unit mass one. A nonzero nonnegative
smooth Archimedean test supported away from zero has positive local
integral at $s=2$, so the factor $1/2$ cannot be dropped. Including the
field-ramified finite places in $S$ restores the displayed scalar on
the unramified character components; alternatively, keep the omitted
mass or rescale the local Mellin transform. None of these qualifications
is stated in the paragraph.

**Disposition and provenance.** The transition and multiplier claims
are Masullo's. The valuation-shell calculation and the quadratic-field
normalization test are the reviewer's. Theorem 5.2.1.1(3), p. 230, states
that this tensor insertion induces the continuous map on the full
theta quotients, and its proof appeals to an equality of the relevant
Mellin kernels. That reading is provisional, from chapter Markdown and
layout extraction. Theorem 6.3.2.1's proof, p. 307, repeats the product
comparison for its chosen stage and characters unramified outside it;
that reading is also provisional, and class group triviality alone
does not enforce the unit-mass premise. This passage is open at the
printed general scope. Verify descent for the actual theta kernels
and track the unit-mass scalar in the normalized comparison. No claim
about a continuous inverse, orbital jets, or contour estimates is
checked here.

The accepted Lean `Masullo.ideleZetaIntegral_rightHalfPlane`
(`Proofs/Theorems/IdeleZetaIntegral.lean`,
`04e0fc6889d4bfc5d3d70ea464fffb8cd4da3ffa`) factors the raw upstairs
integral, not a map on the theta quotients. Its comparison stage must
contain the test exceptions, with unit mass one and character
unramifiedness assumed off that stage, and it assumes the product
measure restrictions and local integrability. It only treats $\Re s>1$.
`Masullo.exists_discriminantNormalizedIdeleHaar`
(`Proofs/Theorems/DiscriminantNormalizedIdeleHaar.lean`,
`002582a9c417a34219ff7c000b722972067b021f`) constructs the calibrated
restricted-product measure, with unscaled stage formulas for stages
containing the different support. It is not a Mellin intertwining
theorem. Neither endpoint verifies the unqualified printed claim.
