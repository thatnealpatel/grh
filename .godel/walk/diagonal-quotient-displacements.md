# Diagonal quotients and the Archimedean factor

**Printed passage.** Masullo, *The Music of the Primes*, §1.7.1,
printed pp. 33–34, second bullet from “One instrument that is pervasive”
through “throughout are lost.” Equation (1.7.1.1) displays
$(\mathbf R^N\times A)/\Gamma_0$, where $A$ is an open subgroup of a
second-countable locally profinite group and $\Gamma_0$ is discrete.
Masullo says that the diagonal action, for example by principal ideles
or $S$-units, trades displacements in the $A$-variable for Euclidean
translations. He says this is used to construct functions and obtain
topological bases on subquotients in the first seven chapters, and that
such quotients are unavailable over global function fields. The next
bullet, on reductive-group double cosets, is separate.

The [pinned PDF](../sources/masullo/README.md) matches SHA-256
`e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5`.
The chapter Markdown and PDF layout extraction located the bullet.
Raster OCR checked its text, and direct inspection of rendered pixel
crops checked the displayed quotient, the direction of the displacement
transfer, and the function-field wording. The later passages below
were located by extraction and their readings are provisional.

**Scope of the transfer.** In right cosets, $(u,b)\in\Gamma_0$ gives
$[x,ab]=[x-u,a]$. This is an identity for displacements by the actual
projection of $\Gamma_0$ to $A$, not for arbitrary $b\in A$. Even on
finite valuation directions (modulo local units), one needs the relevant
valuation vectors in the image. Different lifts can differ by a pure
Euclidean period from $\Gamma_0\cap(\mathbf R^N\times\{1\})$.
Discreteness alone supplies neither the projection hypothesis nor
an identification of the function-space topologies. For example, a
basis transport needs a topological isomorphism for the particular
subquotient, not just a relation between representatives.

Masullo's rational calculation in the proof of Proposition 2.4.1.1,
p. 109, (2.4.1.14), uses a power of $p$ as a diagonal $S$-unit to
normalize support at $p$ while rescaling the real test function.
For the number-field valuation directions, Remark A.1.5.3, pp. 544–545,
(A.1.5.10), identifies the cokernel of the finite-place valuation
projection of $S$-units with $\mathrm{Pic}(\mathcal O_F)$ for $S$
large enough to kill the $S$-class group. This is not arbitrary
surjectivity. Corollary 4.5.1.6, p. 204, supplies a specific basis target:
Under Situation 4.4.2.3, the primal quotient of $\mathcal S_E(G)$ by the
kernel of isotypic monogenic periodization is asserted to have an
absolute Schauder basis mapped to the conjugate characters of the
specified isotype in $(\gamma^{\mathbf Z})^\perp$. Neither input
asserts a basis for arbitrary quotients of the displayed form.

**Scope of the function-field contrast.** In a locally profinite
abelian group, the images of compact open subgroups in a Hausdorff
quotient by a closed subgroup are again compact open and form a basis
at the identity. In particular the natural Hausdorff quotients of the
function-field ideles or $S$-ideles by the closed arithmetic subgroups
are totally disconnected. In contrast, for $N>0$ the quotient of
$\mathbf R^N\times A$ by a discrete subgroup has a local chart at the
identity coset: Restrict the open quotient map to a small product
neighborhood whose pairwise quotients miss all nonidentity elements
of $\Gamma_0$. It embeds a nontrivial Euclidean slice, so the quotient
cannot be totally disconnected. This explains the absence of an
*intrinsic positive-dimensional* chart of this form for those
function-field quotients. It does not rule out (1.7.1.1) with $N=0$,
quotients after adjoining an external real factor, or basis arguments
that do not require an Archimedean factor. The restriction to the
natural arithmetic quotients and $N>0$ is an interpretation of the
contrast, not a premise stated in the printed bullet.

**Provenance and disposition.** The methodological claims and the
constructions named above are Masullo's. The coset calculation, the
projection limitation, and the topological comparison are the
reviewer's informal analysis. In the accepted tree inspected at
`6203cff17bce80aa78fbf8fbd0e50c7b50856f9f`,
`Masullo.exists_rational_principal_mul_finite_valued_eq_one` in
`Proofs/Theorems/RationalIdeleNormalization.lean` supplies simultaneous
principal rescaling to finite valuation one for rational ideles. It
asserts existence of a rational principal multiplier, not a general
quotient chart, a topology on a subquotient, a Schauder basis, or any
function-field comparison. No formal verdict is entered on the bullet.
The projection and topological basis transport must be checked in their
actual settings; the bullet provides no more general theorem or
specified alternative function-field argument to verify here.
