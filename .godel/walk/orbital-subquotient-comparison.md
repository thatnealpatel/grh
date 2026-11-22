# Local-to-global comparison of the orbital subquotients

**Printed passage.** Masullo, *The Music of the Primes*, §1.2.9,
printed p. 18, paragraph beginning “It turns out that the operator,”
its display, and the continuation ending “factors through $J_{F,S}$.”
Masullo displays $p_S$ from the $S$-unit theta quotient on
$\mathcal S_0(\mathbf A_{F,S})$ to the global $F^\times$ theta quotient on
$\mathcal S_0(\mathbf A_F)$, explicitly imposing $f(0)=\widehat f(0)=0$
on both sides. He claims that it identifies the named $p$-primary
orbital subquotients linearly, topologically, and as continuous
$C_F$ representations. He assumes $\mathrm{Pic}(\mathcal O_{F,S})=1$
so $C_{F,S}=C_F$, with the local action factoring through $J_{F,S}$.
The passage and the immediately preceding local quotient formula were
checked directly in rendered pixel crops of p. 18 of the pinned PDF
(SHA-256 `e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5`),
separately from chapter Markdown and PDF text extraction. The local
quotient just defined uses the **full** $\mathcal S(\mathbf A_{F,S})$
isotype, not $\mathcal S_0$. The corresponding global quotient uses
$\mathcal S_0$.

**What a comparison would require.** Class-group triviality identifies
the groups $C_{F,S}$ and $C_F$. To compare the isotypes, the global
norm-one character must also be trivial on the outside-$S$ unit subgroup,
the kernel of $C_{F,S}\to J_{F,S}$. Theorem 6.2.1.1(2), p. 295,
states eventual bijectivity, including the inverse topology, for
insertion on **full** isotypes with this unramifiedness hypothesis.
Theorem 5.2.1.1(3), p. 230, specifies the equivariance of insertion.
For a common choice of principal-value factors at places in $S_p$,
translation at those coordinates commutes with insertion; the same
holds for local unit averaging. For the later, unit-averaged operators,
Lemma 5.3.1.5, p. 242, includes this compatibility. The literal
introductory factors and the later factors can be identified on an
isotype unramified at every place in $S_p$, not in general just because
$S_p\subset S$ (see [the operator comparison](global-orbital-submodule.md)).

**Conditional quotient argument.** Insertion tensors with the unit-ball
indicator outside $S$. It preserves evaluation at zero and multiplies
the Fourier value at zero by the nonzero additive mass of that outside
lattice. Given the full isotype isomorphism and descent of the two global
moments in Lemma 5.5.2.1, p. 280, the local moments descend via insertion.
The full isomorphism then restricts to the joint kernels. This uses the
intrinsic topologies: A quotient map restricted to the full preimage of
a subspace is open onto that subspace, so the joint kernels have both
the restricted test-space quotient topology and the induced topology.
An equivariant homeomorphism of those kernels intertwining the two
principal-value operators gives an equivariant homeomorphism of their
image quotients, by the quotient topology. This last implication does
not require closed range and does not prove Hausdorffness.

**The missing identification.** The conditional argument compares the
two **zero-moment** quotients. To use it for the named full local quotient
one must show that inclusion of the local joint kernel induces an
isomorphism onto the full local quotient. There is a concrete obstruction
to that step on the trivial norm-one isotype, even assuming the
full-isotype comparison: Evaluation at zero descends and is invariant
under the norm-one action. A test with value one at zero still gives
value one after the normalized isotype projection. Each uniformizer
difference kills evaluation at zero, including the unit-averaged version.
Thus evaluation at zero gives a nonzero functional on the full local
orbital quotient and vanishes on all classes represented by zero-moment
tests. In that case the natural inclusion cannot supply the missing
surjectivity. This is a check of the proposed map, not a claim about
abstract isomorphisms between the two representation spaces.

**Provenance and disposition.** The printed assertion and the later
insertion results are Masullo's. The moment calculation, conditional
quotient argument, and test of surjectivity are the reviewer's.
In the proof of Theorem 7.5.0.1, pp. 376–377, Masullo invokes the
zero-moment comparison at a stage unramified outside $S$ and then
writes the full-isotype isomorphism and the principal-value
intertwining relation. Remark 7.5.0.2, pp. 378–379, uses zero-moment
local numerators in the displayed comparison (7.5.0.16), not the full
local numerator of Definition 7.3.1.3, p. 343. These later readings are
provisional, from chapter Markdown and PDF text extraction, not
rendered-page inspection. The paragraph as printed remains open in
the formal ledger; the supported route is conditional and has a
different local source. No accepted Lean result is used to prove or
refute this passage. The following Mellin claim is separate.
