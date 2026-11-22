# Norm time and the descent of positive-time tests

**Printed passage.** Masullo, *The Music of the Primes*, §1.2.11,
printed pp. 20–21, claim in the paragraph from “This fulfills
expectations of Deninger” through “for all saturated S large
enough.” Masullo identifies the flow with the continuous action of
$J_{F,S}/J^1_{F,S}\simeq\mathbf R_{>0}$, restricted to
$\mathbf R_{>1}$ for the tests in use. He says the tests are supported
in $C_F^{>1}$ and “hence descend” to tests supported in $J_{F,S}^{>1}$
for all sufficiently large saturated $S$. The norm quotient,
semigroup inequality, and two support loci were spot-checked in
rendered pixel crops of the [pinned PDF](../sources/masullo/README.md),
SHA-256 `e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5`.
Chapter Markdown, PDF text extraction, and raster OCR were checked
separately. This record stops before the p. 21 paragraph beginning
“With respect to the semigroup action.”

**What the norm and the test hypotheses give.** The product norm on
the S-ideles is split surjective using a positive scalar in one
Archimedean coordinate. Since the S-units have norm one, it induces
the topological isomorphism $J_{F,S}/J^1_{F,S}\simeq\mathbf R_{>0}$.
On coarse orbits of $[D_{F,S}/\mathrm{GL}_1(\mathbf A_{F,S})^1]$,
multiplication by S-ideles consequently induces a continuous norm
action, independent of the choice of lift. On the stack one can use
the chosen norm section. Restricting the tests to positive log time
does not change the full group action.

Let $K_S$ be the image in $C_F$ of the product of the local unit
groups outside $S$. For all sufficiently large $S$, the ideals in
$S$ generate the ordinary class group, so $C_{F,S}=C_F$ and the
norm-preserving quotient $q_S:C_F\to J_{F,S}$ has kernel $K_S$.
The support condition alone does not make a function constant on the
fibres of $q_S$. For each fixed compactly supported Bruhat-smooth
test, use its smooth factorization through a Lie quotient $C_F/k$
as in Appendix D. Here $C_F$ is compactly generated, since its
norm-one group is compact and the norm splits. The inverse image in
the product of all finite local unit groups of a no-small-subgroups
neighborhood in that Lie quotient contains an entire outside-$S$
unit product for some finite $S$. Its image is a subgroup in that
neighborhood and is therefore trivial. Thus $K_S\subset k$, and the
factor on $J_{F,S}$ is still Bruhat smooth through the same Lie
quotient. The descended support is the image of the original compact
support, since $q_S$ is open and the test is constant on its fibres.
Norm preservation then gives support in $J_{F,S}^{>1}$. Both
requirements on $S$ persist on enlarging it, and adding all places
over the rational primes involved makes it
saturated. This is a threshold for a fixed test, not uniformly for
all functions supported at norms greater than one.

The quotient identification is stated in §2.3, p. 99. The use of
smooth compactly supported tests and their Lie quotients follows
Appendix D, Definition D.1.5.3, p. 762, Remark D.1.5.5, p. 763,
and Lemma D.3.6.1, p. 819. These later readings are provisional,
from chapter Markdown, not rendered-page checks. The argument for
eventual tail-unit invariance and the distinction between descent
and support preservation are the reviewer's, not given in §1.2.11.

**Open comparison.** The norm-time interpretation and the claim
that it fulfills Deninger's expectations are Masullo's. To check
that comparison, identify the particular prediction, specify the
action and its time direction in both descriptions, and match the
fixed and periodic loci in the relevant sense. If the comparison
means that these loci carry Masullo's orbital quotients, the
[analytic localization](individual-orbital-loci.md) is a separate
premise: Specify continuous maps from the test space to those
quotients and prove that their dual pullbacks vanish, relative to
$D_{F,S}$, off their designated strata. Norm-time descent does not
give that vanishing. This review does not cover the next paragraph's
attraction or periodicity assertions, does not check Deninger's text,
and uses no Lean declaration.
