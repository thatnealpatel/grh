# Local closed range at the stage containing the different

**Verdict:** For the nontrivial ideal-class character of
$F=\mathbb Q(\sqrt{-5})$, at
$S''=S_\infty\cup\{\mathfrak p_2,\mathfrak p_5\}$,
$\operatorname{im}U_{S'',\chi}$ is closed in the product used by
$T_{S'',\chi}$ **with the two-ended Schwartz–Bergman topology of
Lemma D.3.1.2**. Definition D.3.1.3 literally prevents this prescription
on the left half-plane. Deleting “positive” from “positive rational”
repairs the topology prescription, not the function space or either
map. This is ordinary mathematics, not a Lean result.

## The two cited structure theorems apply to the same quotient

Use the [pinned edition](../sources/masullo/README.md). The hypotheses
are met by the [accepted stage and character check](isotypic-fourier-gluing-q-sqrt-minus-five.md#exact-global-normalization-at-the-stage-containing-the-different):
$S''$ is finite and contains infinity, the unitary $\chi$ is unramified
at every finite place, and inverting $\mathfrak p_2$ kills the class
group. The norm-one idèle with components $\sqrt 2$ and
$\varpi_2$ has value $-1$, so $\chi|_{C_F^1}\ne 1$ and its descent at
$S''$ is nontrivial. Take the section $t\mapsto(\sqrt t,1,1)$ in
$J_{F,S''}$, on which $\chi$ is trivial. Consequently the $c$ and
$\widehat c$ of (5.4.1.2), pp. 265–266, are precisely the restrictions
of $\chi|\cdot|^s$ and $\overline\chi|\cdot|^{1-s}$ in (6.3.2.10),
p. 305, with no coordinate shift. The chosen-stage and no-moment
conditions belong to the Chapter 6 application, not to the local
embedding theorem.

- Theorem 5.2.3.1(2), p. 233, states completeness of the **local**
  Hausdorff space $\mathrm H_{0,\mathrm{cont}}(\omega_{S'},
  \mathcal S(\mathbf A_{F,S'}))$ for finite $S'\supseteq S$, not just
  completeness of its strong dual or of the global limit. Take
  $\omega=\chi|_{C_F^1}$, $S=S_\infty$, and $S'=S''$. The local
  descent and source agree with (6.3.2.10). The [accepted quotient
  reading](isotypic-inverse-range-q-sqrt-minus-five.md#printed-range-and-its-source)
  of (5.2.2.4), p. 232, identifies this with the full Schwartz quotient
  by $\ker\Phi_{F,S'',\omega_{S''}}$, with its quotient topology. No
  kernels from (6.3.2.12), p. 305, are imposed.
- Theorem 5.4.1.1(1), pp. 265–266, calls that pair map a **linear
  topological embedding**, not merely a continuous injection. Its
  target in (5.4.1.2) is the same product
  $P=A\mathcal S(\mathbb C_{>0})\times A\mathcal S(\mathbb C_{<1})$
  as both source and target of (6.3.2.11), p. 305. This is a single
  component, not a product over different isotypes or the topology
  of meromorphic compact convergence. The theorem also states the
  closed range formula (5.4.1.3), p. 266.

With a common Hausdorff product topology in which the stated
embedding holds, completeness of the quotient transfers to the
image, including its induced uniform structure. A net in the image
converging in $P$ is Cauchy there, and its inverse is a Cauchy net in
the quotient. The quotient limit maps to the same ambient limit by
continuity and uniqueness. Ambient completeness is not needed in
this argument. This checks the cited inference and its scope, not
the proofs of the structure theorems in their full generality.

## Printed definition and corrected product

Lemma D.3.1.2, p. 799, allows real samples in $I$ approaching **both**
ends of $I$ in the extended real line. Its proof begins with
$I=(0,+\infty)$ and positive rational samples. Definition D.3.1.3,
pp. 800–801, specifies the same strip-Schwartz underlying space but
says “positive rational numbers as in Lemma D.3.1.2” for its
$p_{m,N}$ seminorms. This works for $(0,+\infty)$ but is impossible
for $I=(-\infty,1)$, where samples must go to $-\infty$. It also
fails for $I=\mathbb R$; the [prior membership audit](isotypic-good-heights-q-sqrt-minus-five.md#rendered-source-and-scope)
did not require the topology. Taken jointly, the literal requirements
do not define the left factor. This is not a nonclosed-image example
in a well-defined topology. If one instead drops the exhaustion
requirement and just samples positive lines, the resulting topology
on the left factor is strictly weaker: $e^{s^2-ns}$ tends to zero in
all its sampled seminorms, since the $n$-dependent norm factor on
$a+i\mathbb R$ is $e^{-na}$. It does not tend to zero at $s=-1$.

For example, interleave $1/n,n$ on the right and $-n,1-1/n$ on the
left ($n\ge2$), and use the given weighted $L^p$ seminorms. These
samples give exactly the uniform strip-Schwartz topology. For a
closed interior strip choose two sample lines strictly bracketing
it. Vertical Cauchy applied to $s^N\phi(s)$, with the horizontal
edges tending to zero by strip decay, bounds its supremum there by
the two weighted line norms: The Cauchy kernels on the chosen lines
have uniformly bounded $L^{p/(p-1)}$ norms because the gaps are
positive. Conversely, the strip sup seminorms at orders $N$ and $N+1$
bound each sampled norm, using the extra power for large ordinate.
This independently identifies the topology on **both** factors with
the same strip topology wherever they occur in (5.4.1.2),
(6.3.2.10), and (6.3.2.11). In particular all overlap evaluations
are continuous, and the product is Hausdorff. Lemma D.3.1.2 gives
the Fréchet assertion under this corrected sampling.

## A closedness check avoiding the finite polar-free reduction

The range condition (5.4.1.3) is the common kernel of
$(P_+,P_-)\mapsto P_+(s)-\rho_{S,\tau}(s)P_-(s)$ for all $s$ in
$0<\Re s<1$ off poles of $\rho_{S,\tau}$. Agreement there is equivalent
to meromorphic agreement on the overlap. The evaluation maps are
continuous in the corrected product, so this condition defines a
closed subspace $W_S$. This argument alone does not show that every
pair satisfying the overlap has a Schwartz representative.

For this stage one can reduce that last equality to the
[accepted archimedean range interface](isotypic-inverse-range-q-sqrt-minus-five.md#verified-local-image-criterion),
without using the general proof's finite polar-free subspace. In the
positive-abscissa half-planes put
$$
 B_+(s)=u_2u_5 L_2(s)L_5(s),\qquad
 B_-(s)=u_2u_5\,20^{1/2-s}L_2(1-s)L_5(1-s).
$$
These are the forward and Fourier-reflected transforms of the tensor
of the **retained** unit balls, by the [accepted shell and trace-dual
calculation](isotypic-fourier-gluing-q-sqrt-minus-five.md#omitted-balls-and-their-mellin-multipliers).
Here $L_v(w)=(1-a_v q_v^{-w})^{-1}$, $a_2=-1$, and $a_5=1$.
The constants $u_v=\mu_v(O_v^\times)$ are the multiplicative unit
masses. Only their being nonzero is needed here. The factor
$20^{1/2-s}$ includes the additive unit-ball masses after Fourier
transform and the change in shell index on the two trace-dual balls.
Each $B_\pm$ and its reciprocal are bounded on
closed interior strips of its half-plane: The Euler denominators are
bounded away from zero there by $1-q_v^{-\varepsilon}$ when the
corresponding positive abscissa is at least $\varepsilon$, and the
exponential's modulus depends only on the real part. Thus
$(P_+,P_-)\mapsto(B_+P_+,B_-P_-)$ is an automorphism of $P$.

On the overlap the local functional equation (3.3.1.2), p. 129,
evaluated on the Gaussian tensored with the two balls gives
$\rho_{S'',\tau}=(B_+/B_-)\rho_{S_\infty,\tau}$, since the Gaussian
legs $G(s)$ and $G(1-s)$ are nonzero there. The diagonal
automorphism therefore carries $W_{S_\infty}$ onto $W_{S''}$. Dividing
any pair in $W_{S''}$ by its two ball factors gives one pair in the
full archimedean image, so one Schwartz representative there,
tensored with the balls, realizes the original pair. The opposite
inclusion is the local functional equation. Hence the local image is
closed using just the archimedean range equality and the accepted
local equations. The reduction works for the same class character
upon adjoining any finite set of unramified places to $S_\infty$:
Use their ball multipliers and trace-dual factors. It does **not**
assert that the global gluing is correct at stages omitting part of
the different. Nor does it validate the [printed finite polar-free
domain](finite-polar-free-domain.md) used elsewhere in Chapter 5.

## Evidence and review

The [earlier rendered topology reading](isotypic-good-heights-q-sqrt-minus-five.md#rendered-source-and-scope)
verified the both-end requirement on p. 799 and the definition on
pp. 800–801; its conclusion only used membership on the full plane.
The present audit applies that requirement to the left half-plane.
The prior [rendered local range reading](isotypic-inverse-range-q-sqrt-minus-five.md#printed-range-and-its-source)
and [rendered gluing interface](isotypic-fourier-gluing-q-sqrt-minus-five.md#source-interface)
supply the full quotient, the two legs, and the identical product in
(6.3.2.10)–(11), p. 305. Those prior renderings are not new checks.

The worker inspected rendered crops of the local quotient, the
containment $S'\supseteq S$, and “They are complete” in Theorem
5.2.3.1(2), p. 233, “linear topological embedding” in Theorem
5.4.1.1(1), p. 266, and “positive rational numbers” in Definition
D.3.1.3, p. 801. Independent reviewer `xSmtsqh` (transcript Yah
`01a2046a-2385-7738-89c6-a02a8a4f700a`, base
`9f10e8ef6104bf715c07054bf7e3c4567f15f687`) reported seeing those
three phrases or words from tight pixel crops. The p. 233 review
read “complete” but did not read its subject reliably from pixels.
The exact attribution there to the local spaces for $S'\supseteq S$
is the worker's reading, independently corroborated by layout
extraction, not by independent pixels. The surrounding wording
of the Chapter 6 completeness citation and closedness deduction on
pp. 305–306 is extraction, with the displayed map interfaces as
verified in the linked gluing note.

Independent reviewer `huFblnj` (same transcript Yah
`01a2046a-2385-7738-89c6-a02a8a4f700a`, base
`a7b18ef844a89902e35499a5e8350b10f4943fd6`) corroborated the theorem
scopes and literal sampling discrepancy by extraction, not pixels.
They separately checked the complete-embedding implication, the
common-kernel argument, and the two invertible ball multipliers and
Gaussian factor ratio using the inherited formulas. This supplies
a check of the local closedness proof, not of the sequential division
argument for $T$ on p. 306.

## Scope and next check

The [accepted global normalization](isotypic-fourier-gluing-q-sqrt-minus-five.md#exact-global-normalization-at-the-stage-containing-the-different)
identifies the map obtained by gluing with $L\circ\overline\pi_{S''}$
with scalar one. At (6.3.2.13) and the following closed-range
paragraph, p. 306, the present result supplies the closedness of
$\operatorname{im}U_{S'',\chi}$ in the domain of $T_{S'',\chi}$. If
$T_{S'',\chi}$ is a closed embedding, its restriction to this closed
subspace has closed image in $P$, hence also in the overlap kernel.
The product correction itself does not give the closed embedding of
$T_{S'',\chi}$, and closedness does not give surjectivity.

**Next bounded check:** Test the forward scalar division step of the
sequential closed-range argument after (6.3.2.13), p. 306. For a
limit $h$ in the right Schwartz–Bergman space of multiples of the
omitted Euler multiplier at $S''$, matching zero jets make the
quotient holomorphic. Check whether the printed residue argument
actually yields its rapid decay on an arbitrary closed interior
strip, without assuming $h$ is entire. If not, test circles centered
on a fixed abscissa $>1$, with radii staying in the right half-plane,
using the Euler lower bound at the center and polynomial upper
bounds on the disks. This would advance the missing forward
membership implication for closedness of the multiplier. The
reflected leg, entire restriction/gluing topology, and global range
surjectivity are separate.
