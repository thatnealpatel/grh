# Primary coordinate cuts and the global principal-value ranges

**Printed passage.** Masullo, *The Music of the Primes*, §1.3.2,
printed pp. 26–27, from “If we let $f$ (equivalently $f_S$) vary”
through the display after “yet smaller and closed subspace.” Write
$H=\mathrm H_{0,\mathrm{cont}}(\chi|_{C_F^1},\mathcal S_0(\mathbf A_F))$.
The paragraph puts the resulting theta images of the $k$th and
$(k+1)$st restrictions in $\mathrm{PV}_{P_k}H$ and
$\mathrm{PV}_{S_{p_{k+1}}}\mathrm{PV}_{P_k}H=\mathrm{PV}_{P_{k+1}}H$,
respectively, calling the latter a smaller, closed subspace. It
follows the convention that restriction is the coordinate unit cut
on a test representative, not restriction of a function on $C_F$
to a subset of that quotient. It follows the explicit first-primes
convention for $P_k$; earlier, (1.3.2.2) used tested sets disjoint
from $S$. The subsequent subquotient and its basis are a separate
claim.

Chapter Markdown and PDF layout extraction located the passage;
raster OCR checked the prose, and spot inspection of rendered crop
pixels checked the principal-value indices, $\mathcal S_0$ source,
and the phrase “yet smaller and closed subspace” across the two
pages. The local PDF matched the [edition pin][source]. The
parallel pp. 493–494 of §11.3.1.1, the Chapter 5 proof of Lemma
5.3.1.5, and the discussion of the moments in Lemma 5.5.2.1 were
consulted in chapter Markdown and are provisional here as new
readings of those passages.

**Failure for the literal cuts.** Take $F=\mathbf Q$, $S=\{\infty,2\}$,
and the trivial character. This $S$ is saturated, contains all the
required places, and has trivial $S$-class group. Take a nonzero even
nonnegative smooth bump $b$ supported away from zero at infinity,
$1_{\mathbf Z_2^\times}-1_{2\mathbf Z_2}$ at $2$, and integer-ring
indicators at the other primes. This test is of the prescribed
shape and belongs to $\mathcal S_0$: Its value at zero vanishes, and
so does its additive integral, since the two $2$-adic sets have equal
additive mass. The cut at $P_1=\{2\}$ kills the second summand and
leaves a strictly positive additive integral. The theta function
of the cut is not merely given by a bad representative: It is not
in $H$ at all.

For that last assertion, normalize additive mass of
$\widehat{\mathbf Z}$ to one, and evaluate theta at the class of
$(t,1,1,\ldots)$, $t>0$. The cut theta sum is
$\sum_{n\text{ odd}}b(nt)$. Multiplying by $t$ and sending $t$ to zero
gives $\tfrac12\int_{\mathbf R}b(x)\,dx>0$. For any rational
Schwartz–Bruhat test, the same scaled limit for the nonzero theta
sum is its additive integral. Indeed, write it as a finite sum of
real Schwartz functions times indicators of finite-adèle cosets
of $N\widehat{\mathbf Z}$ contained in $N^{-1}\widehat{\mathbf Z}$,
for some integer $N\ge 1$. Each coset intersects the rational
diagonal in one progression $a+N\mathbf Z$ by the Chinese remainder
theorem, and each scaled Riemann sum tends to the real integral
divided by $N$, the additive mass of the coset. Omitting zero does
not change that limit. The trivial norm-one projection does not
change the vanishing of the limit for two-zero-moment inputs:
Every norm-one rational idèle class has a sign-and-finite-unit
representative by clearing valuations. One can average the test
over this compact group before taking theta; it preserves the
additive integral and remains Schwartz–Bruhat (there is a common
open stabilizer on each finite test). On the cut example the
group acts trivially, so the projection only contributes a
nonzero scalar if the Haar measure is not normalized. Thus no
two-zero-moment input has its projected theta function equal to
the cut output. This refutes the claimed containment for the
literal filtration already at level one, not closedness of the
principal-value image as a separate claim.

The raw coordinate cut also need not descend, even when both
outputs have zero moments: Use the $2$-unit indicator and a real
factor $h(x)-\tfrac12h(x/2)$, with $h$ nonnegative, even, and
supported in $1<|x|<1.1$. Translate this test by the diagonal
rational $2$ using $T_a f(x)=f(a^{-1}x)$. The two tests remain in
$\mathcal S_0$ and in the same fixed tensor stage, with identical
theta by reindexing the rational sum. The cut fixes the first
and kills the second. The first theta is nonzero: Choose $t$ in
$(1,1.1)$ with $h(t)>0$. Only the odd integers $\pm1$ contribute,
and $h(t/2)=0$. Both theta functions before cutting are in the
trivial norm-one isotype. This obstruction is about cutting inside
$S$, not about descent of a principal-value operator.

**What does work.** If $P_k$ is disjoint from $S$, each tested
factor of a supplied tensor is $1_{\mathcal O_{F_v}}$. On it
$1-T_{\pi_v}$ gives $1_{\mathcal O_{F_v}^\times}$, as in Masullo's
parallel explanation in §11.3.1.1, p. 493. The later unit-averaged
factor $1-T_{\pi_v}U_v$ gives the same result on that factor,
since the normalized unit average $U_v$ fixes it. Both products
preserve the two zero moments and intertwine theta with the
corresponding products of translations and, where used, unit
averages. Thus for a supplied fixed-stage representative in
$\mathcal S_0$ the restricted theta is precisely the image of the
original theta under the corresponding principal-value product;
two such representatives of the same projected theta class give
the same output. If also the new fiber is disjoint from $S$, this
applies at both levels. The product equality and nesting are
algebraic for a consistent choice of commuting descended local
factors and the disjoint union of place sets. Nesting by itself
gives neither strictness nor closedness. Using all of $H$ in the
fixed-stage argument requires representatives with the two zero
moments, not just (1.3.2.1) read as surjectivity from the full
local test space. Lemma 5.5.2.1's moment descent and norm-one
invariance are inputs for that comparison.

**Open topological step.** For closedness, prove closed range of
the finite product in the intrinsic global two-zero-moment theta
quotient topology. It would suffice to obtain closed topological
embeddings on $H$ for the successive individual factors (a finite
composition is then a closed embedding), or verify the full
quotient closed embedding of Lemma 5.3.1.5 for the product and
justify the restriction to the closed moment kernel and isotype
with the intended topology. The [earlier closedness audit][closed]
identifies the missing quotient step. The repetition on pp.
493–494 supplies no proof of closedness. The [Mellin-step audit][step]
checks a raw zeta comparison, which also supplies no closed-range
argument.

**Provenance and Lean comparison.** The two containments and the
closedness assertion are Masullo's. The disjoint-factor identity
uses Masullo's uniformizer-difference explanation. The overlap
examples, scaled Riemann-sum argument, and separation of algebraic
nesting from closedness are the reviewer's. The existing
`Masullo.rationalAdeleLF_uniform_theta_tails` in
`Proofs/Theorems/RationalAdeleLFThetaTails.lean` at the candidate
base `e7cf12509d9926d58b33c64fcc9be7b8e356ed99` bounds the two tails
of the unprojected class theta on a bounded family of rational LF
tests, retaining both zero modes at small norm. It is not used in
the Riemann-sum proof. It does not address coordinate cuts,
principal-value membership, or the general closed range; no Lean
declaration is added or used to prove the refutation. Owning
source-review session: `01a2056a-f3ce-7a75-88fb-d796bae9feb5`.

[source]: ../sources/masullo/README.md
[closed]: global-orbital-submodule.md
[step]: primary-divisorial-mellin-step.md
