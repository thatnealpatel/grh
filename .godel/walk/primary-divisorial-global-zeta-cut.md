# The primary unit cut and the global zeta function

**Printed passage.** Masullo, *The Music of the Primes*, §1.3.2,
printed p. 26, the sentence beginning “and hence multiplication by”
after the unnumbered tensor equality. Multiplication by αₖ is said
to replace the global Zeta function of the supplied test by
$Z(f,\chi|\cdot|_F^s)$ times the reciprocal Euler factors at all
places in $P_k$. The parenthesis says that the reciprocal product of
the local unit volumes is one because $S$ contains all field-ramified
places. This finding stops before “We call such multiplication
process” and does not cover the subsequent iterative or theta-space
claims.

Chapter Markdown and PDF layout extraction located the sentence.
OCR of the rendered p. 26 and direct inspection of its raster crops
from the [digest-verified edition][source] checked the assertion,
its $P_k$ index, and the parenthetical appeal to ramification. The
forward locators below were located by extraction and are not new
rendered-page reviews.

**Checked scope.** Use the explicit coordinate cut from the
[preceding audit][tensor], not the purported ambient norm preimage.
For a supplied $f=f_S\otimes\bigotimes_{v\notin S}1_{O_v}$ and a
finite set $P$ disjoint from $S$, let $f^{(P)}$ be the corrected
Schwartz–Bruhat test obtained by replacing the integer-ring factors
at $P$ by unit indicators. Let $c=\chi|\cdot|_F^s$ with $\chi$
unitary and unramified outside $S$. For a tested place $v$, the
[local Mellin calculation][local] gives, with $m_v=\mu_v(O_v^\times)$,

$$
 Z_v(1_{O_v},c_v)=m_vL_v(c_v),\qquad Z_v(1_{O_v^\times},c_v)=m_v.
$$

Thus $Z_v(1_{O_v^\times},c_v)=L_v(c_v)^{-1}Z_v(1_{O_v},c_v)$;
there is no additional measure scalar even before specializing to
$m_v=1$. Under the printed ramification condition the masses at
these tested places are indeed all one.

On $\operatorname{Re}s>1$, using the restricted-product measure in
Lemma A.3.2.4, (A.3.2.5), p. 560, and absolute convergence in
Theorem 3.2.2.1(1), (3.2.2.1), p. 124, split off the finitely many
coordinates in $P$ by Fubini. The integral on the remaining
coordinates is the same for both tests, even when $f_S$ is grouped
rather than a pure tensor of individual local functions. Applying the
local equalities to the split factors gives

$$
 Z(f^{(P)},c)=\left(\prod_{v\in P}L_v(c_v)^{-1}\right)Z(f,c).
$$

There is no division by $Z(f,c)$. Given the continuation for both
Schwartz–Bruhat tests in Theorem 3.2.2.1(1)(a), the identity extends
meromorphically by the identity theorem. This is the reviewer's
application of Masullo's local mechanism and his stated measure and
continuation results, not a check of the proofs of those forward
inputs.

**Missing premise in the printed application.** Containing the
ramified places does not make $P_k$ disjoint from $S$: The literal
first-$k$ rational-prime fibers can meet $S$. On overlap the unit
cut modifies $f_S$ inside the local integral. The outside-$S$
Euler multiplier still applies to $P_k\setminus S$, but the all-$P_k$
product additionally needs the corresponding Mellin identity for
$f_S$ and its inside-$S$ cut. It does not hold for an arbitrary
supplied $f_S$. For example, take $F=\mathbb Q$, $S=\{\infty,2\}$,
$k=1$, and trivial $\chi$. Take a positive Gaussian at infinity,
$1_{\mathbb Z_2^\times}$ at $2$, and $1_{\mathbb Z_p}$ elsewhere.
The cut fixes the test and $Z(f,|\cdot|^2)$ is finite and strictly
positive by absolute convergence and positivity on an open set.
The claimed multiplier is $1-2^{-2}=3/4$, even though the unit mass
is one. This illustrates why the outside-$S$ convention must be
made explicit or the inside-$S$ comparison separately supplied.
The finding concerns raw idelic zeta integrals on supplied tests,
not preservation of the two zero moments or descent to a theta
quotient.

**Formal comparison.** The inspected signature of
`Masullo.ideleZetaIntegral_rightHalfPlane` at accepted revision
`101d45d870f68543ef113a108bd069c6213d3214` factors a single raw
idele integral and its absolute mass on $\operatorname{Re}s>1$.
It takes a grouped Archimedean test and individual finite tests at
the exceptional places, hypotheses on the stage pullbacks of the
measure, good-place unit masses and unramifiedness, and integrability
of the displayed local tests. It does not state a comparison of
both cut and uncut tests with an arbitrary grouped $f_S$, nor
meromorphic continuation or the result for literal $P_k$. No new
Lean declaration, build, or formal refutation is claimed.

[source]: ../sources/masullo/README.md
[tensor]: primary-divisorial-tensor-cut.md
[local]: local-unit-cut-mellin.md
