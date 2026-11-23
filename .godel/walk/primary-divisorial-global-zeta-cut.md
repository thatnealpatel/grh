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

## Lean-checked raw Mellin multiplier at two distinct rational primes

[`Masullo.rationalTwoPrimeMaskedZetaIntegral`](../../Proofs/Theorems/RationalThetaTwoPrimeMellin.lean)
uses `rationalIdeleHaar` on the actual rational idele group with a Borel
measurable-space instance. For distinct `p q : Nat.Primes`, complex
Schwartz `b` on the real line, and `1 < z.re`, it gives absolute
integrability of the joint-mask density and
$$
Z(M_{p,q}F_b,z)=(1-p^{-z})(1-q^{-z})Z(F_b,z),
\qquad F_b=b\otimes 1_{\widehat{\mathbb Z}}.
$$
Here `M` retains integral units at the two places, and the weight in
both raw integrals is the positive idelic norm to the complex power
`z`. Neither an LF witness nor moment vanishing is required.

The [accepted joint-cut theta theorem](primary-divisorial-theta-range.md#checked-small-norm-tail-at-any-two-distinct-primes)
compares orbit sums on classes, while
[`rationalUnramifiedZetaIntegral_eq_thetaMellin`](../../Proofs/Theorems/RationalThetaMellinKernel.lean)
unfolds the raw integral only for the uncut tensor. The new proof stays
upstairs. On the integral cylinder the excluded nonunits at a place
are precisely its left translate by the uniformizer there: The local
norm is an integral power of the inverse prime, so after lowering the
norm by one step, strict inequality with one is equivalent to the
original weak inequality. The Archimedean coordinate and all other
finite coordinates are unchanged. Thus the second subtraction keeps the
first unit predicate intact, and its intersection term is the double
translate. Haar invariance integrates each translated density with
its inverse-prime norm factor. Absolute integrability follows from the
accepted uncut density and the translated differences; the proof does
not need a separate measurability theorem for the cut.

**Source scope:** The [filtration audit](divisorial-filtration.md)
verifies the disjoint test set in (1.3.2.2), p. 25. The
[tensor audit](primary-divisorial-tensor-cut.md) verifies the outside-`S`
input in (11.3.1.1), p. 492, and the different printed right-hand
index in §1.3.2, p. 26. Here the base is the real place only, and the
unit factors go at the two finite primes, with integer-ring factors
at the remaining places outside the base. The rendered reading at
this note's start separately verifies the inverse-Euler-factor claim
in §1.3.2, p. 26; the formal result uses the repaired support, not the
printed indexing or an overlapping cut. The
[global theta source review](../formalize/global-box-theta-operator.md#source-and-scope)
identifies the kernel comparison in (5.1.2.1), p. 224. The new result
is a raw convergence-half-plane input for that comparison, not a
kernel theorem, descent, or continuation. No new manuscript reading
was needed.

**Review and checks:** Independent exact-source review
`joint-mellin-statement` (`GfbBjjO`), housed in Yah
`01a20691-c6d1-74e3-9211-0645f7562c15`, checked the statement, the
inherited source scope, and the local shell, uniformizer, and Haar
reduction against `021fb6f55c65487e32d54130f5e1b0ebeda089f7`, without
elaboration. The owning session also records the checked dependency
probes, exact integrated candidate, joint signature and axiom report,
and adoption result.

**Next bounded check (formalization only):** Show that if the joint
masked class theta vanishes, then the uncut lattice theta vanishes at
every positive norm. The accepted four-scale formula, evaluated on the
positive norm section, already gives
`(1 - D_p)(1 - D_q) θ_b = 0`, where `D_p f(t) = f(p*t)`. Prove
injectivity of `1 - D_p` on profiles tending to zero at infinity by
iterating the dilation, and use it twice. The needed limit for `θ_b`
is already proved privately as `rationalTheta_tendsto_zero_atTop` in
[`RationalThetaOrbitalConstant`](../../Proofs/Lemmas/RationalThetaOrbitalConstant.lean)
from the accepted uniform tail; the limit for its `q`-difference then
follows by scaling. No new theta computation is needed. Nonvanishing of
the scalar factors on the fixed line, and assembly with the existing
uncut line-kernel equivalence, are separate from this check.
