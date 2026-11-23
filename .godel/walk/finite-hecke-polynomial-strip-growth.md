# Polynomial strip growth of the finite Hecke function

**Status: Open at the formal scope.** Masullo, *The Music of the
Primes*, §1.4.7, printed p. 31, first bullet after “other properties
of $L_f(s,\chi)$ are also used.” The bullet announces a uniform
polynomial **upper** bound for $L_f$, not for its reciprocal. The
other two bullets are separate inputs and are not reviewed here.

In the [digest-verified edition](../sources/masullo/README.md),
chapter Markdown and PDF layout extraction located the bullet and
its source, Lemma B.1.1.2, printed p. 590. OCR of the rendered pages
checked the prose; direct inspection of pixel crops checked the
finite subscript and strip wording on p. 31 and the growth formula
and fixed interval on p. 590. The later uses below were located by
extraction only and remain provisional source readings.

**Needed conclusion.** For fixed $F$, unitary $\chi$, and $a<b$,
there are $C,M,T>0$ with $|L_f(\sigma+it,\chi)|\le C|t|^M$ for
all $\sigma\in[a,b]$ and $|t|\ge T$. The bound needed here is
uniform in $\sigma$ on the given strip, not an exponent common to
all strip locations, and it does not include any finite-height
pole. Lemma B.1.1.2 is where Masullo imports the classical input
from [IK, Ch. 5, §5.1, Lemma 5.2, p. 97]; the preview does not give
an argument. Lemma B.1.1.1 assumes a growth bound and is not a
proof of it. The formal gap is a strip estimate for the
meromorphically continued finite function agreeing with the Euler
product for the actual unitary idèle-class character on $\Re s>1$.

**Use of the bound.** In the proof of Theorem B.6.1.7, p. 642,
(B.6.1.37)–(B.6.1.38) require an upper bound on a fixed strip
wide enough for the large-height disks used on the omitted Euler
product. For fixed finite $S$, each unramified multiplier
$1-\chi_v(\pi_v)q_v^{-s}$ is bounded by $1+q_v^{-a}$ there, and
a ramified factor is $1$. Thus multiplication by the finite product
preserves the upper bound. The text of this later proof cites
Proposition B.1.1.3, p. 591, whose displayed estimate is for
$0\le\Re s\le1$, not for those wider strips. Lemma B.1.1.2 is the
input of the required scope. This citation distinction is the
reviewer's audit, not a proof of the selected-height reciprocal
estimate. Upper bounds alone do not bound the reciprocal, even
on a zero-free line.

**Checked scope and provenance.** The classical citation and
contour use are Masullo's. The project's
[`Masullo.finiteHeckeCharacterEulerProduct_convergesOn`](../formalize/finite-hecke-half-plane.md)
for an actual unitary character proves uniform product convergence
with a summable factor-deviation majorant on $\Re s\ge a>1$.
That is an absolute-convergence result for the product, not a
growth bound for its continuation on arbitrary fixed strips. No
new Lean proof, general formal result, or contour limit is claimed.
