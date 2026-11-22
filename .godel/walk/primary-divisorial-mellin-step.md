# The Mellin step between primary divisorial strata

**Printed passage.** Masullo, *The Music of the Primes*, §1.3.2,
printed p. 26, the paragraph beginning “In particular, and this is
the main observation of this subsection,” through the unnumbered
Euler product. The forward Mellin transform of restriction to the
$(k+1)$st stratum is said to be that of restriction to the $k$th
stratum times $\prod_{v\in S_{p_{k+1}}}L_v(\chi_v|\cdot|_v^s)^{-1}$.
Here the page explicitly identifies $T_k$ with the first $k$
rational primes and defines $P_k$ as the union of the fibers over
them. This note stops before “If we let $f$ (equivalently $f_S$)
vary,” the ensuing theta-space inclusion.

Chapter Markdown and PDF layout extraction located the paragraph.
OCR of rendered crops checked the prose and the first-primes
convention, and inspection of the rendered formula pixels checked
the product index and inverse exponent. The PDF matched the digest
in the [edition record][source].

**Checked scope.** Use the explicit coordinate loci, and put
$B=P_{k+1}\setminus P_k=S_{p_{k+1}}$. For a supplied test of
(11.3.1.1), write $f^{(k)}$ for the test cut at $P_k$. The previous
cut cannot change the factors in $B\setminus S$. If $B$ is disjoint
from $S$, those factors in $f^{(k)}$ are still integer-ring
indicators. Split off just the coordinates in $B$ and use the
[preceding raw zeta comparison][global] there. For unitary $\chi$
unramified outside $S$, this gives

$$
Z(f^{(k+1)},\chi|\cdot|_F^s)
=\left(\prod_{v\in B} L_v(\chi_v|\cdot|_v^s)^{-1}\right)
 Z(f^{(k)},\chi|\cdot|_F^s).
$$

Under the stated restricted-product measure and absolute
convergence results, this holds on $\operatorname{Re}s>1$ with no
extra scalar, and extends meromorphically given continuation of
both tests. No division by the previous zeta integral is needed.
Only the **new** fiber must avoid $S$ for this argument. If the new
fiber meets $S$, the outside-$S$ factors still give their Euler
multipliers, but the already cut $S$-local block needs its own
Mellin identity: Cutting it at $B\cap S$ must multiply its Mellin
integral by the product of the reciprocal Euler factors at those
inside-$S$ places. Neither saturation nor the ramification
condition supplies this identity.

**Literal first-primes counterexample.** Take $F=\mathbb Q$,
$S=\{\infty,3\}$, $k=1$, and trivial $\chi$. This $S$ satisfies
the printed ramification, saturation, and class-number conditions.
Let the finite factors of $f$ be $1_{\mathbb Z_3^\times}$ at $3$
and $1_{\mathbb Z_p}$ elsewhere. For the real factor take
$b(x)=h(x)-\tfrac12 h(x/2)$, where $h$ is a nonzero nonnegative
even smooth bump supported away from zero. Then $b(0)=0$ and
$\int b(x)\,dx=0$ by scaling, so both the supplied test and its
coordinate cuts satisfy the two global zero moments. The first cut
puts the unit indicator at $2$. The next cut, at $3$, changes
nothing. At $s=2$ the real multiplicative integral of $b$ is
$(1-2)\int h(x)|x|^2\,d^\times x\ne 0$ by multiplicative Haar
invariance. With the unchanged finite factors, the raw global
integral is that real integral times the strictly positive unit
masses at $2,3$ and the convergent, positive Euler product at the
other primes. The printed multiplier at $3$ is $1-3^{-2}=8/9$,
so the asserted equality fails even on this two-zero-moment test.
If one instead retains the earlier outside-$S$ convention and
enumerates only fibers outside $S$, the restricted identity above
applies, but the filtration is then not the literal first-primes
one. This counterexample concerns the coordinate unit cut, not a
principal-value dilation-difference operator.

**Provenance and Lean comparison.** The iteration is Masullo's
claim. The reviewer applies the preceding audited finite-coordinate
argument to the new fiber and adapts its overlap counterexample to
a single step and a real test with both moments zero. The measure
and continuation inputs are those recorded in the preceding audit,
not newly checked proofs. At the inspected project revision
`733c290eb19976bcb4dc15f00835ef3872bb0fc3`,
`Masullo.ideleZetaIntegral_rightHalfPlane` factors one raw integral
and its absolute mass above one, under stage-measure, good-place,
and local integrability hypotheses, with grouped Archimedean data
and individual finite tests. The rational specialization
`Masullo.rationalIdeleZetaIntegral_schwartzMellin` factors one raw
rational integral above one as a stage integral times its outside
Euler tail, with a flat-at-zero real Schwartz factor and continuous
compactly supported exceptional finite factors. Neither statement
compares the two successive cuts, proves their meromorphic
comparison, or asserts preservation or descent on the theta
quotient. There is no new Lean declaration, build, or Lean
refutation in this note.

[source]: ../sources/masullo/README.md
[global]: primary-divisorial-global-zeta-cut.md
