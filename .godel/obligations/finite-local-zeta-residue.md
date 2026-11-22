# The residue of the finite local zeta integral

**Status:** The two-ball calculation below contradicts the printed
finite residue formula, not local meromorphic continuation or the
forward polar-free entireness claim. The decisive hat, measure
conversion, and witness normalizations were independently checked
on the rendered pinned edition. The calculation is informal and
uses the accepted Lean inputs listed below.

## Printed residue and admissible tests

On p. 141, Lemma 3.3.2.2, (3.3.2.23), prints the functional
$N(\mathfrak d_{F_v/\mathbb Q_p})^{-1/2}(1-q_v^{-1})\widehat f(0)/\log q_v$.
The proof's (3.3.2.25) instead retains $Z_v(\widehat f,|\cdot|_v)$,
and the sentence after it uses $\nu_v=|\cdot|_v\mu_v$ to pass to
(3.3.2.23). For a finite place, (A.3.2.3), p. 560, actually gives
$|\cdot|_v\,d\mu_v=(1-q_v^{-1})^{-1}d\nu_v$ on the punctured field.

Take $F=\mathbb Q$, the place $v=3$, $B=\mathbb Z_3$, and
$c_s=|\cdot|_3^s$. These are local continuous quasi-characters, with $s$
a coordinate near the trivial character by §3.1.2.1 and (3.1.2.2),
p. 120. Here $q_v=3$, $|3|_3=1/3$, and the local extension is the identity,
so the different and discriminant are units. The two tests
$f_0=\mathbf1_{3B}$ and $f_1=\mathbf1_{1+3B}$ are indicators of compact
open balls, hence in the additive $\mathcal S(F_v)$ by §2.1.2.1, p. 63,
and Example 2.1.2.5, p. 64. By (A.3.1.2), p. 556, $\nu_v(B)=1$, and
(A.3.2.2), p. 560, gives $\mu_v(B^\times)=1$. By Example A.3.1.6,
p. 557, and (D.1.1.4), p. 746, frequency $0$ is the trivial additive
character, so $\widehat f_j(0)=\nu_v(j+3B)=1/3$ for both tests.
This uses the kernel definition, not the intermediate shifted-argument
expression in (A.3.1.5). The printed prediction is $2/(9\log 3)$
for each test.

## Defining integral and reflected control

**Defining integral, (3.3.1.7), p. 130.** Each shell $3^kB^\times$ has
multiplicative Haar mass one by translation. The subsets $1+3B$ and
$2+3B$ partition $B^\times$ and are related by multiplication by $2$, so
each has mass $1/2$. Only $k\ge 1$ contribute for $f_0$, while $f_1$ is
supported in the shell $k=0$. Thus for $\Re s>0$ the two absolutely
convergent integrals are
$$
 Z_v(f_0,c_s)=\sum_{k\ge1}3^{-ks}=\frac{3^{-s}}{1-3^{-s}},\qquad
 Z_v(f_1,c_s)=\frac12.
$$
These continuations have residues $1/\log 3$ and $0$ in coordinate $s$
at $0$, respectively. In particular, $f_1$ is regular there despite
its nonzero printed residue, and the residues are not equal under any
common change of local parameter.

**Reflected integral with (A.3.2.3), p. 560.** The dual in (3.1.1.4),
p. 119, is $\widehat c_s=|\cdot|_3^{1-s}$. The transforms determined
by the kernel are $\widehat f_0(y)=\tfrac13\mathbf1_{3^{-1}B}(y)$ and
$\widehat f_1(y)=\tfrac13\overline{\psi_{\rm std}(y)}\mathbf1_{3^{-1}B}(y)$.
On $B$ both values are $1/3$. On the outer shell $3^{-1}B^\times$,
the two congruence slices have additive mass one each and the phase
has values $e^{\mp 2\pi i/3}$. The sum of the two phases is $-1$.
Consequently $\int\widehat f_0\,d\nu_v=1$ and
$\int\widehat f_1\,d\nu_v=0$, independently of conjugating the kernel.
At $s=0$, (A.3.2.3) therefore gives
$$
 Z_v(\widehat f_j,\widehat c_0)
 =\frac32\int\widehat f_j\,d\nu_v
 =\frac32 f_j(0).
$$
In fact, writing $x=3^{-s}$ and $y=3^{s-1}$, the reflected shell sums
for $\Re s<1$ are $x/(1-y)$ and $(1-x)/(2(1-y))$: The nonnegative
shells give $1/(3(1-y))$ for each test, and shell $-1$ adds $x$ for
$f_0$ and $-x/2$ for $f_1$. They are holomorphic near $s=0$. For
$c_s=|\cdot|_3^s$ use the unshifted ratio $(1-y)/(1-x)$ in §3.3.1,
p. 133. The shifts printed in (3.3.2.24) must be trivial here to
match its own claim of a pole at $s=0$. The direct contradiction to
(3.3.2.23) does not depend on those shifts. Multiplication gives both
defining integrals on their common strip $0<\Re s<1$, checking this
instance of the reflected route. At $0$ the factor has residue
$2/(3\log 3)$, the prefactor in (3.3.2.25). If instead one
substitutes the proof's claimed measure identity, (3.3.2.25) gives
$2/(3\log 3)$ and $0$, still not the equal predictions of
(3.3.2.23). Dropping the conversion factor and replacing the integral
of $\widehat f$ by its value at zero are distinct errors.

**Informal generality.** For a finite completion $F_v$ with uniformizer
$\pi_v$, let $m_v=\mu_v(\mathcal O_{F_v}^\times)$ under (A.3.2.2).
For any additive Schwartz–Bruhat $f$, compact support bounds the negative
shell indices, and local constancy gives $f=f(0)$ on all shells of
index $k\ge K$. On $c_s=|\cdot|_v^s$ the finite prefix is entire and the
tail is $m_v f(0)q_v^{-Ks}/(1-q_v^{-s})$. The corrected residue in $s$
is therefore $m_v f(0)/\log q_v$. On a component with nontrivial unit
character, extend the unit character by value one at $\pi_v$; the high
shell integrals are zero by unit Haar invariance, so only a finite sum
remains and this component is entire. The same local shell proof works
without comparing finite-extension additive characters or invoking a
functional equation.

## What is checked in Lean and what Chapter 5 can use

The accepted [`padicTranslatedBall_fourier`](../../Proofs/Theorems/PadicIntegralBallFourier.lean)
with $p=3$, $N=1$, and $a=0,1$ gives the transforms above with the
conjugate kernel. The accepted
[`map_rationalLocalMultiplicativeHaar_val`](../../Proofs/Theorems/RationalLocalHaarDensity.lean)
gives the rational finite density on the punctured field. Its additive
measure is transported from `padicAddHaar` by the
[completion equivalence](../../Proofs/Theorems/RationalAdeleIntegralStageHaar.lean).
The accepted
[`RationalLocalNormShell.measure`](../../Proofs/Lemmas/RationalLocalNormShell.lean)
gives mass one on every integer shell. The accepted
[`finiteHeckeLocalZeta_unramified`](../../Proofs/Theorems/FiniteHeckeLocalZeta.lean)
gives the integer-ball integral on $\Re s>0$ with its unit mass retained.
It does not state the residues or the translated-ball zeta integral.
No new Lean proof or audit is claimed here: The zeta sums, their
residues, and the manuscript comparison above are mathematical checks
using those interfaces, not new formal endpoints.

For the finite-place ingredient of Lemma 5.3.4.2(2), p. 260, the
corrected functional vanishes exactly when $f(0)=0$ on additive
Schwartz–Bruhat tests. By local constancy this is exactly the class
supported away from zero, which has entire local zeta integrals by
the finite shell sum. These tests are precisely $C_c^\infty(F_v^\times)$
extended by zero. The test $f_1$ is already of that type, whereas $f_0$
is not. This repairs the finite local input on that class, not the
claimed inclusion of the full $\mathcal S(F_v^\times)$ in (5.3.4.1)
and its use on p. 260. The full multiplicative Schwartz space is
strictly larger than compactly supported tests by Remark 2.1.2.1,
p. 63. The proof of part (2), p. 260, starts with product entireness
and infers local vanishing, the reverse of the implication needed by
the statement. Its continuity argument does not supply the missing
forward calculation on the printed domain.
Local poles can cancel against zeros of other factors; neither this
calculation nor the local residue criterion justifies that inference.
It does not refute the stated entireness for a correctly defined
polar-free product class or establish the
[range inclusion needed for trace transfer](trace-polar-free-q.md).

**Independent review:** Yah session `01a201e2-f513-7d67-867d-9165aa0a9f77`,
agent `wypcyMX`, independently checked the [pinned PDF](../sources/masullo/README.md)
using page rasters and extraction for surrounding prose. For the
printed route, the reviewer confirmed the hat and coefficient in
(3.3.2.23), the additive test hypotheses, and the two equally
normalized witnesses. For the defining route, the reviewer checked
(3.3.1.7), the norm coordinate and measure normalizations, and derived
the unequal residues by shell masses. For the reflected route, the
reviewer checked the dual and Fourier kernel, derived the reflected
shell sums, and compared the conversion in (A.3.2.3) with the one
asserted after (3.3.2.25). The reviewer confirmed the printed shift
in (3.3.2.24), not its general meaning. The review also checked the
general shell-tail argument informally and confirmed the direction
of the proof on p. 260. The applicability of the accepted Lean
declarations above was checked against the source at
`5563a07927b65c8eca3ca6f2dab255ed0491bde3` in the parent run, not by a
new proof audit.

**Follow-up:** The [finite-domain audit](finite-polar-free-domain.md)
shows that the unit-invariant rapid sequence $3^{-k}$ for $k\ge0$,
zero otherwise, admits no locally constant additive extension at
zero. One real flat bump then disproves the pointwise tensor inclusion
in (5.3.4.1), p. 259. See that note for the proposed next topology
check. Finite Plancherel for the
[primitive conductor shell](hecke-right-line-majorant.md#primitive-prime-power-conductor-shells-over-mathbb-q_p)
remains a separate open amplitude check.
