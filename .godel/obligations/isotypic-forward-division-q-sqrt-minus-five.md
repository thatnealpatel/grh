# Forward scalar division at the stage containing the different

**Verdict:** The residue citation after (6.3.2.13), p. 306, does not
supply the forward quotient's rapid decay as written. The stated
horizontal estimates are not the vertical-line inputs to the cited
residue theorem, and its conclusion is an integral identity, not the
required uniform strip bound. The theorem does not require an entire
numerator, but the full strip named on p. 306 crosses its available
half-plane. A disk argument proves the forward membership and closed
range for the specified class character using only interior seminorms.
The repair is reviewed ordinary mathematics, not Lean.

## Printed route and its domain

Use the [pinned edition](../sources/masullo/README.md). The
[accepted rendered gluing interface](isotypic-fourier-gluing-q-sqrt-minus-five.md#source-interface)
for (6.3.2.10)–(6.3.2.11), p. 305, makes the forward multiplier the
**omitted** product $D=L_{\Sigma_F-S''}(\chi,\cdot)$, not the retained
or completed product. The [stage and character check](isotypic-fourier-gluing-q-sqrt-minus-five.md#exact-global-normalization-at-the-stage-containing-the-different)
puts the nontrivial ideal-class character of $\mathbb Q(\sqrt{-5})$
at $S''=S_\infty\cup\{\mathfrak p_2,\mathfrak p_5\}$ in the case
$\chi|_{C_F^1}\ne1$, with no polar factor. The paragraph after
(6.3.2.13) takes a limit in the product of two half-plane spaces,
not in the overlap kernel. In particular, write $H=\{\Re s>0\}$ and
$X=A\mathcal S(H)$. The forward limit $h$ need only belong to $X$.
The [accepted topology check](isotypic-local-closed-range-q-sqrt-minus-five.md#printed-definition-and-corrected-product)
identifies the right factor with the seminorms
$$
p_{[a,b],n}(h)=\sup_{a\le\sigma\le b,\ t\in\mathbb R}
             (1+|t|)^n |h(\sigma+it)|,
\qquad 0<a\le b<\infty,\quad n\in\mathbb Z_{\ge0}.
$$
The sampling defect on the left does not affect this right factor.

The paragraph invokes Theorem B.3.2.1, pp. 605–606, with reciprocal
bounds at selected horizontal levels on $[-\varepsilon,1+\varepsilon]$,
$0<\varepsilon<1$, and claims membership in $X$ using the residue
theorem and Lemma D.3.1.1, pp. 797–799. For a residue-theorem
application with $h$ as the holomorphic test, the theorem requires that
it be uniformly Schwartz on a larger open strip containing the closed
abscissa interval $[a,b]$. This is a local-strip assumption, not an
entire-function assumption. On an enlarged strip still in $H$, the
numerator satisfies it by the interior seminorms. But the full strip
named on p. 306 contains $s=0$, where $h$ need not extend. Even an
actual multiple $h(s)=D(s)e^{s^2+1/s}$, hence a constant sequence of
multiples, has an essential singularity at zero: The exponential
factor is rapid on every interior strip and the nonzero entire $D$
can vanish there only to finite order. This tests the full-strip
substitution, not the claimed closed range.

One can truncate the horizontal segments to positive abscissas,
and use the Euler product for the region to the right of $1$.
That does not supply both vertical-side inputs for a smaller
rectangle that reaches into the critical strip. The bound in
Corollary B.6.1.8, p. 643, (B.6.1.45), is on $[-1,2]+iT_k$,
not on all ordinates of fixed abscissas. Definition B.3.1.1(3), p. 604,
requires two pole-free vertical lines on which the meromorphic
factor grows at most polynomially. Selecting horizontal edges does
not provide those lines or bounds. The conclusion in (B.3.2.1)–(2),
p. 606, concerns a residue limit and absolutely convergent vertical
integrals. To use a Cauchy kernel for pointwise decay would require
control of the vertical integrals uniformly in the evaluation point.
The citation does not give that argument. Lemma D.3.1.1 upgrades
already-bounded $s^N$-weighted functions on interior strips to
weighted bounds for derivatives; it does not supply the order-zero
estimate. This is a missing inference in the cited route, not a
claim that no modified rectangular argument can work.

## Interior-circle repair

The [accepted finite factorization](isotypic-euler-factorization-q-sqrt-minus-five.md#the-norm-test-and-the-grouped-euler-polynomials)
is for the product at $S_\infty$. Deleting the factors at the two
places retained at $S''$ gives precisely
$$
D(s)=(1+2^{-s})(1-5^{-s})L(s,\chi_{-4})L(s,\chi_5).
$$
The identity first holds by absolute convergence on $\Re s>1$,
and then by continuation. For $\sigma\ge u>0$, the two elementary
factors are bounded. For either Dirichlet character $\psi$, bounded
periodic partial sums $A_\psi(x)=\sum_{1\le n\le x}\psi(n)$ give
$L(s,\psi)=s\int_1^\infty A_\psi(x)x^{-s-1}\,dx$ by summation by
parts and continuation. The integral is absolutely and locally
uniformly convergent on $H$, and gives
$|L(s,\psi)|\le |s|\|A_\psi\|_\infty/u$. This is the first step of
the [accepted growth argument](isotypic-good-heights-q-sqrt-minus-five.md#upper-growth-and-anchor),
and gives polynomial growth on every bounded closed interior strip.
The Euler products on $\Re s=A>1$ give the lower bound
$|D(A+it)|\ge d_A=(1-2^{-A})(1-5^{-A})/\zeta(A)^2>0$;
no bound from Appendix B is used in the repair.

Fix a target $[a,b]$ as above. Take $A>\max(b,1)$ and fix
$A-a<r_1<r_2<r_3<R<A$. For every $t\in\mathbb R$ the point
$\sigma+it$, $a\le\sigma\le b$, lies inside radius $r_1$ around
$c=A+it$. The whole closed disk of radius $R$ lies in the fixed
interior strip $J=[A-R,A+R]$. Put $M=C(1+|t|)^k\ge1$ for a bound
on $|D|$ on the disk, with constants independent of $t$.

1. Jensen bounds the total order $N$ of the zeros in $|s-c|\le r_3$
   by $\log(M/d_A)/\log(R/r_3)$, increasing $M$ if necessary.
   Use radii tending to $R$ from below if there are boundary zeros.
   Divide out their monic full-order product $P(s)$, and write
   $g=D/P$ with singularities filled. On $|s-c|=R$ every factor
   has modulus at least $R-r_3$, so the disk bound for $|g|$ is
   $M'=M\max(1,(R-r_3)^{-1})^N$ by maximum modulus. At $c$,
   $|g(c)|\ge d_A/\max(1,r_3)^N$.
2. Apply Harnack to the nonnegative harmonic function
   $\log M'-\log|g|$ on the open radius-$r_3$ disk, where $g$ is
   zero-free. On $|s-c|\le r_2$ the Harnack factor is at most
   $(r_3+r_2)/(r_3-r_2)$. The bounds on $M'$ and $|g(c)|$ make
   the resulting upper bound $O(\log(2+|t|))$. Since $M'\ge1$,
   this gives a uniform polynomial lower bound for $|g|$ there.
3. For each zero $\rho$, the integral over $r_1\le r\le r_2$ of
   $\log^+(1/|r-|\rho-c||)$ is at most $2$. Thus one radius $r$
   in this interval avoids all zero radii and has total loss,
   counted with multiplicity, at most $4N/(r_2-r_1)$; for $N=0$
   any radius works. On its entire circle the reverse triangle
   inequality bounds $-\log|P(s)|$ by that loss. Combining with
   Step 2 gives $|D(s)|^{-1}\le C'(1+|t|)^K$ on the circle,
   with a fixed integer $K\ge0$. The chosen radius may depend on
   $t$ but never on the numerator. This works for every ordinate
   and does not require a horizontal sequence.

For $h\in X$ whose quotient $q=h/D$ is holomorphic on $H$, apply
maximum modulus to $q$ on the selected disk. Its boundary points
$w$ have $\Re w\in J$ and $|\Im w-t|\le R$, so the weights
$1+|\Im w|$ and $1+|t|$ are comparable with constants depending
only on $R$. It follows that for every $n\ge0$,
$$
p_{[a,b],n}(q)\le C_{a,b,n}\,p_{J,n+K}(h).
$$
Cauchy's derivative estimates on disks of fixed small radius inside
a slightly enlarged target strip also give every weighted derivative
bound. In particular there is no estimate at $\Re s=0$ or on any
extension of $h$.

## Closed range, evidence, and next check

Multiplication by $D$ on $X$ is continuous by polynomial upper
bounds. Its image is exactly the common zero-jet kernel
$$
\{h\in X:h^{(j)}(\rho)=0\text{ for all }D(\rho)=0,
                \ \rho\in H,\ \ 0\le j<\operatorname{ord}_\rho D\}.
$$
Indeed, local Taylor division under these conditions gives the
holomorphic quotient, and the estimate puts it in $X$. Evaluation
of each jet is continuous by Cauchy and the interior seminorms.
So an arbitrary limit of multiples has the needed jets, the image
is closed, and the same estimate makes the inverse on it continuous.
The disk proof works for any holomorphic multiplier on $H$ with
polynomial upper growth on bounded closed interior strips and
anchors arbitrarily far to the right with polynomial reciprocal
bounds on the anchor lines. Replacing $d_A$ in the proof by
$d_A(1+|t|)^{-k_A}$ keeps all logarithmic losses of the same order.
For the explicit product here the stronger constant bound holds
at every $A>1$.

The worker read the p. 306 abscissa interval and membership claim,
the larger-strip inclusion of B.3.2.1, p. 605, the vertical growth
phrase of B.3.1.1(3), p. 604, the integral form at (B.3.2.2), p. 606,
the horizontal domain and bound at (B.6.1.45), p. 643, and the
boundedness hypothesis of D.3.1.1, p. 797, in rendered crops with
layout for context. Reviewer `behueme` independently checked the
statements by extraction, including the p. 306 residue paragraph,
and separated the horizontal and vertical inputs, local strip
assumption, and integral conclusion. They could not read the p. 306
or p. 605 crops reliably and did not independently verify pixels.
The [map and topology readings](#printed-route-and-its-domain) are
inherited as credited above, not new readings. Reviewer `JJphgfh`
independently applied those accepted interfaces and checked the
factor removal, growth and anchor hypotheses, full-order disk
factorization, uniform circle bound, and half-plane seminorm
conclusion mathematically, not by a source reading. Both review
transcripts are in Yah `01a20477-8a8f-70ac-827f-a84a25011bc0`
(base `1088bcbba66b4ac4f9ea9824afe2c61aa6db6368`).

**Next bounded check:** At (6.3.2.11), p. 305, test transport of this
estimate to the reflected multiplier by $s\mapsto 1-s$, checking
the conjugated character and the two-ended topology separately.
That would advance the left-factor membership implication in the
closed-range paragraph on p. 306. The closed embedding of the pair
$T_{S'',\chi}$, the whole-plane restriction/gluing topology, and
surjectivity are not checked here. The earlier local closed range
and normalization $L\circ\overline\pi_{S''}$ are unchanged.
