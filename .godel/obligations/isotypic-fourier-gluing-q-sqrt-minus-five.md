# The reflected insertion on the quadratic class isotype

**Result (reviewed ordinary mathematics, not Lean):** For
$F=\mathbb Q(\sqrt{-5})$ and its nontrivial ideal-class character $\chi$,
the literal pair in (6.3.2.11) fails to glue in (6.3.2.13) already at
$S'=S_\infty\cup\{\mathfrak p_2\}$. This stage meets the printed
hypotheses. Its reflected multiplier omits $5^{1/2-s}$, the contribution
from Fourier transforming the inserted unit ball at $\mathfrak p_5$.
The smaller stage $S_\infty$ fails the printed Picard-group hypothesis,
but has a separate [isotypic insertion isomorphism](isotypic-exhaustiveness-q-sqrt-minus-five.md);
there the corresponding missing factor is $20^{1/2-s}$. The factors
restore agreement for all tests at these stages, with no local moment
conditions. This is a mismatch in the stated gluing step, not a
refutation of the Global Converse Theorem.

## Source interface

**Literal route.** In the digest-matched [pinned edition](../sources/masullo/README.md),
(6.3.2.10), p. 305, uses the local pair $Z_S(f,c_s)$ and
$Z_S(\widehat f,\widehat c_s)$, with the $S$-local Fourier transform as
in (5.4.1.2), pp. 265–266. Use the norm section $t\mapsto(\sqrt t,1,\ldots)$,
on which $\chi=1$, so $c_s$ is the local restriction of $\chi|\cdot|_F^s$
and $\widehat c_s$ that of $\chi^{-1}|\cdot|_F^{1-s}$. Here $\chi^{-1}=\chi$.
The local domains are $\Re s>0$ and $\Re s<1$, respectively.
Equation (6.3.2.11), p. 305, multiplies these legs by
$L_{\Sigma_F-S}(\chi,s)$ and $L_{\Sigma_F-S}(\bar\chi,1-s)$, with no
polar multiplier since $\chi|_{C_F^1}\ne1$. The quotient in (6.3.1.6),
p. 303, is the completed product divided by the retained local factors,
not a Fourier-corrected Euler product. The inherited rendered
[completed-product](isotypic-inverse-range-q-sqrt-minus-five.md#verified-completed-product-and-divisibility)
and [finite-product](isotypic-euler-factorization-q-sqrt-minus-five.md#manuscript-interface)
readings give the omitted product on $\Re s>1$ and hence its continuation.
Equation (6.3.2.13), p. 306, subtracts the two outputs on $0<\Re s<1$;
the next sentence asserts $\operatorname{im}(T_{S,\chi}U_{S,\chi})\subseteq
\ker R_{S,\chi}$.

**Fourier route.** The insertion appends $1_{O_v}$ at the omitted
places, by (2.1.4.3), p. 71, and the inductive limit (5.2.3.2). The
local equation (3.3.1.2), p. 129, compares the forward zeta integral
with $\rho_S(c_s)$ times the local reflected one, with $\rho_S$ formed
only from places in $S$. The global equation (3.2.2.2), p. 124 (proof on
pp. 126–127), compares insertion with its **global Fourier transform**,
not with insertion of the $S$-local Fourier transform. Example A.3.1.10,
(A.3.1.8), p. 558, uses the standard trace character and self-dual
additive measure: $\widehat{1_{O_v}}=\nu_v(O_v)1_{\mathfrak d_v^{-1}}$.
The correction is therefore not part of the printed $T_{S,\chi}$, nor
can the $S$-local equation supply a factor at an omitted place.

**Printed scope.** Page 305 distinguishes the embedding (6.3.2.9)
from the stage chosen for the proof: $S$ contains infinity, has
$\mathrm{Pic}(\mathcal O_{F,S})=1$, and $\chi$ is unramified outside
$S$. Theorem 6.2.1.1(2), p. 295, and Terminology 6.3.1.1, p. 303, use
these conditions. At $S_\infty$, the class group has order two, so it
is not the chosen stage. Inverting $\mathfrak p_2$ kills its generating
class, so $S'$ qualifies even though it omits $\mathfrak p_5$. The
character is trivial on every finite unit group. The norm-one idèle
$(\sqrt 2,\varpi_2,1,\ldots)$ lies at $S'$ after taking omitted entries
to be $1$, has value $-1$, and witnesses nontriviality both globally and
on the restricted norm-one isotype. The requirement to include the
field-ramified places in Example A.3.1.11, pp. 558–559, is for the
lattice duality and covolume-one normalization, not the product
self-dual measure used for $Z_S$; §3.3.1, p. 128, explicitly distinguishes
the latter from that additional characterization.

**Evidence and review:** The worker and independent reviewer `FjvFwqA`
(transcript Yah `01a20454-3ea6-790c-84ec-d5a38f3affd6`, reviewed base
`4ce485fba3b33c37f7e3f33d30783a6fcded4599`) inspected the rendered
p. 305 stage choice, local pair, and multiplier, the p. 306 subtraction
and kernel claim, and the displays on pp. 71, 124, 129, 266, 303, and
558 cited above. The reviewer confirmed from pixels
on p. 128 the distinction between self-duality and lattice normalization.
Theorem 6.2.1.1 corroborates the stage conditions. The scope of Theorem
5.4.1.1 and the p. 561 measure definition were extraction corroboration,
as was the proof on pp. 126–127, not new rendered verification.
The reviewer separately checked the literal substitution and the
true global Fourier calculation at $S'$, the membership of the Gaussian
class, and the existence of a real nonzero comparison point by the
identity theorem. The explicit $s=3/4$ point below is an additional
mathematical check. Prior renderings of the completed and finite products
are credited in their accepted notes, not reread here.

## Omitted balls and their Mellin multipliers

Write $\alpha=\sqrt{-5}$. In the integral basis $(1,\alpha)$ the trace
pairing has matrix $\operatorname{diag}(2,-10)$. Its dual lattice is
$(2\alpha)^{-1}O_F$, so the different is $(2\alpha)$. The prime
$\mathfrak p_2$ over $2$ has $q_2=2$, $\mathfrak p_2^2=(2)$, and is the
nonprincipal class from the insertion audit. The prime $\mathfrak p_5$
over $5$ has $q_5=5$ and is the principal ideal $(\alpha)$ of norm $5$.
Thus the different exponents $d_v=v(2\alpha)$ are $2$ at $\mathfrak p_2$,
$1$ at $\mathfrak p_5$, and $0$ elsewhere. Put
$a_v=\chi_v(\varpi_v)$. Then $a_2=-1$ and $a_5=1$; $\chi_{\mathfrak p_5}$
is trivial on the entire local multiplicative group, not just on units.

For $u_v=\mu_v(O_v^\times)$ and $L_v(w)=(1-a_vq_v^{-w})^{-1}$,
valuation shells give $Z_v(1_{O_v},\chi_v|\cdot|^w)=u_vL_v(w)$ for
$\Re w>0$. The trace annihilator of $O_v$ is
$\mathfrak d_v^{-1}=\varpi_v^{-d_v}O_v$; the character integral on $O_v$
is its mass on that annihilator and zero off it, by translation
invariance. Self-duality gives $\nu_v(O_v)=q_v^{-d_v/2}$. Applying the
same shell sum at $w=1-s$ to the transformed indicator gives

$$
Z_v(\widehat{1_{O_v}},\chi_v^{-1}|\cdot|^{1-s})
 = u_v L_v(1-s)\,a_v^{d_v}q_v^{d_v(1/2-s)}.
$$

**Lean (finite local test only):** [FiniteCompletionFourierSquare](../../Proofs/Theorems/FiniteCompletionFourierSquare.lean)
proves `finiteCompletionFourier_square_integers_eq_iff` and constructs the Haar
fixing this test under the double transform. [FiniteCompletionFourierMellin](../../Proofs/Theorems/FiniteCompletionFourierMellin.lean)
proves the displayed identity (`finiteCompletionFourier_reflectedMellin`) for
an unramified self-inverse unitary character at the place, with absolute
convergence exactly for $\Re s<1$. The multiplicative Haar is independent.
These results do not formalize the global product or gluing argument.

The factors relative to the reflected unit-ball Mellin transforms are
as follows:

| Omitted place | Fourier transform of $1_{O_v}$ | Relative reflected factor |
| --- | --- | --- |
| $\mathfrak p_2$ | $2^{-1}1_{\varpi_2^{-2}O_v}$ | $(-1)^2 2^{1-2s}=2^{1-2s}$ |
| $\mathfrak p_5$ | $5^{-1/2}1_{\varpi_5^{-1}O_v}$ | $5^{1/2-s}$ |
| Other finite places | $1_{O_v}$ | $1$ |

At $S=S_\infty$ put $E(s)=20^{1/2-s}$. With the product measures (A.3.2.2),
(A.3.2.5), and (A.3.4.2), $A:=\prod_{v\notin S}u_v=20^{-1/2}$.
The exact multipliers of the local zeta integrals are therefore
$A L_f(s,\chi)$ forward and $A E(s)L_f(1-s,\chi)$ reflected. Dropping the
common $A$ (equivalently, taking omitted multiplicative unit masses one)
is harmless for gluing; dropping $E(s)$ is not. These are identities of
the unfolded integrals first on $\Re s>1$ for the forward leg and
$\Re s<0$ for the reflected leg, where the omitted products converge
absolutely. The multipliers on the overlap are their continuations,
not termwise products there.

## Gaussian discrepancy and boundary cancellation

Take $f(z)=\exp(-2\pi|z|^2)$. With trace character
$e^{4\pi i\Re(zy)}$ in the pairing and additive measure $2\,dx\,dy$,
the two real Gaussian integrals give $\widehat f=f$. In particular,
$f(0)=\widehat f(0)=1$. With $|z|_\infty=|z|^2$ and the multiplicative
measure $2\,dx\,dy/|z|^2$, the angular integral and the change of variable
$t=|z|^2$ give the local pair $G(s),G(1-s)$, where

$$
G(s)=2\pi(2\pi)^{-s}\Gamma(s).
$$

For the inserted test $f\otimes\bigotimes_{v<\infty}1_{O_v}$, the two
exact unfolded zeta integrals agree by (3.2.2.2) after continuation.
Dividing out $A$ gives the identity

$$
H(s):=G(s)L_f(s,\chi)=E(s)G(1-s)L_f(1-s,\chi).
$$

Equivalently, this follows from the archimedean local equation and the
finite functional equation; the trace-dual calculation fixes the root
number $+1$ and the exponent for this particular character. The literal
formula for $R_{S,\chi}T_{S,\chi}U_{S,\chi}$, extended to this smaller
stage, is thus
$(1-E(s)^{-1})H(s)$ on the overlap. It vanishes there at zeros of $H$
and where $E(s)=1$, i.e. $s=1/2+2\pi i k/\log 20$ with $k\in\mathbb Z$.
The central-point comparison alone cannot detect the missing factor.
A nonzero point in the open overlap is checked below.

The forward local pole at $s=0$ has residue $2\pi$ and the reflected
local pole at $s=1$ has residue $-2\pi$ in the same coordinate $s$.
For a general test the corresponding residues are $2\pi f(0)$ and
$-2\pi\widehat f(0)$: Its circular average at radius $\sqrt t$ is
$f(0)+O(\sqrt t)$ as $t\downarrow0$, and likewise for $\widehat f$.
The completed function of (3.2.1.2) is entire on this nontrivial
isotype by Proposition 3.2.1.3(1), so $L_f(s,\chi)$ has a zero at $0$.
It is simple because $H(0)=E(0)H(1)\ne0$, using positivity at $1$
from the block argument below. At $0$ the omitted
$L_{\mathfrak p_2}(s)=(1+2^{-s})^{-1}$ is regular, of value $1/2$;
$L_{\mathfrak p_5}(s)=(1-5^{-s})^{-1}$ has a simple pole of residue
$1/\log 5$. More precisely, the continued product after deleting both
factors is $(1+2^{-s})(1-5^{-s})L_f(s,\chi)$ and has a double zero
there. Reinstating the $\mathfrak p_5$ pole leaves one zero to cancel
the archimedean pole. At $s=1$ the reflected variable $w=1-s$ is zero,
so the same order count applies, with the pole signs reversed in $s$.
In the other leg at each endpoint the finite argument is $1$, where
both local factors are regular (values $2/3$ and $5/4$, respectively).
The factor $E$ changes neither order count; it changes the finite
values ($E(0)=\sqrt{20}$, $E(1)=1/\sqrt{20}$). Thus the printed legs
have removable boundary poles but still fail to agree in the open
strip. No archimedean zero mode had to vanish. The global residual
functionals vanish **on the projected isotype**; they do not force
these local modes to vanish on an archimedean representative.

## In-scope control and scope of the repair

At $S'$, use $g=f\otimes 1_{O_{\mathfrak p_2}}$ for the same Gaussian
$f$ as above, and take its class in the full nontrivial isotypic
Schwartz quotient of (6.3.2.10). Its local integrals calculate $U_{S',\chi}$
on this class. The forward integral is
$u_2G(s)L_{\mathfrak p_2}(s)$, not identically zero. No moment condition
from (6.3.2.12) applies. The insertion of $g$ is the **same global test**
as at $S_\infty$. The omitted product at $S'$ is
$D'(s)=L_f(s,\chi)/L_{\mathfrak p_2}(s)$; the ball at $2$ belongs to the
local Fourier calculation and already contributes $2^{1-2s}$ there.
Thus, with the common $u_2$ divided out, the two **literal** legs are
$H(s)$ and $2^{1-2s}G(1-s)L_f(1-s,\chi)=5^{s-1/2}H(s)$, by the
same global identity above. In the **trace-dual** route the omitted ball at
$5$ adds $5^{1/2-s}$ to the latter leg, giving $H(s)$ instead. Equivalently,
when unfolding the two global integrals the common omitted unit mass is
$\prod_{v\notin S'}u_v$; it does not affect this ratio.

One can take $s=3/4$ in both tests. In fact, the
[accepted factorization](isotypic-euler-factorization-q-sqrt-minus-five.md#the-norm-test-and-the-grouped-euler-polynomials)
identifies $L_f(s,\chi)$ with $L(s,\chi_{-4})L(s,\chi_5)$ also by
continuation. The Dirichlet series converge for $\Re s>0$ by bounded
partial sums of the periodic coefficients and summation by parts.
For real $s>0$, writing $b(n)=n^{-s}$, the blocks
$b(4j+1)-b(4j+3)$ and
$b(5j+1)-b(5j+2)-b(5j+3)+b(5j+4)$ are strictly positive by monotone
decrease and strict convexity, respectively. So $H(3/4)>0$.
The two literal differences after normalization are
$(1-20^{1/4})H(3/4)$ at $S_\infty$ and $(1-5^{1/4})H(3/4)$ at $S'$;
both corrected differences are zero. Even without the explicit point,
entireness and nonvanishing on $\Re s>1$ imply nonvanishing somewhere
on any open real subinterval of the overlap.

For any $S$-local test in this isotype, global Fourier reflection and
continuation give $R_{S,\chi}T^{\rm corr}_{S,\chi}U_{S,\chi}=0$ after
multiplying the reflected multiplier by the product of the relative
factors at omitted places. More generally, the geometric shell calculation
at a place with unramified unitary $\chi_v$ works without
$\chi_v=\chi_v^{-1}$: Use $L_v(1-s,\chi_v^{-1})$ in the reflected leg,
and the relative factor is still $\chi_v(\varpi_v)^{d_v}q_v^{d_v(1/2-s)}$.
This is an identity for the unit-ball insertion and trace-dual Fourier
transform, not a general converse result. The product is finite and
nowhere zero, and it and its reciprocal have bounded derivatives on
bounded-width vertical strips. For the quadratic case, including both
finite different places in $S$ is an alternative repair allowed by the
proof's choice of stage. The witness refutes the gluing inference under
its stated stage conditions, not a proof using that stronger choice.

The [Haar normalization check](#exact-global-normalization-at-the-stage-containing-the-different)
below identifies the glued pair with the global zeta image at $S''$.

**Separate results and premises:** The [corrected inverse-range proof](isotypic-inverse-range-q-sqrt-minus-five.md)
uses the corrected multipliers to lift every target in the claimed range
at $S_\infty$. Its checked denominator switch on pp. 308–309 is separate
from this gluing counterexample. The general converse and global Lean
realization are not addressed here.

## Exact global normalization at the stage containing the different

**Result (reviewed ordinary mathematics, not Lean):** Put
$S''=S_\infty\cup\{\mathfrak p_2,\mathfrak p_5\}$. For the nontrivial
ideal-class character $\chi$ of $F=\mathbb Q(\sqrt{-5})$, the operator
induced by gluing in the paragraph after (6.3.2.13), p. 306, is
**exactly** $L\circ\overline\pi_{S''}$ on every local test class. The
scalar is one. This is not obtained by canceling an unspecified common
unit mass, as in the smaller-stage overlap comparison.

### The printed identification and the defining integrals

The paragraph after (6.3.2.13), p. 306, defines $A$ by the two
restrictions of one entire function and calls the factor of
$T_{S,\chi}U_{S,\chi}$ through $A$ the map $L\circ\overline\pi_S$.
The unnumbered line on p. 307 asserts, with generic $S$ and no scalar,
$Z(\pi_S f,\chi|\cdot|_F^s)=Z_S(f,\chi_S|\cdot|_{F,S}^s)
L_{\Sigma_F-S}(\chi,s)$. This is the **printed route**: By the
[accepted source interface](#source-interface), its right side is
precisely the forward leg of (6.3.2.10)–(11), p. 305, since there is
no polar multiplier. The choice of stage is satisfied: Inverting
$\mathfrak p_2$ already kills the class group, the norm-one idèle
with component $\varpi_2$ and Archimedean component $\sqrt 2$ still
witnesses $\chi|_{C_F^1}\ne1$, and $\chi$ is unramified at every
finite place. Take the norm section $t\mapsto(\sqrt t,1,\ldots)$,
so $\chi$ has no twist on the section. The domain is the full
isotypic Schwartz quotient, not its zero-moment subspace.

For the **defining-integral route**, write $c_s=\chi|\cdot|_F^s$ and
$h=\pi_S f=f\otimes\bigotimes_{v\notin S}1_{O_v}$. The descended
insertion sends $[f]$ to $[h]$, with no rescaling, by (2.1.4.3), p. 71,
(5.2.3.2), p. 233, and (6.3.2.9), p. 305. The kernel criterion
(5.1.2.2), p. 224, makes evaluation of $L(h,c_s)=Z(h,c_s)$
well-defined on this class. In particular $L$ is the Mellin transform
of the periodization against $\bar\mu$ in (3.2.2.3), p. 124, or
equivalently the radial Mellin transform of the homogeneous average in
(3.2.2.5), p. 125.
The latter does not integrate a second time against norm-one Haar.

On $\Re s>1$, apply counting Weil to $h(x)c_s(x)$, which is absolutely
integrable. Definition A.3.2.1, pp. 559–560, uses counting measure on
$F^\times$ to induce $\bar\mu$ from $\mu$. Since $c_s$ is constant on
each principal fibre, (3.2.2.11), p. 127, gives

$$
(L\circ\overline\pi_S)([f])(s)
 =\int_{C_F}\sum_{\xi\in F^\times}h(\xi x)c_s(x)\,d\bar\mu(x)
 =\int_{\mathrm{GL}_1(\mathbf A_F)}h(x)c_s(x)\,d\mu(x).
$$

There is no quotient-to-idèle scalar: Each $\xi$ counts once. In
particular the norm-one volume in (A.3.2.1) is not a multiplier for
this unfolding. The upstairs measure is the restricted product in
(A.3.2.5), p. 560; the local pairing (3.3.1.1), p. 129, uses the
product over $S$ in (A.3.4.2), p. 561, of the **same** local measures.
Thus the two integrals do not differ by a renormalization at a
retained place.

### Euler tail and nonzero control

For $a_v=\chi_v(\varpi_v)$ and $u_v=\mu_v(O_v^\times)$, each omitted
ball contributes $u_v/(1-a_vq_v^{-s})$ by valuation shells. This
uses unramifiedness of the character there; the separate condition
$u_v=1$ depends on the field discriminant, by (A.3.2.2), p. 560.
Factor first on stages allowing arbitrary valuations at finitely many
places, including $S$ and the exceptional unit masses, and unit
entries elsewhere. These stages exhaust the idèles; absolute
integrability and absolute Euler convergence on $\Re s>1$ justify
the limit. This keeps $f$ as a single $S$-block, so no pure-tensor
hypothesis on $f$ is needed. With $D_S(s)=L_{\Sigma_F-S}(\chi,s)$,

$$
Z(\pi_S f,c_s)
 =\left(\prod_{v\notin S}u_v\right) Z_S(f,c_s|_S)D_S(s)
 \qquad(\Re s>1).
$$

At $S''$, the retained unit masses are $u_2=1/2$ and $u_5=1/\sqrt5$,
using the different exponents computed [above](#omitted-balls-and-their-mellin-multipliers).
Every omitted $u_v$ is one. The printed p. 307 identity therefore
holds as written at this stage. The formula for the omitted mass is
reusable over any number field on $\Re s>1$ for an inserted local
Schwartz test and a unitary character unramified off $S$, with the
same product Haar conventions. If an exceptional unit mass is omitted,
the **global** integral is the printed forward expression multiplied
by $\prod_{v\notin S}u_v$, not the other way around. This is a forward
formula, not a claim that the literal reflected leg glues at such a
stage.

For the reflection at $S''$, every omitted ball is Fourier-fixed,
so $\widehat{\pi_{S''} f}=\pi_{S''}\widehat f$ with the actual
self-dual measures. On $\Re s<0$, apply the same absolute unfolding
to $\widehat f$ at $1-s$ with $\chi^{-1}=\chi$, and use (3.2.2.2),
p. 124. This gives the printed reflected leg with the same scalar
one. By holomorphic continuation the legs are restrictions of
$L\circ\overline\pi_{S''}$ on $\Re s>0$ and $\Re s<1$ respectively.
They agree on the overlap, and uniqueness of the glued function
identifies the operator in p. 306. The same measure and Fourier
argument applies at larger stages on this isotype, and character- and
field-unramifiedness off $S$ suffice for these two absolute evaluations
in general. No general Converse Theorem is used.

For a nonzero control take $f_0=e^{-2\pi|z|^2}\otimes
1_{O_{\mathfrak p_2}}\otimes1_{O_{\mathfrak p_5}}$. The Gaussian
factor is self-dual; the retained balls need not be. The local
forward integral is

$$
2\pi(2\pi)^{-s}\Gamma(s)\,
\frac{1/2}{1+2^{-s}}\,\frac{1/\sqrt5}{1-5^{-s}}.
$$

At $s=2$ the omitted Euler product is strictly positive by absolute
convergence and real unitary coefficients $\pm1$. Both global and
glued values are $G(2)L_f(2,\chi)/\sqrt{20}>0$, in the notation of
[the Gaussian calculation](#gaussian-discrepancy-and-boundary-cancellation).
In particular $[f_0]$ cannot be the zero class, and the ratio one is
not a consequence of comparing two vanishing expressions.

### Evidence and limits

The worker and reviewer `cUqiVab` (transcript Yah
`01a20460-7cf8-7714-b62e-3ac1a6879123`, reviewed base
`beec9711ce91e866712d93df734f572d220deac1`) inspected readable pixels
from the digest-matched [pinned PDF](../sources/masullo/README.md).
On the printed route the reviewer confirmed the closing identification
on p. 306 and the unnumbered identity with no scalar on p. 307. On the
defining-integral route the reviewer confirmed $\bar\mu$ in (3.2.2.3),
p. 124, and the quotient, principal sum, and $\mu$ integral in
(3.2.2.11), p. 127; the counting clause of Definition A.3.2.1,
p. 559; the finite mass and global product (A.3.2.2) and (A.3.2.5),
p. 560; and the $S$-product (A.3.4.2), p. 561, used in the local
integral (3.3.1.1), p. 129. This resolves the previous extraction-only
reading of the $S$-product. The worker also inspected the radial formula
(3.2.2.5), p. 125. The reviewer's additional check of the quotient and
induced-map definitions in (5.2.2.3)–(4) and (5.2.3.14) was textual,
not a new rendering. The reviewer checked the counting unfolding, absolute
Euler factorization, Fourier compatibility, and nonzero test as
mathematics, not by assuming the p. 307 identity. Stage, multiplier,
insertion, and Fourier readings are inherited from the
[accepted source interface](#source-interface); their applicability,
not their rendering, was rechecked here.

The [checked raw integral](hecke-right-line-majorant.md#checked-exhaust-the-raw-zeta-integral-above-one)
and the [checked counting Weil bridge](single-place-norm.md#full-class-counting-weil-and-the-absolutely-integrable-weighted-pairing)
provide separate Lean inputs, not a formalization of this gluing
identity. This audit identifies the map, not closedness or
surjectivity of its image. The printed smaller-stage gluing remains
incorrect; the general converse and a global Lean realization
remain separate.
