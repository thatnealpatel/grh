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

**Next bounded source check:** At $S''=S'\cup\{\mathfrak p_5\}$ this
gluing obstruction is absent. In the factorization just after (6.3.2.13),
p. 306, and the unnumbered unfolding on p. 307, check whether the glued
pair then agrees exactly with $L\circ\overline\pi_{S''}$ with the printed
global and $S''$-local Haar conventions, or requires a common scalar.
This checks the identification of the glued function with the global
zeta image, not closedness or surjectivity of that image.

**Separate results and premises:** The [corrected inverse-range proof](isotypic-inverse-range-q-sqrt-minus-five.md)
uses the corrected multipliers to lift every target in the claimed range
at $S_\infty$. Its checked denominator switch on pp. 308–309 is separate
from this gluing counterexample. The general converse and global Lean
realization are not addressed here.
