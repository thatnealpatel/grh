# The reflected insertion on the quadratic class isotype

**Result (ordinary mathematics, not Lean):** For $F=\mathbb Q(\sqrt{-5})$,
its nontrivial ideal-class character $\chi$, and $S=S_\infty$, the
[isotypic insertion isomorphism](isotypic-exhaustiveness-q-sqrt-minus-five.md)
does not make the literal pair in (6.3.2.11) glue. With the forward
multiplier normalized to $L_f(s,\chi)$, the reflected multiplier is
$20^{1/2-s}L_f(1-s,\chi)$, not $L_f(1-s,\chi)$. The extra factor is a
nowhere-zero entire function. It gives gluing for all tests in this
isotype, with no local moment conditions. This is a mismatch in a proof
step, not a refutation of the Global Converse Theorem.

## Source interface

Locations and formula readings are provisional, from layout extraction
of the digest-checked [pinned edition](../sources/masullo/README.md), not
inspection of rendered pages. On pp. 305–306, (6.3.2.10) uses the two
$S$-local transforms at $c_s=\chi|\cdot|^s$ and its dual
$\widehat c_s=\chi^{-1}|\cdot|^{1-s}$. Here $\chi^{-1}=\chi$, and its
restriction to $\mathbb C^\times$ is trivial. The input pair is
holomorphic on the respective half-planes $\Re s>0$ and $\Re s<1$, not
necessarily across their respective endpoints. The stated $T_{S,\chi}$
in (6.3.2.11) uses $L_{\Sigma_F-S}(\chi,s)$ and
$L_{\Sigma_F-S}(\chi,1-s)$ with no polar multiplier because
$\chi|_{C_F^1}\ne 1$. At $S_\infty$, (6.3.1.6) and (3.2.1.7) give
$L_{\Sigma_F-S}(\chi,s)=L_f(s,\chi)$. Equation (6.3.2.13) subtracts the
two outputs on $0<\Re s<1$ and cites the local (3.3.1.2) and global
(3.2.2.2) functional equations.

The global equation compares the insertion with its **global Fourier
transform**, not with the insertion of the $S$-local Fourier transform.
The relevant source dependency is Example A.3.1.10, (A.3.1.8), p. 558
(also Remark A.3.4.2, p. 562). With the trace character of (A.3.1.7) and
self-dual measure of (A.3.1.2), the local transform of $1_{O_v}$ is
$\nu_v(O_v)1_{\mathfrak d_v^{-1}}$. The transform is not a unit-ball
insertion when the place is ramified in the field extension, even if
the multiplicative character is unramified there. The accepted rational
[`RationalAdeleUnramifiedFourier`](../../Proofs/Theorems/RationalAdeleUnramifiedFourier.lean)
computes the self-annihilating unit-ball case, not these omitted
trace-dual balls.

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

The factors relative to the reflected unit-ball Mellin transforms are
as follows:

| Omitted place | Fourier transform of $1_{O_v}$ | Relative reflected factor |
| --- | --- | --- |
| $\mathfrak p_2$ | $2^{-1}1_{\varpi_2^{-2}O_v}$ | $(-1)^2 2^{1-2s}=2^{1-2s}$ |
| $\mathfrak p_5$ | $5^{-1/2}1_{\varpi_5^{-1}O_v}$ | $5^{1/2-s}$ |
| Other finite places | $1_{O_v}$ | $1$ |

Set $E(s)=20^{1/2-s}$. With the literal product measures (A.3.2.2),
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
number $+1$ and the exponent for this particular character. The printed
$R_{S,\chi}T_{S,\chi}U_{S,\chi}$ on this test is thus
$(1-E(s)^{-1})H(s)$ on the overlap. It vanishes there at zeros of $H$
and where $E(s)=1$, i.e. $s=1/2+2\pi i k/\log 20$ with $k\in\mathbb Z$.
It is nonzero for real $s<1$ sufficiently close to $1$: $E(s)\ne 1$
and $H(1)=L_f(1,\chi)\ne 0$ by the right-edge nonvanishing in
Proposition 3.2.1.3(4), applicable to this nontrivial compact isotype.
The central-point comparison alone cannot detect the missing factor.

The forward local pole at $s=0$ has residue $2\pi$ and the reflected
local pole at $s=1$ has residue $-2\pi$ in the same coordinate $s$.
For a general test the corresponding residues are $2\pi f(0)$ and
$-2\pi\widehat f(0)$: Its circular average at radius $\sqrt t$ is
$f(0)+O(\sqrt t)$ as $t\downarrow0$, and likewise for $\widehat f$.
The completed function of (3.2.1.2) is entire on this nontrivial
isotype by Proposition 3.2.1.3(1), so $L_f(s,\chi)$ has a zero at $0$.
It is simple because $H(0)=E(0)H(1)\ne0$. At $0$ the omitted
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

## Scope of the repair and next check

For any local test, the exact global transform of its insertion
has the same omitted factors as for the Gaussian. Global Fourier
reflection and continuation therefore give $R_{S,\chi}T^{\rm corr}_{S,\chi}
U_{S,\chi}=0$ on the projected quotient: Keep the printed forward
multiplier and multiply the printed reflected multiplier by $E(s)$.
This change preserves the half-plane Schwartz spaces and the
multiplier's image topology, since $E$, $E^{-1}$, and their derivatives
are bounded on each bounded-width vertical strip. This check repairs the
Mellin gluing step; it does not on its own identify the converse range.

The proof chooses $S$ with trivial localized Picard group and $\chi$
unramified outside $S$. At $S'=S_\infty\cup\{\mathfrak p_2\}$ those
conditions hold but the same omitted-ball calculation still gives a
factor $5^{1/2-s}$ on the reflected leg. Taking $S$ to contain **both**
finite different places eliminates this omission, and is possible under
the proof's large-stage choice. The smaller stage, despite the forward
isomorphism, requires the corrected multiplier. This does not disprove
the theorem or rule out its proof at a sufficiently large stage.

**Follow-up:** The [corrected inverse-range proof](isotypic-inverse-range-q-sqrt-minus-five.md)
uses these two multipliers to lift every target in the claimed range
at $S_\infty$. It propagates rapid decay through zeros by maximum
modulus at separated heights, and applies (5.4.1.3) to the resulting
pair. It also checks the omitted-to-retained denominator switch in
the rendered pp. 308–309, separately from the provisional source
reading in this note.
