# The half-plane exhaustion needs a valid fixed-width premise

**Printed passage.** Masullo, *The Music of the Primes*, printed p. 30,
claim in §1.4.5, the sentence beginning “Since $a>0$ is arbitrary.”
Write $G_\chi(s)=L_f'(s+1/2,\chi)/L_f(s+1/2,\chi)$. Masullo infers
that $G_\chi$ is holomorphic on $\{\Re s>0\}\setminus\{1/2\}$ from
the preceding fixed-$a$ pole exclusion. This finding stops before
“This implies that,” which begins the application to zeros.

Chapter Markdown and PDF layout extraction located the sentence in the
[digest-verified edition][edition]. Raster OCR checked the prose; direct
inspection of rendered crops checked the shift, the domain, and the
excluded singleton. The character convention and component
parametrization were also checked in rendered crops on pp. 12 and 29.

**Checked scope.** The exhaustion is valid conditionally: For any point
$s$ in the claimed domain choose $0<a<\Re s$. Then a neighborhood of
$s$ lies in $\{\Re s>a\}\setminus\{1/2\}$. This needs holomorphy of the
same meromorphic logarithmic derivative on those domains for a sequence
of positive $a$ tending to zero. It does not need convergence of the
holomorphic remainders as $a\to0$.

Read $\chi$ as the unitary base point used to parametrize the component
by $\chi|\cdot|_F^s$ at the end of §1.4.3 (p. 29). The second bullet
of §1.1.4 (p. 12) explicitly chooses $\chi=1$ in the trivial norm-one
component rather than an imaginary norm twist. For this convention the
half-plane claim is **open here**. The [first-continuation audit][first]
refutes the signed subtraction even for $\chi=1$, but that does not
refute the pole exclusion for this representative. The trace route
still needs, for arbitrarily small $a>0$, a correctly normalized limit
identity with a remainder holomorphic on $\Re s>a$ after subtracting
the actual polar part, or equivalent local continuations on connected
domains covering that region and matched to the right-half-plane germ.

The bare §1.4.1 wording (p. 28) fixes $\chi\in\widehat{C_F}$ without
locally restating the base-point choice. The broader reading that keeps
the deleted point fixed for unrestricted $\chi$ is false: Over
$\mathbb Q$ take $\chi=|\cdot|^{-it}$ with real $t\ne0$. At a prime $p$
the local character has value $p^{it}$ on a uniformizer and is trivial
on units. The Euler product (3.2.1.7), printed p. 124, then identifies
$L_f(u,\chi)$ with $\zeta(u-it)$ on $\Re u>1$, and uniqueness of
meromorphic continuation carries the identity further. The simple pole
of $\zeta$ at $1$ gives residue $-1$ for $G_\chi$ at $1/2+it$, a point
not deleted by the sentence. The exponent sign in the Euler product
was checked on the rendered page. This is a check on the quantifier,
not a counterexample with Masullo’s p. 12 base-point convention.

**Provenance.** The exhaustion is Masullo’s argument. The reviewer
checked its premise and applied the rational norm-twist check from the
first-continuation audit to the exhausted domain. At the Mathlib pin
`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`,
`riemannZeta_residue_one` gives the punctured limit of $(u-1)\zeta(u)$
at $1$ equal to one and `analyticOn_riemannZeta` states analyticity of
$\zeta$ off $1$. Neither says that the logarithmic derivative is
holomorphic on the claimed domain, nor identifies the twisted Hecke
Euler product. Independent Yah reader `arbitrary-a-reader` (output
`6290c6bd38f3c90166eff1a8f1a02bc3393e9339`) checked the rendered p. 30
sentence, the p. 12 and p. 28 convention distinction, the Euler factor
and residue, and the two signatures against GRH revision
`0978c8f46bb01d0499f5052bcf2d06db2100f302`. No Lean theorem is added,
and no zero-location claim is established or refuted here.

[edition]: ../sources/masullo/README.md
[first]: first-logarithmic-derivative-continuation.md
