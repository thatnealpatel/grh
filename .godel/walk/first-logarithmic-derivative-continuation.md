# The first continuation retains the wrong zeta pole sign

**Printed passage.** Masullo, *The Music of the Primes*, printed p. 30,
claim directly after §1.4.5, first paragraph from “We deduce that” through
“(when $\chi|_{C_F^1}=1$).” Write $D_a=\{s:\Re s>a\}$,
$F_\chi(s)=L_f'(s+1/2,\chi)/L_f(s+1/2,\chi)$, and
$P(s)=(s+1/2)^{-1}+(s-1/2)^{-1}$. Masullo claims that
$F_\chi-\delta P$ is holomorphic on $\operatorname{Int}K$ for any
$K\subset D_a$ by analytic continuation from the right. He then infers
that $F_\chi$ has no poles in $D_a$ except possibly $s=1/2$ in the
trivial norm-one isotype. The next paragraph, beginning “Since $a>0$
is arbitrary,” is not part of this finding.

Chapter Markdown and PDF layout extraction located the paragraph in the
[digest-verified edition][edition]. Raster OCR checked the prose, and
direct inspection of rendered crops confirmed the subtraction of the
polar term, the plus between the two reciprocals, the denominators,
and the indicated continuation domains.

**Checked scope.** The signed holomorphy assertion is false. Reuse the
[preceding residue check][assembly] with $F=\mathbb Q$, $\chi=1$,
$a=1/4$, and $K$ the closed disc centered at $1$ of radius $5/8$. This
disc is inside $D_a$, meets $\Re s>1$ in its interior, and has $1/2$
in its interior, so it is admissible even under the earlier conditions
on $K$. The simple pole of $\zeta$ at $u=1$ gives residue $-1$ for
$F_1(s)$ at $s=1/2$. Here $\delta=1$, and $P$ has residue $+1$ there.
The printed difference has residue $-2$, so its germ on the
right-half-plane overlap cannot have a holomorphic continuation to the
whole disc. This uses uniqueness of meromorphic continuation on the
connected disc, not a divergence estimate at its boundary.

The weaker conclusion about absence of other poles at fixed $a$ would
follow from a valid holomorphic remainder after subtracting the actual
polar part. There is a separate character convention to fix: §1.4.1
(p. 28) merely fixes $\chi\in\widehat{C_F}$. If unrestricted characters
are intended, take $F=\mathbb Q$ and $\chi=|\cdot|_{\mathbb Q}^{-it}$
for real $t\ne0$. The character is trivial on $C_F^1$, but the finite
Euler product of Definition 3.2.1.4, (3.2.1.7), p. 124, gives
$L_f(u,\chi)=\zeta(u-it)$, first on $\Re u>1$ and then meromorphically.
The exceptional pole in $D_{1/4}$ is now $s=1/2+it$, not the printed
$s=1/2$. The character quantifier on p. 28 and the sign of the Euler
exponent on p. 124 were checked in rendered crops. To fix the exception
at $1/2$ in the trivial norm-one isotype, one needs to use $\chi=1$ as
its representative. Even under that convention $F_1+P$ only removes the
known local pole; it does not control poles at zeros elsewhere.
For the trace route, the missing input is a correctly normalized
limiting trace identity giving a holomorphic pole-subtracted remainder
on $D_a$ or on connected domains covering it and linked to the
right-half-plane identity. The [rational subtraction repair][repair]
is conditional on a strip-restricted fixed-test trace, not a proof of
that input. The residue counterexample refutes the signed remainder
regardless of the character convention. Neither check refutes the
weaker pole-location conclusion with normalized representatives or
settles a zero-location conjecture.

**Provenance.** The continuation argument is Masullo's. The residue
calculation applies the reviewer's preceding rational check to the
printed remainder. At the Mathlib pin
`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`,
`riemannZeta_residue_one` gives the punctured limit of
$(u-1)\zeta(u)$ at $1$ equal to one, and `analyticOn_riemannZeta`
gives analyticity off $1$. Neither Lean statement asserts the
continuation of the printed difference or the weaker pole-location
conclusion. No new Lean theorem is added. Independent Yah reader
`continuation-reader` (`vnhfGsM`, session
`01a205ac-86ff-705f-8ec7-1e6d8f49a762`) checked the rendered p. 30
signs, the admissible disc and residue, the scope caveat for norm
twists, and the two signatures at GRH revision
`0167563648f5b5423c5e54c5d8b10a1c3f38f61a`.

[assembly]: assembled-logarithmic-derivative.md
[edition]: ../sources/masullo/README.md
[repair]: ../obligations/trace-to-zeros.md#fixed-parameter-subtraction-over-the-rationals
