# The weight-four spectral operator misses the circle-invariant block

**Ordinary mathematics, not Lean.** Let $G=C_{\mathbb Q(i)}$, let $H$ be
its Archimedean-only circle, and set $a=1/2$, $I=\{0\}$, and $s=4$.
Write $K=\prod_{v<\infty}\mathcal O_v^\times$ and
$$
\eta([z,u])=(z/|z|)^4,\qquad
\varphi(g)=b(\log|g|_F)\eta(g),\quad
0\ne b\in C_c^\infty((0,\log 2)).
$$
On the Hilbert space in (12.1.1.21), PDF p. 503, the actual operator
$T=P_a^{\mathrm{spec}}A(\varphi)$ satisfies
$$
TP_H=P_HT=0,\qquad T=(1-P_H)T(1-P_H),
$$
where $P_H$ is probability-Haar averaging on $H$. In fact $T$ is
supported on the full norm-one **left-action** isotype
$\overline\eta|_{G^1}$, on input and output. This is a bounded-operator
statement, independent of nuclearity, a kernel representation, or any
calculation with the Hecke zeros.

## Test and source interface

Use the [accepted circle note](trace-circle-compression-qi.md) at
`f82ec6bf8bf7fb124cf181806dc5de5fd1e72ee9` for
$G\simeq (\mathbb C^\times\times K)/\mathbb Z[i]^\times$, the embedding
of $H$, and the literal box images. This inherits the norm and class
conventions from its [angular source check](trace-spectral.md#the-averaging-boxes-must-actually-shrink),
not a new check of those passages. In the indicated model $|[z,u]|_F=|z|^2$.
Multiplication by any diagonal Gaussian unit leaves $\eta$ unchanged,
and $\eta([h,1])=h^4$ is nontrivial on $H$. The test factors through
$\mathbb C^\times/\mathbb Z[i]^\times$ by forgetting finite units.
The kernel of this quotient is the compact image of $K$. Its annihilator
in $\widehat G$ is open and isomorphic to $\mathbb R\times\mathbb Z$,
so it is compactly generated.
The smooth function on that Lie quotient has compact support on $G$
because the norm-one fibers are compact. This is a Bruhat test in
$\mathcal D(G)$, with $\varphi(1)=0$ and support in $1<|g|_F<2$.
For the test-function convention see §9.3.1, p. 419, Lemma D.3.6.1,
p. 819, Definition D.1.5.1, p. 760, and Remark D.1.5.5, p. 763.

For $I=\{0\}$, §10.2.1, p. 439, uses $W^{s,2}(G)$ and (10.2.1.1)
is its quotient by the closed weighted theta space $M_a$ in (10.1.1.3),
p. 434. The norm (9.1.2.3), p. 399, is the $L^2(G,w\bar\mu)$ norm with
$w(g)=(1+|\log|g|_F|^2)^2$ at $s=4$; the $a$-twist is in $M_a$,
not in this ambient norm. The order on p. 503 is convolution first.
Equation (10.4.2.5), p. 459, reads
$$
P_a^{\mathrm{spec}}A(\varphi)=S_a\bar A(\varphi)Q_a.
$$
The accompanying description gives $Q_a:W^{s,2}(G)\to W^{s,2}(G)/M_a$,
$M_a$ closed and $G$-invariant, and $S_a$ the unique lift to $M_a^\perp$.
Here $S_aQ_a=P_a^{\mathrm{spec}}$, $Q_aS_a=1$, and $\bar A$ is the
quotient convolution. The $S_a^{-1}$ in the lift position of
(10.4.2.8), p. 459, does not have this type; the support calculation
uses (10.4.2.5) and the orthogonal-lift definition. Neither
requires that $P_a^{\mathrm{spec}}$ commute with translations of
nonunit norm.

## Input cancellation and output lift

Use $U_g f(x)=f(g^{-1}x)$, the action above Definition 9.3.1.1, p. 419.
Equation (9.3.1.2) integrates $\varphi(g)U_g$ against Haar measure, with
no conjugation on $\varphi$. For $h\in G^1=\ker|\cdot|_F$, substitution
by $g\mapsto hg$ yields
$$
U_h A(\varphi)=A(U_h\varphi)=\overline\eta(h) A(\varphi),
\qquad A(\varphi) U_h=U_h A(\varphi),
$$
the second equation using commutativity of $G$. In particular
$A(\varphi)P_H=0$ by averaging the second slot over $H$. This proves
$TP_H=0$ before asking whether the projection preserves the output.

The weight is norm-radial, so $U_h$ is unitary for $h\in G^1$. Invariance
of $M_a$ under both $U_h$ and $U_{h^{-1}}$ then implies invariance of
$M_a^\perp$, and uniqueness of the orthogonal lift makes $S_a$ intertwine
the norm-one action. In particular $P_a^{\mathrm{spec}}$ commutes with
$U_h$, and $U_h T=T U_h=\overline\eta(h)T$. Averaging output gives
$P_HT=0$. Averaging against the conjugate of the eigencharacter on
$G^1$ gives the stronger full-isotype statement. The proof uses no
commutation with translations off $G^1$.

The vanishing identities apply to any compact subgroup of an abelian
translation group acting unitarily on the weighted space and preserving
the closed quotient kernel, with the test replaced by any test whose
average over that subgroup is zero. Indeed averaging the integrated
action gives $A(P_H\varphi)=P_H A(\varphi)=A(\varphi)P_H$. This includes
the operator support check for other weights invariant under that
subgroup and does not assert trace class in those settings.

## Character labels in the two printed trace routes

With the printed left action, $\varphi$ has weight
$\overline\omega$ for $\omega=\eta|_{G^1}$. In contrast, the **plus**
Mellin integrals in the trace sums (10.3.1.5), p. 449, and (10.3.2.5),
p. 454, select $\chi|_{G^1}=\overline\omega$, not $\omega$: Translating
$g$ to $hg$ multiplies $\varphi(g)\chi(g)|g|_F^{it}$, or its strip
analogue with exponent $b+it$, by $\eta(h)\chi(h)$. The Haar integral
vanishes unless this product of characters is trivial on $G^1$.

Both printed statements instead put $\overline\omega$ in the homogeneous
premise, $\omega$ in the output isotype, and $\chi|_{G^1}=\omega$ in the
summation label. Here an $\omega$-isotype means **action** eigencharacter
$\omega$, not pointwise character $\omega$: The projector in (10.1.1.8),
p. 436, averages $\overline\omega(h)U_h$, as in the quotient convention
(10.2.1.2), p. 439, and Terminology 4.3.2.1, p. 180. Thus the homogeneous
specializations have a conjugation mismatch. With the plus Mellin
integrand and printed label relation $\chi|_{G^1}=\omega$ retained, the
consistent premise would be action weight $\omega$. This comparison
checks the character selection, not whether either sum evaluates the
operator trace. In the strip notation let $\beta$ denote the real
displacement (printed $b$, unrelated to the bump). For $I=\{0\}$,
$\beta=0$ and the points are boundary points, so the character selection
is the same as in the singleton formula. The support proof does not
rely on these statements or on deciding whether the operator is nonzero.

## What the boxes omit, and what remains

Taking trace class as asserted for this $T$ in Theorem 10.4.2.1, p. 459,
the omitted trace in the [circle-compression result](trace-circle-compression-qi.md)
is the full $\operatorname{Tr}(T)$. The isometric lift in (10.4.2.5) also
identifies it with $\operatorname{Tr}(\bar A(\varphi))$: In
$M_a^\perp\oplus M_a$, $T$ is the lifted quotient operator on the first
summand and zero on the second. No spectral sum or scalar is evaluated.
In particular, this does not say the trace is nonzero.

For a correctly identified weighted Hilbert-Schmidt kernel the signed
Haar product average is even zero at **every** relatively compact
$H$-saturated box $E$ of positive mass, not merely in the limit. The
unnormalized average of the weighted-relative kernel is the matrix
coefficient of $T$ tested against $\mathbf 1_E/w$ in both slots of
$L^2(G,w\bar\mu)$. These vectors are invariant, so the coefficient
is zero. Both $w$ and $1/w$ are bounded on $E$, so the kernels are
locally Haar-integrable. For the Haar-relative kernel $w(y)k_w(x,y)$,
the input vector is instead $\mathbf 1_E$, also invariant. This uses the
$H$-saturation established in the accepted circle note, and applies to
any representative of the indicated actual kernel. It does **not**
identify the manuscript's named $\widetilde k^{\mathrm{spec}}$ in
(12.1.1.21), and does not refute (12.1.1.2) under its $D'$ hypothesis.

**Review evidence.** In the pinned PDF, the verdict uses rendered norm,
convolution, quotient-lift, trace-order, and homogeneous-character
passages at the locators above. Independent read-only reviewer
`angular-review` (Yah transcript `01a20263-38a8-75ff-a0af-5fe7f268d283`,
agent `OWrxjil`) inspected the decisive crops, checked both support
identities, and separately compared the singleton and strip labels
against the action convention and the actual Mellin selection rule.
The exact per-box matrix coefficient is the worker's extension of
those identities. No kernel-identification or trace-nonvanishing
review was requested. Selector Yah: `01a20261-9167-7d5e-a57c-ae78bba1c296`.

**Next bounded check:** Follow one nonzero formal tensor term through
(10.4.3.23)–(10.4.3.28), PDF p. 470, and the first kernel in
(10.4.3.30), p. 470 and its continuation on p. 471. Starting from the
defining dual pairing, check the two variable slots and the factor
of $w(y)$ in the singleton series, rather than substituting the claimed
integral formula.
This would determine whether the printed normalization even represents
the right operator on each finite term, before using box cancellation
on the named kernel. Convergence to the actual operator in the right
kernel topology, compatibility with the local-to-global diagonal, and
nonvanishing or evaluation of the trace on the selected support remain
separate premises. The cited spectral nuclearity and trace proof are
not independently established here.
