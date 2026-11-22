# Closedness of the glued image at the stage containing the different

**Result (ordinary mathematics, not Lean):** Let $F=\mathbb Q(\sqrt{-5})$,
let $\chi$ be its nontrivial ideal-class character, and put
$S''=S_\infty\cup\{\mathfrak p_2,\mathfrak p_5\}$. With the two-ended
sampling correction to Definition D.3.1.3, pp. 800–801, the **actual**
$L\circ\overline\pi_{S''}$ is a closed linear topological embedding
of the full local isotypic Schwartz quotient into
$A\mathcal S(\mathbb C)$. This repairs the closed-range inference
after (6.3.2.13), p. 306, not the printed residue argument. No
surjectivity or closedness at other stages is asserted.

## Interfaces and the two scalar inverses

In the [pinned edition](../sources/masullo/README.md), the
[accepted rendered interfaces](isotypic-fourier-gluing-q-sqrt-minus-five.md#source-interface)
for (6.3.2.10)–(11), p. 305, apply at $S''$: Inverting $\mathfrak p_2$
kills the class group, the character is unramified, and the idèle
with components $\sqrt 2$ and $\varpi_2$ has norm one and character
value $-1$. There is no polar multiplier and no restriction to a
moment-zero subspace. The norm section $t\mapsto(\sqrt t,1,1)$ is
character-trivial and uses the same $s$ as the global transforms.
The reflected character is $\bar\chi=\chi$, with norm parameter
$1-s$ (no conjugation of $s$). Every omitted place has trivial
different, so its inserted ball is Fourier-fixed. The trace-dual
factor is therefore one at this stage.

Write $H_+=\{\Re s>0\}$, $H_-=\{\Re s<1\}$,
$X_\pm=A\mathcal S(H_\pm)$, and $P=X_+\times X_-$. Give these spaces
the corrected topology of the
[local closed-range check](isotypic-local-closed-range-q-sqrt-minus-five.md#printed-definition-and-corrected-product).
For each bounded closed real interval $I$ in the abscissa domain and
each integer $n\ge0$, use the equivalent seminorm
$$
p_{I,n}(f)=\sup_{\sigma\in I,\ t\in\mathbb R}(1+|t|)^n|f(\sigma+it)|.
$$
Then the operator in (6.3.2.11) is
$T=T_{S'',\chi}=M_D\times M_{D(1-\cdot)}$, with $M$ denoting
multiplication and
$$
D(s)=(1+2^{-s})(1-5^{-s})L(s,\chi_{-4})L(s,\chi_5).
$$

The [forward division repair](isotypic-forward-division-q-sqrt-minus-five.md#closed-range-evidence-and-next-check)
gives a continuous injection $M_D:X_+\to X_+$ whose image is the
closed common kernel of the jets at the zeros of $D$ in $H_+$,
through order one less than the respective multiplicity. Its inverse
is continuous on that image. The result needs no continuation of
an arbitrary numerator across the edge of $H_+$.

The holomorphic reflection $Jf(s)=f(1-s)$ from $X_+$ to $X_-$ is
an isomorphism: For every interior $[a,b]$ of $H_-$,
$$
p_{[a,b],n}(Jf)=p_{[1-b,1-a],n}(f),
$$
and the reverse reflection gives the inverse. Hence
$M_{D(1-\cdot)}=J M_D J^{-1}$. In particular, whenever the quotient
$h(s)/D(1-s)$ is holomorphic in $H_-$, its reflection satisfies the
forward estimate, giving membership in $X_-$ and continuous
left division, with no estimate across $\Re s=1$. The fixed product
$T$ is thus a closed embedding on $P$: Its image is the product of
the two closed ranges, and its inverse there is the product of the
continuous divisions. This uses the inverse estimates, not an
inference about the range from continuity or graph closedness.

## The overlap and the corrected whole-plane topology

On each domain used here, including the whole plane, the corrected
sampled topology and the interior strip topology agree by the same
bracketing argument. For the whole plane, take for example samples
$-m,m$ interleaved for $m\ge1$. For any bounded interval $I$, choose
two sample lines strictly outside its endpoints. Apply vertical
Cauchy to $s^N f(s)$ between those lines: The horizontal edges vanish
by the defining strip decay, and the Cauchy kernels on the two lines
have uniformly bounded dual $L^{p/(p-1)}$ norms since both gaps from
$I$ are positive. This bounds the weighted sup on $I$ in terms of the
two sampled $L^p$ norms, using $N=0,n$ to pass to $(1+|t|)^n$. In the
other direction, the strip seminorm of order $N+1$ on a sample line
bounds its $N$-weighted $L^p$ norm, since $|s|^N$ is at most a
line-dependent constant times $(1+|t|)^N$ and $p>1$. Derivative
seminorms, if included, give the same topology by Cauchy on a slightly
larger interior strip. This uses the [accepted membership and sampling reading](isotypic-good-heights-q-sqrt-minus-five.md#rendered-source-and-scope)
of Lemma D.3.1.2 and Definition D.3.1.3, pp. 799–801, not the literal
positive-only prescription on the whole plane.

Let $K=\ker R_{S'',\chi}$ for the difference of restrictions in
(6.3.2.13), p. 306. Each interior strip of the overlap is interior
to both half-planes, so the difference is continuous and $K$ is
closed in $P$. Restriction gives a continuous injection
$$
A:A\mathcal S(\mathbb C)\longrightarrow P,\qquad
f\longmapsto (f|_{H_+},f|_{H_-}).
$$
A pair $(f_+,f_-)\in K$ agrees where the two domains meet. It gives
a unique entire function $f$ by holomorphic gluing, since the
half-planes cover $\mathbb C$. For **any** bounded closed interval
$I$, split $I$ at $1/2$, setting $I_-=I\cap(-\infty,1/2]$ and
$I_+=I\cap[1/2,\infty)$. Each nonempty piece is interior to its
respective half-plane. Exactly
$$
p_{I,n}(f)=\max\bigl(p_{I_-,n}(f_-),p_{I_+,n}(f_+)\bigr),
$$
omitting terms for empty pieces. This proves rapid strip decay
for the glued function, and continuity of gluing in the subspace
topology on $K$. Thus $A$ is a homeomorphism onto $K$; its closed
range does not follow just from Hausdorffness of the factors. The
same argument works with any split abscissa strictly in the overlap.

## Closedness of the actual image

Put $U=U_{S'',\chi}$ on the full local quotient. The
[accepted local result](isotypic-local-closed-range-q-sqrt-minus-five.md#scope-and-next-check)
gives $\operatorname{im}U$ closed in this **same** $P$, with $U$ a
linear topological embedding. A closed embedding takes this closed
subspace to a closed subset of its own image and hence of $P$.
Therefore $T(\operatorname{im}U)$ is closed in $P$. This step uses
local closed range and the two inverses; continuity of $R$ alone
would only show that $K$ is closed.

By the [accepted exact normalization](isotypic-fourier-gluing-q-sqrt-minus-five.md#exact-global-normalization-at-the-stage-containing-the-different),
$T(\operatorname{im}U)\subseteq K$, and both legs are restrictions
of the actual $L\circ\overline\pi_{S''}$, with scalar one. In that
argument counting Weil contributes no scalar, the two retained unit
masses stay in the local integral, and all omitted unit masses are
one. Thus $A^{-1}T(\operatorname{im}U)$ is the actual image, closed
in the corrected whole-plane topology, and the composite
$A^{-1}TU$ is a linear topological embedding. The proof neither
requires the two local zero modes to vanish nor repairs the missing
trace-dual factor at the smaller stage.

## Evidence and next check

In the digest-matched PDF, p. 306, the worker inspected rendered
crops of the sentence following the sequential range argument after
(6.3.2.13). Independent reviewer `SPWAkWw` read “the range of,”
$T_{S,\chi}\circ U_{S,\chi}$, and “closed in the kernel of
$R_{S,\chi}$” from separate tight crops. This confirms the subject
and relative closedness assertion; it does not check the printed
proof. Reviewer `vphxvmq` independently corroborated the full
sentence by layout extraction, but their crops did not permit a
reliable pixel reading. The p. 305 map, the rest of the p. 306 map
identification, and the pp. 799–801 membership and sampling
requirements are inherited from the accepted notes cited above,
not new rendered readings.

Independent mathematical reviewer `SuwMswf` checked that the
inherited stage, character, full quotient, and exact normalization
apply, that the local result supplies both closedness in $P$ and
the embedding $U$ into $P$, and that the reflection, product inverse,
sample bracketing, and split-strip gluing prove the claimed endpoint.
This is a review of the application and new proof, not of the
original residue or general local structure theorems. All three
review transcripts are in Yah `01a20482-7392-7c96-a20b-7a9c01484f00`,
reviewed base `7cef9eea71d25e41c25980abe0998a45d99b5f51`.
The selector Yah is `01a20480-d488-7ae9-856a-b9a4905b2736`.

**Next bounded check:** For the proposed range in (6.3.2.3), p. 304,
compare the full zero orders of the completed $L$-factor with those
of $D(s)$ on $H_+$ and $D(1-s)$ on $H_-$, using the
[accepted completed product](isotypic-inverse-range-q-sqrt-minus-five.md#verified-completed-product-and-divisibility)
and the two exact Gaussian-and-balls legs in the
[normalization check](isotypic-fourier-gluing-q-sqrt-minus-five.md#exact-global-normalization-at-the-stage-containing-the-different).
This would identify the two scalar jet conditions for a target in
terms of the completed divisor, with $0$ and $1$ each tested in the
half-plane that contains it. Separate from that comparison: To
prove a direct lift at $S''$, the divided pair must satisfy the
[local functional-equation relation](isotypic-local-closed-range-q-sqrt-minus-five.md#a-closedness-check-avoiding-the-finite-polar-free-reduction),
not just two independent scalar membership conditions. The general
stage question and a Lean realization remain outside this result.
