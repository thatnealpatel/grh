# The capped singleton jets annihilate every weight-four theta lift over Q(i)

**Result (ordinary mathematics, not Lean).** Let $F=\mathbb Q(i)$,
$G=C_F$, $G^1=\ker|\cdot|_F$, and $K=\prod_{v<\infty}\mathcal O_v^\times$.
Use the class model $(\mathbb C^\times\times K)/\mathbb Z[i]^\times$ and
$\eta([z,u])=(z/|z|)^4$. Let $M_a$ be the $W^{s,2}(G)$ closure of
$|\cdot|_F^a\Phi_F(\mathcal S_0(\mathbf A_F))$. For the singleton
$I=\{0\}$, $a=1/2$, $s=4$, and every zero $w_0=1/2+it$ of the
completed $L(w,\bar\eta)$ of order $d$, the bilinear jets

$$
D_t^m(h)=\int_G h(g)\bar\eta(g)|g|_F^{it}(\log|g|_F)^m\,d\bar\mu(g),
\qquad 0\le m<\min(d,2),
$$

annihilate $M_{1/2}$ and descend to the Sobolev quotient, in particular
its left-action $\bar\eta|_{G^1}$-isotype. This proves the annihilation
part of Theorem 10.2.1.1 in the selected case. It does not prove jet
totality or trace evaluation. In fact the Mellin quotient below is
entire, and the proof works for any fixed real $a$ and every integer
$m<d$ with $2m+1<s$ in the singleton norm, at a zero $a+it$ of order $d$.

## Source and character convention

The local PDF matches the [pinned edition](../sources/masullo/README.md).
Chapter 2, 6, 9, and 10 Markdown and the numbered layout located the
passages. The worker inspected rendered crops of the following:

- On p. 440, the pairing following (10.2.1.3) is bilinear and pairs
  opposite isotypes. Notation (10.2.1.4) takes a unitary extension
  $\chi$ of the compact character. With $\chi=\bar\eta$ the radial
  section $x\mapsto[e^{x/2},1]$ has $\chi=1$ on it. The jet in
  (10.2.1.5) uses $\chi$, positive $it$, and the $m$-th log power;
  (10.2.1.6) caps the multiplicity. At $s=4$ the integer orders
  permitted by the strict criterion (9.1.2.16), p. 402, are $0,1$.
- (10.2.1.9), p. 442, is the same bilinear Haar integral. Its input
  label $W^{s,2}(C_F)(\omega)$ is consistent with the choice
  $\omega=\chi|_{G^1}$ in the proof on p. 441. Indeed, under the
  left action the kernel $\chi$ itself has weight $\bar\omega$;
  the input has left-action weight $\omega$ and pointwise weight
  $\bar\omega$. This also follows from the projector
  $\phi\mapsto\int\omega(h)\phi(h\cdot)\,dh$ in (4.3.2.1), p. 178,
  and the theta version (2.2.5.2), p. 95. For $\chi=\bar\eta$ the
  input pointwise weight is $\eta$, so the characters cancel.
  Interpreting the input label as a *pointwise* weight instead
  gives the spurious $\bar\eta^2$ average, identically zero at every
  $t$. No change to the integrand or input label of (10.2.1.9) is
  needed. The actual ambient jet is nonzero on the intended block,
  for example on the compact smooth log profile
  $q(x)=x^m e^{-itx}u(x)$ with $u\ge0$ nonzero on $(1,2)$.
- (6.3.2.3), p. 304, asserts a range equal to
  $L(w,\chi)\mathscr O(\mathbb C)\cap A\mathcal S(\mathbb C)$ on a
  nontrivial character component. We prove the forward divisibility
  for this bilinear Mellin transform, not the range equality or its
  topology.
- Lemma 2.1.3.2 and (2.1.3.2), p. 68, give the tensor model. We use
  arbitrary compactly supported locally constant finite tests, not
  its part (3) wording “compact subgroup.” An additive subgroup
  indicator is even, whereas in general a translated compact open
  coset indicator is not. Remark 2.1.3.5, p. 70, describes generation
  by local Schwartz–Bruhat tensors for imaginary quadratic fields.

The [accepted Gaussian closure note](trace-theta-density-qi.md#source-interface)
supplies the independently rendered readings of the defining theta
sum (2.2.3.1), p. 81, the two zero modes in (2.2.4.23), p. 91, the
completed Euler product and Gamma factor (3.2.1.2)–(5), p. 123, the
bilinear Mellin integral (3.2.2.3), p. 124, and the above-one unfolding
(3.2.2.11), p. 127. The same note and its linked
[angular operator check](trace-spectral-angular-qi.md#test-and-source-interface)
identify the twist and closure in (10.1.1.1)–(3), p. 434, the quotient
in (10.2.1.1)–(2), p. 439, and the positive norm weight (9.1.2.3),
p. 399, namely $(1+x^2)^{s/2}$ for $x=\log|g|_F$. The left-action
isotype convention comes from (10.1.1.8), p. 436, and §9.3.1, p. 419,
as checked there. These are inherited readings of the same pin and
apply with $|[z,u]|_F=|z|^2$; they are not fresh visual checks.

## Project every lift before unfolding

Take $f\in\mathcal S_0(\mathbf A_F)$ arbitrary. First average over
$K$ on the finite variables using probability Haar. Then project the
complex variable to pointwise weight four:

$$
(\mathcal P f)(z,y)=\int_{S^1}\int_K h^{-4} f(hz,uy)\,du\,dh.
$$

This is again Schwartz–Bruhat. Indeed a finite adelic test is supported
in a compact open box and constant on cosets of a smaller product of
open additive subgroups. The larger box is a finite union of those
cosets, each a product of local cosets with standard factors outside
finitely many places. Together with the tensor model this gives a
finite sum of simple tensors for $f$. On every tensor the finite
average acts factor by factor, leaves the standard factors fixed, and
is still locally constant and compactly supported. The circle average
preserves all complex Schwartz seminorm bounds and gives a function
$b$ with $b(hz)=h^4b(z)$. In particular $b(0)=0$ and
$\int_{\mathbb C}b(z)\,dz=0$, by rotation invariance. Every projected
tensor therefore has both required zero modes, independently of
whether the original tensors separately had them.

The average commutes with the theta sum and the twist. To justify
termwise averaging, on the class representative $(z,u)$ the finite
support of a tensor bounds $\alpha\in F^\times$ in a fixed fractional
ideal, uniformly in the finite units being averaged. On each compact
interval of $\log|z|^2$ the corresponding archimedean sum is bounded
by a summable inverse lattice power, uniformly in the rotations. The
probability pushforward from $S^1\times K$ to $G^1$ is Haar, and
$h^{-4}$ comes from $\bar\eta$ on $G^1$. Thus
$\Phi_F(\mathcal P f)$ is exactly the $\bar\eta$ **left-action**
component of $\Phi_F(f)$, including after twisting. Moreover, Haar
invariance gives $D_t^m(h)=D_t^m(\mathcal P_Gh)$ for any ambient $h$,
where $\mathcal P_G$ is the corresponding bounded compact-isotype
projection on $G$.

## The normalized factors

Put $\chi=\bar\eta$, and let $Z_f(w)$ be the quotient Mellin integral
of $\Phi_F(\mathcal P f)$ against $\chi(g)|g|_F^w$. By (3.2.2.11),
p. 127, for $\Re w>1$ this unfolds to the corresponding upstairs
integral. Compute each projected tensor separately. The character
restricts trivially to every $\mathcal O_v^\times$, including at the
place over $2$. For a finite place fix a uniformizer $\pi_v$, put
$q_v=\#(\mathcal O_v/\pi_v\mathcal O_v)$, and write
$Y_v=\chi_v(\pi_v)q_v^{-w}$. Use the actual unit mass
$\nu_v=\mu_v(\mathcal O_v^\times)>0$ from the
[accepted finite normalization check](finite-gaussian-tamagawa.md),
not a unit-mass calibration at the place over $2$.

If $b_v$ is a finite factor after averaging, set $c_n=b_v(\pi_v^n)$.
Compact support implies $c_n=0$ for $n<A$ for some integer $A$;
local constancy at zero gives $c_n=b_v(0)$ for all $n\ge B$, for some
integer $B\ge A$. Every multiplicative shell has mass $\nu_v$. For
$\Re w>0$, $|Y_v|<1$, so the local integral is absolutely convergent
and its quotient by the Euler factor $(1-Y_v)^{-1}$ is

$$
\nu_v\left((1-Y_v)\sum_{A\le n<B}c_nY_v^n + b_v(0)Y_v^B\right).
$$

This formula includes negative valuations and nonzero constant tails.
It is entire in $w$ because $Y_v$ is an exponential with no zeros.
As a control, $1_{\pi_v^{-1}+\mathcal O_v}$ averages to $1/(q_v-1)$
on the shell $n=-1$ and vanishes elsewhere: The condition on the
unit after multiplying by $\pi_v$ is being $1$ modulo $\pi_v$.
The normalized factor is $\nu_v(1-Y_v)Y_v^{-1}/(q_v-1)$.
For $b_v=1_{\mathcal O_v}$ the quotient is $\nu_v$. The product of
these mass constants has only finitely many terms different from $1$;
the arbitrary test corrections also occur at only finitely many places.
The finite factors therefore leave an entire product after extracting
the unramified Euler factors, initially on the absolutely convergent
half-plane $\Re w>1$.

At the complex place the pointwise weight four cancels the restriction
of $\chi$. With $y=|z|^2$, the local integral is
$\nu_\infty\int_0^\infty b(\sqrt y)y^{w-1}dy$ for a fixed positive
Haar constant $\nu_\infty$. At infinity the radial factor is Schwartz
in $\sqrt y$. Near zero, Taylor expansion of a smooth function in
$z,\bar z$ followed by the angular projection keeps exactly the
monomials $z^p\bar z^q$ with $p-q=4$. Thus for every $N\ge0$,

$$
b(\sqrt y)=\sum_{k=0}^N a_k y^{2+k}+O(y^{3+N}).
$$

For this remainder one may expand through total degree $5+2N$; the
next possible surviving degree is $6+2N$. In particular the integral
is holomorphic for $\Re w>-2$. Subtracting the displayed terms on
$(0,1)$ gives a meromorphic continuation with only simple possible
poles at $w=-2-k$, contributed by $a_k/(w+2+k)$. Dividing by the
printed complex factor $(2\pi)^{-(w+2)}\Gamma(w+2)$ cancels all these
poles by the simple zeros of the reciprocal Gamma function. So the
archimedean quotient is entire as well. Absolute factorization on
$\Re w>1$ and finite summation now give
$Z_f(w)=L(w,\bar\eta)E_f(w)$ there with $E_f$ entire. The factor
$E_f$ includes Haar constants; no equality of raw local pairings and
unit-mass Euler factors is used.

## Continuation and descent

For a direct check on the quotient, each unit-invariant finite factor
is the telescoping sum $\sum_{n=A}^B(c_n-c_{n-1})1_{\pi_v^n\mathcal O_v}$,
with $c_{A-1}=0$. Expanding the finite product expresses the radial
theta profile as a finite linear combination of
$\sum_{0\ne\alpha\in\mathfrak a} b(e^{x/2}\alpha)$ for nonzero
fractional ideals $\mathfrak a$ of $\mathbb Z[i]$. Each ideal is a
full lattice in $\mathbb C$. The direct Schwartz bound at $x\to+\infty$
and Euclidean Poisson on the lattice at $x\to-\infty$ give
$O_N(e^{-N|x|})$ for every $N$: On the negative tail the transform
is evaluated on $e^{-x/2}\mathfrak a^*$ with a constant times $e^{-x}$,
and both zero terms vanish by $b(0)=\widehat b_{\mathrm{Euc}}(0)=0$.
Use inverse lattice powers of degree greater than $2N+2$ on that tail.
These bounds justify differentiation under the quotient integral with
all log moments, on every compact set of $w$. They do not need the
printed adelic Fourier inversion convention. The Mellin integral is
entire, as is $L(w,\bar\eta)$ by the accepted single-Gaussian identity.
The identity theorem extends $Z_f=L E_f$ to all $w$.

For $x=\log|g|_F$ the quotient Haar measure splits as $d\mu_1\,dx$
with $C=\mu_1(G^1)>0$. A twisted projected theta function has the form
$\eta(g)q(x)$ with $q(x)=e^{ax}\Phi_F(\mathcal P f)([e^{x/2},1])$.
On it $D_t^m=C\int q(x)e^{itx}x^m dx=Z_f^{(m)}(a+it)$;
relative to the positive log Fourier transform it is $C i^{-m}$ times
the $m$-th frequency derivative. For $m<d$ this is zero by divisibility.
The same evaluation on an unprojected generating lift equals the
projected one by the compact-character cancellation. Finally,
Cauchy–Schwarz bounds the ambient functional by the $W^{s,2}(G)$ norm
times

$$
\left(C\int_{\mathbb R}|x|^{2m}(1+x^2)^{-s/2}\,dx\right)^{1/2},
$$

finite exactly for $2m+1<s$. In particular, on the ambient isotype,
$|x|^m q(x)$ is integrable for each such $m$, so dominated
differentiation identifies the displayed pairings with the actual
positive log Fourier value and derivatives there as well. Each
permitted jet vanishes on the closed twisted theta space and defines
a continuous functional on the quotient. The accepted Lean
[log-line kernel criterion](../../Proofs/Props/BoundaryLogJet.lean)
already checks this strict threshold for the divided kernel at width
zero; it is not a Lean proof of the adelic factorization or of descent
for this Gaussian block.

## Review and remaining work

**Independent review:** `gaussian-jet-review` (agent `qhEjWlk`,
transcript in Yah session `01a2028d-6b7a-77f1-ae2e-e2642ed5da64`)
checked the rendered pp. 68, 70, 95, 178, 183, 304, 402, and 440–442
interfaces and the applicability of the inherited sources. The
review independently verified averaging and the two zero modes,
absolute shell sums with their true unit masses, the off-center
coset control, Gamma normalization and cancellation, Euclidean
Poisson continuation, and continuous jet descent. Its opening
assessment called the input label of (10.2.1.9) wrong, but its own
rendered readings and derived rule say the input left-action label
must be $\chi|_{G^1}$. The worker independently checked the
projector and input labels on pp. 95, 178, and 442. Applying that
rule to the p. 441 choice $\omega=\chi|_{G^1}$ gives the conclusion
above: The input label is right under the left action, not under a
pointwise reading. No consequential manuscript reading for the
scoped verdict remains provisional. This does not audit the rest
of the surrounding duality argument.

Selector Yah `01a2028c-0ad3-75e4-b55d-bdc9b6106fb6`; worker Yah
`01a2028d-6b7a-77f1-ae2e-e2642ed5da64`.

**Resolved successor:** The [singleton totality check](trace-theta-totality-qi.md)
uses the single-Gaussian inclusion and this annihilation result to
identify the full closed theta block with the common capped jet kernel.
It checks the cap by local division and shrinking bumps, and obtains
exhaustion by strongly convergent Sobolev cutoffs.

**Separate open premises:** Scalar trace evaluation and nonvanishing
for specific bumps, printed kernel convergence and identification,
and the local-to-global diagonal comparison. No positive-width
result is claimed.

**Deferred comparison:** A Lean proof of the corrected integer-ball
residue in (3.3.2.23), p. 141, would certify one coefficient; arbitrary
local test factors take precedence because they establish descent for
all admissible lifts in the [trace-class singleton case](trace-spectral-singleton-qi.md).
