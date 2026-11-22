# A positive-width boundary vector fails the printed endpoint cap

**Result:** In the [pinned Masullo edition](../sources/masullo/README.md),
Theorem 10.2.2.1, p. 446, lists a rational trivial-character boundary
vector at Sobolev degree $s=1$ that does not belong to $W_I^{-1}(C_{\mathbb Q})$
with the reciprocal norm on p. 417. The same vector does belong at $s=2$.
This is a membership check before any quotient-basis or trace argument.
The prior [strict log-model criterion][model] proved the threshold in
Lean but checked the cap only in extraction and did not identify the
manuscript vector with the model. This check uses the rendered cap,
bracket convention, and defining norm.

## Printed selection

Notation 10.2.2.1, p. 445, with (10.2.1.4), p. 440, permits the
unitary base point $\chi=1$ over the trivial norm-one character. In
Definition 3.2.1.2 and (3.2.1.2)–(3.2.1.4), p. 123, the Hecke
function is completed. For $F=\mathbb Q$ and $\chi=1$ the finite product
(3.2.1.7), p. 124, has all factors $(1-p^{-z})^{-1}$, and the real
factor is $\pi^{-z/2}\Gamma(z/2)$. By continuation the function is
$\pi^{-z/2}\Gamma(z/2)\zeta(z)$; the prefactor is finite and nonzero
in the open strip $0<\Re z<1$, so it preserves its zeta zeros and their
multiplicities.

Let $\rho=\beta+it$ be any nontrivial zeta zero. Choose
$0<2\alpha<\beta<1$ and $a=\beta-\alpha$. Then
$I=[-\alpha,\alpha]$ has positive width and $a+I=[\beta-2\alpha,\beta]$
lies in $(0,1)$. With $b=\alpha$, the zero parameter in
Theorem 10.2.2.1(1) is $|\cdot|^{a+it+b}=|\cdot|^\rho$, with
multiplicity $N(\rho)\ge 1$. The displayed cap (10.2.2.5) is
$\min\{N(\rho),[(s-1)/2+1]\}$, with the $+1$ inside the brackets.
The same counting function (10.3.2.4), p. 454, explicitly defines
$[x]$ as the largest integer $N\ge 0$ with $N\le x$. At $s=1$ the
cap is one, and the displayed $0\le m\le N_{I,s}-1$ admits $m=0$.
The vector in (10.2.2.4) is therefore $\eta(g)=|g|^{\alpha+it}$.
The Sobolev degree $s$ is not the complex argument of the Hecke
function here. No multiple zero, zero-width strip, or off-line zero is
required.

## Defining norm and control

Proposition 9.2.2.11, p. 417, assumes a second-countable
$\mathbb R_{>0}$-modulated group, an arbitrary Haar measure, a
nondegenerate compact interval, and real $s\ge 0$. The rational quotient
and descended norm are defined in (A.1.4.1)–(A.1.4.2), p. 542. In
(A.2.2.3)–(A.2.2.4), p. 546, the positive real norm section splits off
$C_{\mathbb Q}^1\simeq\prod_p\mathbb Z_p^\times$, a compact
second-countable group. This also follows by normalizing the finite
valuations to zero by a rational multiple, then choosing the real
component positive. In particular the norm is proper and surjective,
as required by Definition D.2.1.1, p. 793. With $x=\log|g|$, Haar pushes
forward to $c\,dx$ for $0<c<\infty$ by the product formula in §9.1.2,
p. 400, and Remarks D.2.1.2–D.2.1.4, pp. 793–794. Its absolute
normalization is immaterial. The accepted [rational Haar module][haar]
constructs one such measure, with $c=1$.

The completion in (9.2.2.40) embeds isometrically into
$L^2(w_{I,s}^{-1}d\mu)$. The cited radial duality (9.2.1.29)–(9.2.1.31),
pp. 409–410, has the same reciprocal weight, specialized to $dt/t$.
For the vector named by (10.2.2.4), (9.2.2.40)–(9.2.2.41) give the
squared norm integral

$$
c\int_{\mathbb R}\frac{e^{2\alpha x}}{e^{2\alpha |x|}(1+x^2)^{s/2}}\,dx.
$$

At $s=1$ the positive tail is exactly $c(1+x^2)^{-1/2}\,dx$,
which dominates $c/(\sqrt 2\,x)\,dx$ for $x\ge 1$. Thus the vector
is not even in the ambient weighted $L^2$. At $s=2$ the density is
bounded by $c/(1+x^2)$ on the whole line, and the same vector is still
selected by the printed cap. It belongs to the completion: Multiply
it by smooth log cutoffs equal to one on $[-R,R]$, bounded by one, and
with compact support. These are pullbacks of compactly supported smooth
log functions on the quotient by $C_{\mathbb Q}^1$, even after
multiplication by any $|\cdot|^u$. The group $C_{\mathbb Q}$ is compactly
generated, and the annihilator of $C_{\mathbb Q}^1$ is open and
isomorphic to $\mathbb R$, so these groups form a structural pair in
Definition D.1.5.1, p. 760. Hence the cutoffs lie in every $\mathcal S_J$ of
(9.2.2.40) by Definition D.1.5.3, p. 762, and Definition D.3.3.1,
p. 804. Dominated convergence gives norm convergence.

For the same rational radial calculation, replacing $m=0$ by any
$m\in\mathbb N$ multiplies the squared integrand by $|x|^{2m}$.
At either boundary the matching tail has power $2m-s$, and the compact
middle is harmless. The other tail gains exponential decay. Thus the
reciprocal norm, and by the same cutoffs radial membership, requires
and suffices that $2m+1<s$. The ambient calculation also works for a
unitary isotype and any split group with compact norm-one factor:
The character has modulus one. At width zero the log model still has
the same threshold, but Proposition 9.2.2.11 does not cover that case.
The [accepted Lean theorem][jet] `Masullo.memLp_boundaryLogJet_iff`
proves the ambient log-model equivalence for $s\ge 0$ and
$|\Re z|=\alpha$, all $m\in\mathbb N$, including width zero. The
identification with the printed vector above is ordinary mathematics,
not a new Lean declaration.

## Scope and successor

Theorem 9.3.2.6, cited in the proof on p. 446, concerns approximate
units on the primal space. Its kernel intersection (9.3.2.10), p. 426,
does not supply boundedness of a boundary evaluation. Its own cited
Lemma 9.3.2.5, pp. 425–426, assumes interior zeros. The [earlier
nesting and totality check][total] is a separate issue, also confirmed
on the rendered kernel intersection in this review. For boundary
membership, a repair is to retain precisely the orders $m<N(\rho)$
with $2m+1<s$, or use cap $\min(N(\rho),\lceil(s-1)/2\rceil)$ for
$s\ge 0$. This removes the equality case; it is not a proof of basis
or totality after that correction. The $s=1$ witness is outside the
range of the later spectral nuclearity and trace theorem (Theorem
10.3.2.1, pp. 453–454, assumes $s>1$). It also does not test a strip
without boundary zeros or decide RH or GRH.

**Next bounded check:** Inspect the rendered Corollary 9.2.2.5(2),
p. 414, (9.2.2.24), and test $k=0$, $s=1$ on smooth compact log profiles
using the positive Hardy–Sobolev norm and Mellin convention it cites.
This would determine whether the boundary membership defect already
appears as an upstream continuity assertion. The [existing smooth
obstruction][smooth] provides a log-model test, not the source check.
Formal transport to rational quotient Haar, quotient annihilation,
totality, and trace assembly are separate obligations.

## Review evidence

Independent read-only review on `13dfbec9f1a7387f3d6f9875da8313a58a5e23a0`:
Yah session `01a20223-cda2-7c14-a21b-9638356920cf`, agent `DfoaQji`
(`boundary-review`; review selector `01a20224-5160-7da7-8406-3ceff6a36ba9`).
Both readers checked the pinned digest and used rendered raster crops
for the cap, bracket, and reciprocal norm, not text extraction or OCR.
The reviewer separately found:

- **Printed selection:** The rendered p. 446 cap includes the $+1$
  inside the brackets, and the rendered p. 454 weak inequality gives
  $[1]=1$. The reviewer checked the trivial lift and completed Hecke
  convention against the p. 445 and pp. 122–124 definitions, then
  verified the right-edge placement and positive multiplicity. The
  existence of a nontrivial zeta zero is classical input, not a new
  Lean result.
- **Defining norm:** The rendered p. 417 equations show the inverse
  weight, the outer square root, the maximum of the endpoint powers,
  and the $s/2$ power. Independently of the cap, the reviewer computed
  the log-Haar density from the rational splitting. They checked
  divergence at $s=1$, and the smooth-cutoff membership argument at
  $s=2$ against the appendix test-function definitions.
- **Cited dependency:** The rendered p. 426 kernel intersection
  gives decreasing, not increasing, ranges. The review found no
  boundary boundedness statement in the cited result and checked the
  interior hypothesis of its basis input. This is not used to deduce
  nonmembership, which follows directly from the norm.

The review and the independent calculation agree on both routes.
The accepted Lean log criterion has matching ambient hypotheses
and density after the ordinary-mathematics identification; neither
reader used it as a check of the printed cap or as a formalization of
the idelic completion. No Lean sources were changed.

[haar]: ../../Proofs/Theorems/RationalIdeleClassHaar.lean
[jet]: ../../Proofs/Props/BoundaryLogJet.lean
[model]: theta-inversion-q.md#checked-strict-integrability-threshold-for-boundary-jets
[smooth]: theta-inversion-q.md#checked-obstruction-on-smooth-compactly-supported-profiles
[total]: trace-spectral-strip-q.md#source-interface-a-missing-totality-step
