# Chapter 13 moment conditions on the full rational test space

## Printed statement and domain

Masullo, Theorem 13.3.1.1, PDF p. 522, starts with
$\varphi\in\mathcal D(C_F)$, chooses a continuous homomorphic section
$\tau$ to the norm, and requires (13.3.1.2) for every
$0\le k\le [F:\mathbb Q]-1$ and **all** $\chi\in\widehat{C_F}$. Its
last paragraph calls the common kernel $A\subset\mathcal D(C_F)$
$[F:\mathbb Q]$-codimensional. Neither the initial test space nor the
last paragraph restricts to one compact isotype. Footnote 1 says
“Correct statement”; it does not give a replacement. The theorem's
quantifier, moment, ambient space, and codimension were checked in
pixel crops of the [pinned edition](../sources/masullo/README.md)
(rendered with `pdftoppm`, with the crop pixels read as Braille cells).
The decisive supporting passages below were checked the same way.
Independent Yah review `oDkPonw` separately examined the rendered
p. 522 and the definitions licensing the two tests, and confirmed
the rank computation. The local-Haar interpretation of (13.3.1.4)
is separate and not established here.

The following definitions put the witnesses in that domain:

- Definition A.1.4.1 and the following norm discussion, p. 542, give
  the class quotient, descended norm, and norm-one subgroup.
- (A.2.2.2)–(4) and Lemma A.2.2.1, p. 546, give the rational
  splitting $C_{\mathbb Q}\simeq\mathbb R_{>0}\times K$, with
  $K=C_{\mathbb Q}^1\simeq\widehat{\mathbb Z}^{\times}$, and section
  $\tau(t)=[(t,1,\ldots)]$. The norm is the positive real coordinate.
  This uses the positive real representative and does **not** quotient
  the finite units by $\{\pm1\}$ again. The group operations and
  section are also supplied by the accepted Lean declarations below.
- Theorem D.1.1.1, p. 746, defines $\widehat G$ using continuous
  $U(1)$-valued characters. Each character of $K$ used here extends
  trivially along $\tau$ and is therefore an allowed $\chi$.
- Lemma D.3.6.1, p. 819, writes $\mathcal D(G)=C_c^\infty(G)$ for the
  indicated modulated groups. The rational product is second countable,
  and the norm projection is continuous, nontrivial, and proper by
  compactness of $K$ (Definition D.2.1.1, p. 793).
  For the smoothness hypothesis, Definitions D.1.5.1, p. 760, and
  D.1.5.3(1), p. 762, use invariance by a good subgroup and smoothness
  on the structural Lie quotients. Let $H$ be the kernel in $K$ of
  reduction on the $3$-adic unit coordinate modulo $3$. The quotient
  $C_{\mathbb Q}/H$ is $\mathbb R_{>0}\times(\mathbb Z/3\mathbb Z)^\times$
  (the ideal-topology completion in §A.1.2, p. 540, gives the finite
  reduction by the Chinese remainder theorem). The annihilator of $H$
  is open (compactness of $H$) and is the compactly generated dual of
  this quotient by Lemma D.1.4.6(2), p. 758, so $H$ is good. Both
  tests below descend to smooth functions on this quotient, hence on
  $\Gamma/H$ for every structural pair with this $H$, by restriction
  to the open subgroup. Their supports are contained in a compact norm
  band times $K$.
- Definition A.3.2.1 and (A.3.2.1), pp. 559–560, use $dt/t$ and
  Haar on $C_F^1$. For $\mathbb Q$, the compact Haar mass is
  $2/2=1$ (empty regulator determinant, class number one, absolute
  discriminant one, and two roots of unity). Thus $x=\log t$ gives
  $dx$ and probability Haar $du$ in the two coordinates. In fact
  any positive Haar normalization gives the same rank.

## Two independent moments, even away from norm one

Put $F=\mathbb Q$, so only $k=0$ occurs. The factors
$\chi(\tau(t))t^s$ cancel at the printed evaluation point
$s=-ix_0(\chi)$. Thus for $\eta=\chi|_K$ the moment is

$$M_\eta(\varphi)=\int_{\mathbb R}\int_K
     \varphi(\tau(e^x)u)\eta(u)\,du\,dx.$$

For the two selected characters (trivial extensions of compact
characters), $x_0=0$. Write $\epsilon(u)=1$ if $u_3\equiv1\pmod 3$,
and $-1$ if $u_3\equiv -1\pmod 3$. The map onto
$(\mathbb Z/3\mathbb Z)^\times$ is surjective. Its two cosets have equal
Haar probability by translation, so $\int_K\epsilon\,du=0$ and
$\int_K\epsilon^2\,du=1$. Let $b\in C_c^\infty((0,\log 2))$ have
$\int b\,dx=1$, and put
$\varphi_1(\tau(e^x)u)=b(x)$ and
$\varphi_\epsilon(\tau(e^x)u)=b(x)\epsilon(u)$. These are tests in
$\mathcal D(C_{\mathbb Q})$ by the preceding checks, and vanish on a
neighborhood of $K$. Compact support and the character bound give
absolute convergence. With rows and columns ordered as $1,\epsilon$,

$$\big(M_\eta(\varphi_\xi)\big)_{\eta,\xi}
  =\begin{pmatrix}1&0\\0&1\end{pmatrix}.$$

The formula pairs with $\chi$, not $\overline\chi$; both characters
here are self-inverse. In particular $\varphi_\epsilon$ has **zero
total mass** and fails the quadratic condition. The image of the
joint moment map already has dimension two at this level, so no
single scalar linear condition, or correction in one fixed scalar
bump direction, enforces (13.3.1.2) on the full space.

More generally, on tests factoring through the compact quotient
$(\mathbb Z/3^n\mathbb Z)^\times$, the map has rank
$2\cdot 3^{n-1}$: All characters nontrivial on the kernel have zero
average by Haar translation, and the quotient characters give the
identity matrix when the test factors use the inverse characters.
These tests satisfy the same smoothness check. The full common kernel
therefore has **infinite algebraic codimension**, already among tests
supported in the same short positive-log band. This argument does not
require a topological description of the full quotient.

## Scope and handoff

The [prior divisor handoff](trace-divisor-uniqueness.md#the-common-test-class-and-the-missing-comparison)
correctly finds one condition on **radial** tests: All other compact
characters integrate to zero automatically. More generally, for a
test of the form $f(x)\overline{\eta(u)}$ in a fixed compact isotype,
only the matching compact restriction imposes a condition, namely
$\int f=0$ over $\mathbb Q$. On each finite quotient stage one can
subtract $b(x)\int_{\mathbb R}\varphi(\tau(e^y)u)\,dy$ from
$\varphi(\tau(e^x)u)$, still on that stage. This is a
compact-variable-valued correction, or a scalar correction in each
isotype, not the globally codimension-one statement on p. 522 or a
proof of the trace on those tests. The computation only refutes the
codimension assertion and the proposed single scalar correction on the
full space. It does not refute (13.3.1.3)–(5) on the actual common
kernel, or supply any capped trace evaluation.

Accepted Lean inputs are
[`rationalIdeleClassLogSplit`](../../Proofs/Theorems/RationalIdeleLogSection.lean),
[`rationalFiniteUnitClassEquiv`](../../Proofs/Theorems/RationalIdeleFiniteUnitFactor.lean),
and [`measurePreserving_rationalFiniteUnitClassEquiv` and
`rationalIdeleClassHaar_eq_logVolume_prod_finiteUnitHaar`](../../Proofs/Theorems/RationalIdeleFiniteUnitHaar.lean).
They give the actual class-group coordinates and quotient Haar, not
the mod-$3$ moment matrix. This audit is ordinary mathematics; no
Lean code changed. The accepted [conditional zeta endpoint](../../Proofs/Props/ZetaTestSumComparison.lean),
`zetaZero_on_criticalLine_and_simple_of_test_sum_eq`, is still a
trivial-isotype result conditional on full and capped sums agreeing
on all smooth compactly supported positive-log profiles of mass zero.
No ramified Fourier recovery or Hecke contour statement is needed
for this rank computation.

**Next bounded source check (mapped):** The p. 522 display of
(13.3.1.4) has no separate factor $1/2$. Follow the prime through
(B.4.4.1)–(2), pp. 619–620, and the real Fourier kernel (B.4.3.13),
p. 619, then compare (B.4.4.4), p. 620, and (B.4.4.16), p. 623.
Determine whether the prime on the short positive-log radial mass-zero
tests gives raw real Haar or half Haar. Equation (B.4.4.5), p. 620,
is only stated for finite places. The short tests vanish near the real
singularity and restrict identically to zero at finite places by the
norm band. This isolates the normalization premise
of the [prior pole test](trace-divisor-uniqueness.md#a-pole-test-for-the-raw-haar-reading)
without solving the trace comparison. The $s=2$ global singleton
geometric evaluation, full-versus-capped test agreement, and the
nontrivial-isotype trace and explicit formula interfaces remain open.
The [Gaussian global stage evaluation](weil-admissible-set.md#reusable-scope-and-remaining-premises)
is a separate mapped task, not used here.
