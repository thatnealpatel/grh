# The singleton tensor pairs against Haar, not reciprocal-weight Haar

**Ordinary mathematics, not Lean.** In Masullo's singleton kernel
construction (10.4.3.22)–(10.4.3.30), PDF pp. 469–471, the
coordinate order and the integration density are separate issues.
The flip to output-first order is valid, but the resulting tensor
function is already the Haar-relative kernel. The extra $w(y)^{-1}$
in (10.4.3.25) inserts a multiplier on the input. The first conversion
in (10.4.3.30) is correct *given the correct Haar kernel*, not a repair
of (10.4.3.25)–(26).

## The defining action

Use $G=C_{\mathbb Q(i)}$, $I=\{0\}$, $s=4$, $a=1/2$, $r=\log|\cdot|_F$,
$\mu=\overline\mu$, and $w=(1+r^2)^2$. In (9.1.2.3), PDF p. 399,
$W^{4,2}(G)=L^2(w\mu)$, and $W^{-4,2}(G)=L^2(w^{-1}\mu)$.
Take the [accepted weight-four test and isotype](trace-spectral-angular-qi.md):
$\varphi=b(r)\eta$, $\eta([z,u])=(z/|z|)^4$, with
$0\ne b\in C_c^\infty((0,\log 2))$. Its descent and compact support,
and the input and output isotype $\bar\eta|_{G^1}$ for the actual
operator, are inherited from that note. The compact norm-one group
and the radial section give compact log annuli and Haar measure
proportional to $dr$ on the radial factor.

For a formal index $(\chi,t,m)$ of the summand in (10.4.3.22), let
$D(f)=\int f(y)\eta_{\chi,t,m}(y)\,d\mu(y)$,
$\eta_{\chi,t,m}=\chi e^{itr}r^m$, as in (10.2.1.9), p. 442, with
$t$ real and $\chi$ unitary. The integral is complex-linear in $f$
and uses Haar, with no conjugation, weight, or $a$-twist in the
ambient density. Proposition 9.1.2.5, (9.1.2.14)–(16), p. 402,
identifies the dual with $W^{-s,2}$ and gives the strict bound
$m<(s-1)/2$, so the only possible orders here are $0$ and $1$,
subject also to the multiplicity cap in (10.2.1.9), p. 442.
The transpose of convolution (inverse left translation in §9.3.1
and (9.3.1.2), p. 419) acts by

$$
(D\circ A(\varphi))(f)=\int f(y)d(y)\,d\mu(y),\qquad
 d(y)=\int\varphi(g)\eta_{\chi,t,m}(gy)\,d\mu(g).
$$

For compactly supported $f$, this follows by $x=gy$ in the inner
Haar integral. The formula extends by Cauchy–Schwarz, since
$d=\chi e^{itr}p(r)$ for a polynomial $p$ of degree at most $m$:
Expand $(r(g)+r(y))^m$ in the last integral. The $g$-angular average
kills all labels except $\chi|_{G^1}=\bar\eta|_{G^1}$. The quotient
factorization (10.4.2.5), p. 459, applies $Q_a$ to the input and
the orthogonal lift $S_a$ to the output. The functional of the
quotient pulled back along $Q_a$ is exactly the transpose pairing
above, not an extra multiplication on the input. Thus
(10.4.3.21)–(22), p. 469, send $d\otimes u$, with
$u=S_a(\psi_{\chi,t,m})$, to

$$
R f(x)=u(x)\int d(y) f(y)\,d\mu(y).
$$

This is the elementary dual tensor action of (C.3.6.7), PDF p. 705.
The selected $s=4$ is within the $s\ge3$ domain of Definition 10.4.3.2,
p. 470. Assume $d$ and $u$ are nonzero in this term; no existence of a
particular Hecke zero or of a surviving index is asserted.

## The two kernel routes

* **Haar.** (10.4.3.23) passes to the Hilbert tensor product and leaves
  the elementary tensor unchanged. The canonical product embedding
  in the order of the factors in (10.4.3.24), p. 470, sends it to
  $d(y)u(x)$ on $(y,x)$, with measure $(w^{-1}\mu)\otimes(w\mu)$.
  This input-first convention also matches (C.3.6.6), p. 705.
  For the output-first convention $k(x,y)$ of (10.4.3.25), flip the
  product measure as well, to $w(x)w(y)^{-1}\,d\mu(x)d\mu(y)$.
  Flipping does not change the density in the coefficient functional.
  With $K_\mu(x,y)=u(x)d(y)$, the printed integral (25) and the
  Haar integral obtained by (26) and (28) both act as $R M_{1/w}$,
  not $R$. Here $M_q$ denotes multiplication by $q$. The compatible
  Haar representation integrates $K_\mu f$ directly against $\mu$,
  with no extra factor in (25) or (26). Even supplying the missing
  evaluation on the right of (28) does not change this comparison.
  Formula (27) then subtracts the corrected Haar kernel from
  $\varphi(xy^{-1})$ for the order
  $(1-P_a^{\rm spec})A(\varphi)$. The restricted-input statement (29)
  does not identify the full-space kernel or reverse the order.
* **Weighted.** To represent $R$ against $\nu=w\mu$, use
  $K_\nu(x,y)=K_\mu(x,y)/w(y)$, with exactly one division. Its
  $L^2(\nu\otimes\nu)$ squared norm is
  $\|u\|_{L^2(w\mu)}^2\|d\|_{L^2(w^{-1}\mu)}^2$.
  The first expression in (10.4.3.30), p. 470 with the target
  space on p. 471, performs this correct conversion on its *given*
  Haar kernel, once the missing $f(y)$ in the proof's integral on
  p. 471 is supplied. The earlier
  [rational interface note](trace-divisor-singleton-diagonal.md#what-the-cited-kernels-supply)
  tracks the conversion starting from the asserted integral; it does
  not check that integral against the tensor. With the value from the
  printed (26), (30) yields $K_\mu/w(y)^2$; integration against $\nu$
  still gives $R M_{1/w}$. Multiplying by the output cutoff $\rho(x)$
  leaves the input weight unchanged. The operator label for the second
  expression in (30) is not part of this check.

A test that distinguishes both routes from the defining action is
$f(y)=\beta(r(y))\overline{d(y)}$, where $\beta\ge0$ is a nonzero
smooth bump on a compact subinterval of $(0,\log 2)$ on which $p$ is
nonzero. The character and radial polynomial make $f$ a compactly
supported Bruhat test in the selected left-action isotype
$\bar\eta|_{G^1}$. The true coefficient of $u$ is
$\int\beta|d|^2\,d\mu$, while either printed route gives
$\int\beta|d|^2/w\,d\mu$. The latter is strictly smaller because
$w>1$ on the support. Even if (25) is used as a separate definition,
its reciprocal-weight input measure forces the representing function
$w(y)u(x)d(y)$ by uniqueness against compactly supported tests.
This is not the tensor image. For this nonzero spectral density it
is not even in the required mixed space: The input square integral
in the flipped, output-first space is $\int |d|^2 w\,d\mu=\infty$;
read literally in unflipped output-first order it would instead be
$\int |d|^2 w^3\,d\mu=\infty$.

## Scope and Chapter 12 interface

The Haar and weighted conversions extend to every Hilbert–Schmidt
operator on $L^2(w\mu)$: Multiplication by $1/w(y)$ is an isometry
from the output-first mixed kernel space to $L^2(\nu\otimes\nu)$.
This does not require a spectral series. If the canonical tensor
series does converge to the actual $T$, using its kernel image with
(25)–(26) instead yields $TM_{1/w}$. Equality would force $T=0$:
$M_{1-1/w}$ has dense range, since the norm-one fiber is Haar-null.
These implications do not show that $T$ is nonzero. Also, $M_{1/w}$
is circle invariant, so the wrong operator would still pass the
circle-cancellation check if formed this way. Zero box averages
alone cannot verify the normalization.

The [circle-compression result](trace-circle-compression-qi.md) can
be used for the repaired Haar kernel of $T$ in (12.1.1.21), p. 503,
conditional on trace class, not to identify the named kernel from
(25)–(26) as printed. This locates a failure of the printed route,
not a refutation of (12.1.1.2) under its genuine $D'$ hypothesis or a
nonzero discrepancy for the full spectral trace.

**Review evidence.** The worker and independent reviewer
`singleton-review` (agent `kgNWGbu`, Yah transcript
`01a2026e-7431-72af-9cd0-6e6d00d6b127`) read rendered crops of
Masullo's [pinned PDF](../sources/masullo/README.md), not only the
text extraction. In particular, (10.2.1.9), p. 442, has the Haar
pairing; (10.4.3.24), p. 470, has the negative exponent first and
positive exponent second; (10.4.3.25), (26), and the first (30), p. 470,
each have the negative exponent on $y$. The positive-weight square
space for (30) is in the continuation on p. 471. For example, the
p. 470 top-left point rectangles $(352,247,443,264)$ and
$(441,247,548,264)$ show the signs in (24); $(210,331,387,355)$
shows the integral in (25). The reviewer independently checked the
transpose and lift against the defining pairing, both kernel routes
separately, the compact witness, and the failed mixed-space rescue.
The scope excludes the second operator label in (30), convergence of
the series, and proof of the Chapter 12 trace identity. The angular
and box results are reused from the accepted notes, not rechecked
against their source. Selector Yah: `01a2026d-2089-78a5-ad69-aa60b8c7a8b7`.

**Next bounded check:** On the weight-four Gaussian norm-one
isotype, check whether the log Fourier transform of the closed
$a=1/2$ theta subspace contains $Z v$ for every compactly supported
smooth frequency function $v$, where $Z(t)=L(1/2+it,\bar\eta)$.
Use a weight-four complex-place lift and the standard finite unit
factors, and check the permitted zero-moment test class. This would
put all smooth frequency tests supported away from the zeros in the
theta closure, the local finite-rank premise in the
[rational singleton argument](trace-spectral-q.md#translation-and-local-finite-rank).
Kernel-series convergence, an actual trace-class estimate, scalar
trace nonvanishing, and local-to-global diagonal comparison remain
separate.
