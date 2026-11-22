# Boundary point evaluation fails in the printed strip topology

**Result:** Corollary 9.2.2.5(2), p. 414, (9.2.2.24), asserts
continuity at $k=0$, $s=1$, and $z_0=1$ on the strip with base
$I=[-1,1]$. Smooth compact log profiles give entire Mellin transforms
with value one at $1$ that tend to zero in every defining line
seminorm for a permitted interior sequence. Separately, their inverse
profiles tend to zero in the positive $W_I^1$ norm. These are two
checks, not a transport of the positive norm to the printed topology.

The [previous source audit][vector] checked a boundary-vector
membership failure at $s=1$ on pp. 446 and 417, with a positive
membership control at $s=2$. This check locates an upstream failure
in the scalar evaluation claim, without any Hecke-zero assumption.

## Printed cutoff and test domain

In the [pinned edition](../sources/masullo/README.md), the cutoff
below (9.2.2.24) uses two weak inequalities, $0\le k\le [(s-1)/2]$,
so at $s=1$ it includes $k=0$. The strip notation (B.5.3.1), p. 632,
is the inverse image of $I$ under the real-part map, so $1$ qualifies
on the right edge. The bracket reading is $[0]=0$ by the floor
convention in the text below (10.3.2.4), p. 454, also checked for
the [accepted boundary-vector audit][vector]. Proposition 9.2.2.4(3),
p. 414, expressly assumes even integral $s$ for the Mellin
isomorphism (9.2.2.22). Corollary 9.2.1.4, p. 407, which the proof
proposes to mirror, concerns points with real part strictly less
than $b$ in the degree-$2N$ space; it supplies no endpoint estimate
at degree one.

For integers $R\ge 2$, choose $\chi_R\in C_c^\infty(\mathbb R)$
with $0\le\chi_R\le1$, support in $[1/2,R+1]$, and value one
on $[1,R]$. Set

$$
A_R=\int_{\mathbb R}\frac{\chi_R(x)}{\sqrt{1+x^2}}\,dx,\qquad
f_R(x)=\frac{e^{-x}\chi_R(x)}{A_R\sqrt{1+x^2}},\qquad
\phi_R(t)=f_R(\log t).
$$

The support of $\phi_R$ stays away from $0$ and $\infty$ for each
$R$, so all its derivatives meet the decay condition of Definition
B.2.1.1(2), p. 593. Hence $\phi_R$ is in
$\mathcal S_{\mathrm E}(\mathbb R_{>0})$, the normed test domain in
Definition 9.2.2.1, p. 412. Use the Mellin convention of Proposition
D.3.2.5, p. 802, (D.3.2.2), with $t^z\,dt/t$:

$$
u_R(z)=M(\phi_R)(z)=\int_{\mathbb R} f_R(x)e^{zx}\,dx.
$$

Compact support gives entireness and integration by parts gives
rapid vertical decay of every polynomial order, uniformly on
bounded real-part intervals for each $R$. Thus $u_R$ is in
$A\mathcal S(\mathbb C)$ of Definition D.3.1.3, pp. 800–801,
the dense test space in Definition 9.2.2.3. We have $u_R(1)=1$ and
$A_R=\log R+O(1)$ by comparison with the integrals on $[1,R]$
and $[1/2,R+1]$.

## Positive norm and the degree-two control

The maximum of the endpoint powers in (9.2.2.4), p. 412, is
$e^{2x}$ on the support, and it cancels $e^{-2x}$ from $|f_R|^2$.
The squared positive norm is

$$
\|\phi_R\|_{I,s}^2=A_R^{-2}\int_{\mathbb R}
             (1+x^2)^{s/2-1}\chi_R(x)^2\,dx.
$$

At $s=1$, use $\chi_R^2\le\chi_R$ to bound the squared norm by
$1/A_R\to0$. At $s=2$ it is at least $(R-1)/A_R^2\to\infty$.
Indeed, at $s=2$ the general bound on the same compact test class is
$|M(\phi)(1)|\le\sqrt\pi\|\phi\|_{I,2}$: Apply Cauchy–Schwarz
with squared dual weight $e^{2x-2|x|}/(1+x^2)\le 1/(1+x^2)$.
This control is for the **positive norm**. It is not a continuity
claim in the line topology.

The accepted Lean theorem [Masullo.boundaryLogJet_exists_smooth_extension_iff][lean]
gives the exact weighted log-model threshold $2m+1<s$ for real
$s\ge0$, $m\in\mathbb N$, and $|\Re z|=\alpha$, including width
zero. With $\alpha=1$, $z=1$, and $m=0$, this corroborates the
positive norm result. It does not check (9.2.2.19), whose topology
has to be tested independently.

## Defining line topology

Definition 9.2.2.3, p. 414, uses the separate line norms
(9.2.2.19), not their supremum. The sequence is in $\mathbb R$
and must have the boundary points as accumulation points; neither
actual edge lines nor exterior lines are required. Choose the
interleaving of $\sigma_n^\pm=\pm(1-1/(n+2))$, $n\ge0$.

At any fixed $\sigma<1$ and any fixed integer $j\ge0$,
Plancherel, with Fourier kernel $e^{iyx}$, gives

$$
\left(\frac{1}{2\pi}\|u_R^{(j)}(\sigma+i\,\cdot)\|_{L^2(dy)}\right)^2
\le \frac{1}{2\pi A_R^2}
    \int_{1/2}^\infty
      \frac{x^{2j}e^{-2(1-\sigma)x}}{1+x^2}\,dx
\longrightarrow 0.
$$

The integral is finite for each $(\sigma,j)$, and no estimate
uniform in $\sigma$ or $j$ is needed. In particular, the result
holds for every interior-only sequence, even if all fixed
derivative orders are included. The displayed $k$ in (9.2.2.19)
is not explicitly ranged by $s$ in that definition; taking $k=0$
at $s=1$ under the nearby $[s/2]$ convention, or using any family
of such fixed orders on the chosen lines, yields the same null
sequence. Continuity of evaluation on the completion would imply
continuity on this test space, contradicting $u_R(1)=1$.

The seminorm check is unchanged at $s=2$, where the positive norm
control has the opposite behavior. In particular (9.2.2.22),
**with the interior-only line topology**, cannot have a continuous
inverse even in this even-degree case. Replacing the chosen family
by the endpoint $L^2$ norms of orders zero and one gives the
positive-norm topology at $s=2$ by Plancherel, as in (9.2.2.5),
p. 412: The sum of the two endpoint weights is between the
maximum and twice the maximum. This is a different topology,
not a justification of (9.2.2.19). For the positive weighted
model alone, changing the boundary cutoff to $2k+1<s$ removes
the equality error. That strict inequality by itself does not
repair the interior-line topology.

## Scope and successor

This is an ordinary-mathematics source counterexample to the
printed boundary continuity assertion on a permitted topology.
It does not test interior point evaluation and does not use a
zero of an $L$-function. No Lean sources changed. The prior
membership result, quotient annihilation, basis totality, and
trace assembly are separate. In particular, the degree-two
topology mismatch is not a refutation of a spectral trace
statement formulated in the strong weighted norm.

**Next bounded check:** Test the separate boundary trace claim
of Proposition 9.2.2.4(2), p. 414, (9.2.2.20), at $s=2$ on the
same interior sequence. Use Mellin transforms of compact cutoffs
of a smooth log profile equal to $e^{-x}$ on $x\ge1$ and zero
on $x\le1/2$. Check whether their interior completion limit has
a right-edge trace in $L^2(d\tau)$ before testing the stronger
$W^{s,2}$ assertion. This would distinguish failure of trace
regularity itself from failure of point evaluation on a trace.

## Review evidence

Read-only review against `6dcfdcf66739d8c8f9160b9ab18023a25570fb61`:
Yah session `01a20231-eb92-70d4-b967-5060d946922e`, agent `DPKekYy`
(`point-review`). Both readers matched the pinned digest and used
layout coordinates to locate direct raster crops, displayed as
Braille pixels without OCR. The reviewer independently found:

- **Printed selection:** The rendered p. 414 statement allows real
  $s\ge0$ and uses the weak cutoff. The rendered strip definition
  on p. 632 and bracket convention on p. 454 put $z_0=1$ and $k=0$
  within the printed hypotheses at $s=1$ and $s=2$.
- **Positive-norm route:** The rendered weight in (9.2.2.4), p. 412,
  gives the $1/A_R$ upper bound at $s=1$ and a squared norm of order
  $R/A_R^2$ at $s=2$. The reviewer also checked the general $s=2$
  Cauchy–Schwarz bound and the separate even-degree restriction
  on transport in Proposition 9.2.2.4(3).
- **Defining-topology route:** The rendered (9.2.2.19) ranges over
  a sequence accumulating at both edges, not a supremum norm.
  The reviewer independently applied Plancherel on each fixed
  line, including all fixed derivative orders, and found the null
  sequence at both degrees and the failure of the continuous
  inverse at $s=2$. The reviewer checked the test domains and
  positive Mellin sign in the rendered definitions on pp. 593
  and 800–802. The p. 407 dependency provides only interior
  evaluation for the even-degree half-plane space.

These findings agree with the two calculations above. No reading
needed for the verdict remains provisional; the derivative-index
ambiguity is in the print, and the estimate does not rely on
choosing one interpretation. The previous p. 446 membership audit
is inherited, not rechecked here.

[vector]: boundary-vector-membership-q.md
[lean]: ../../Proofs/Props/BoundaryLogJet.lean
