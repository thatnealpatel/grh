# From a trace identity to a statement about Hecke zeros

**Status: Provisional readings from `pdftotext -layout` of the [digest-matched edition](../sources/masullo/README.md), and project reasoning as labeled.** Page numbers are PDF ordinals. This does not extend or replace the [visual finding on pp. 522–523](divisor-heading.json).

## The two trace statements have different interfaces

- **Theorem 12.5.1.1, pp. 519–520:** The test is in $D(C_F)$ and vanishes on $C_F^1$. Equations (12.5.1.1)–(12.5.1.4) use zeros in the interior of a strip with full orders $N(c)$.
- **Theorem 13.3.1.1, p. 522:** The test obeys the Mellin-jet conditions (13.3.1.2), with derivative orders $0$ through $[F:\mathbb Q]-1$. Equations (13.3.1.1) and (13.3.1.3) restrict the spectral sum to the critical line and use $N_{\mathrm{spec}}(c)=\min\{N(c),[F:\mathbb Q]\}$. The heading that follows has an unresolved theorem reference and a footnote asking for the statement. Check the exact test class, weights, and local factors before comparing these statements. The text's description of Chapter 13 as a restatement does not justify specializing the strip, clipping orders, or changing test classes.

**Project control for the test class.** Take $F=\mathbb Q$ and a radial test $\varphi(g)=h(\log|g|_F)$ for a nonzero nonnegative smooth $h$ compactly supported in $(1,2)$. The norm-one subgroup is compact, so the radial lift is a smooth compactly supported test (it factors through the Lie quotient $\mathbb R_{>0}$). It vanishes on $C_F^1$. But the $k=0$, trivial-character condition in (13.3.1.2) integrates it against a positive Haar measure and is not zero. Thus the Chapter 12 condition does not imply the Chapter 13 condition, independently of whether either trace formula holds.

## Two proposed deductions, not two proofs

- **Holomorphic approximation:** §§1.4.2–1.4.6, pp. 28–30, sketch a one-sided family of tests and a Montel/analytic-continuation argument for the finite Hecke logarithmic derivative. Section 1.4.6 and the letter excerpt on p. 35 explicitly say that Weil positivity is not used in this route. The extraction of p. 522 n. 3 also requests a deduction by approximation, but with $e^{-s|\log t|}$, not the one-sided family. The two approximations need separate interfaces.

  **Project control, independently challenged by a Yah text reader.** For $F=\mathbb Q$, trivial $\chi$, and a fixed real $z>\max(1,\sup I)$, take the proposed nonnegative cutoff and mollifier. If the resulting smooth compact profiles $a_n$ are supported above $1$ and converge to $t^{-z}$ for $t>1$ as requested, the two real unit terms on p. 29 add. They give

  $$A_n=\int_1^\infty a_n(t)\frac{t^{-1/2}}{t-1}\,dt.$$

  Fatou's lemma on $(1,2)$ gives $\liminf_n A_n=+\infty$, since $t^{-z-1/2}$ tends to $1$ at the singular endpoint. This is already failure at one parameter, not just a failure of uniformity in $z$. If the Archimedean term is read as a principal value, the individual cutoff tests still have zero value at the singularity, so the supported terms in (B.4.3.13), p. 619, supply no subtraction. Compare (B.4.4.20), p. 625; the divergence in modulus does not depend on an overall sign. This blocks the displayed separate Archimedean bound, not the conclusion about zeros or every continuation argument. The [fixed-parameter subtraction below](#fixed-parameter-subtraction-over-the-rationals) gives a conditional continuation argument over $\mathbb Q$ without a Montel subsequence.
- **Positivity:** §14.1.2, pp. 528–529, describes the intended content of Theorem 13.3.1.2 as location on the critical line and a degree bound away from the central zero, with a caveat on the parametrization of the central point. It credits a positivity criterion with an unresolved theorem reference; see also p. 533. This is evidence of the author's intended result, not a statement or proof printed under the heading on p. 522. Proposition 14.1.2.3 on p. 531 assumes separate conjectures and cannot supply an unconditional deduction. A positivity repair would need a precise criterion applicable to the available test class, with enough tests to detect off-line zeros and distinguish clipped orders from true orders away from the center. The usual nonzero convolution squares cannot be inserted into Chapter 12: For $\psi^*(g)=\overline{\psi(g^{-1})}$, $(\psi*\psi^*)(1)=\int|\psi(g)|^2\,d\mu(g)>0$ for nonzero $\psi\in D(C_F)$. This does not rule out a restricted-test criterion for Chapter 13.

## Fixed-parameter subtraction over the rationals

**Source comparison (provisional, independently checked in Yah against the digest-matched extraction).** The positive-log radial specialization of the displayed local integral in (12.5.1.1), p. 519, uses $g_\infty=\pm e^x$ with $dx$ on each sign. Its kernel is

$$H(x)=\tfrac12 e^{x/2}\left((e^x-1)^{-1}+(e^x+1)^{-1}\right)=\frac{e^{3x/2}}{e^{2x}-1}.$$

The real terms as written in §§1.4.1 and 1.4.3, pp. 28–29, instead use $|1-t|$ for both signs. Both expressions have the same orders at zero and infinity, so the discrepancy does not affect the subtraction estimate. On $p^{-m}\mathbb Z_p^\times$, both $|g_p|_p$ and $|1-g_p|_p$ equal $p^m$ for $m>0$. The shell has the same multiplicative volume as $\mathbb Z_p^\times$, so the volume cancels in (12.5.1.2) and the coefficient is $(\log p)p^{-m/2}$. The norm-one volume is one over $\mathbb Q$ under (A.3.2.1), p. 560. The polar terms, orders, and shift by $1/2$ are as in (12.5.1.3)–(12.5.1.4), pp. 519–520, with the stated spectral sum over the interior strip. These are checks of the displayed interface, not of the trace proof or the validity of all cited principal-value identities.

**Project repair, conditional on the trace.** Work over $\mathbb Q$ with the trivial character and $x=\log |g|_{\mathbb Q}$. Fix a width $0<a<1/2$. For $f\in C_c^\infty((0,\infty))$, extend by zero to $\mathbb R$ and use $\varphi(g)=f(x)$. The test is smooth because it factors through the Lie norm quotient and has compact support because the norm kernel is compact. It vanishes near norm one, and compact averaging kills the nontrivial character terms. Assume the following rational, one-sided trace identity for these tests:

$$
\int_0^\infty H(x) f(x)\,dx
+\sum_{p,m\ge1}(\log p)p^{-m/2} f(m\log p)
=\int_0^\infty (e^{x/2}+e^{-x/2})f(x)\,dx
-\sum_{w\in Z_a} m(w)\int_0^\infty e^{wx}f(x)\,dx.
$$

Here $p$ runs over primes, $Z_a$ consists of the shifted nontrivial zeta zeros $w=\rho-1/2$ with $|\Re w|<a$, and $m(w)$ is the order of the zero. Only the bounds $H(x)=O(x^{-1})$ near zero and $H(x)=O(e^{-x/2})$ at infinity, with local integrability for $x>0$, are used. The normalization in this interface is raw global Haar with norm-one volume one. This is an input, not a proof of either trace evaluation or of the range of widths for which it holds. In particular, the input is not the classical explicit formula with a sum over **all** zeros. The proof also allows boundary terms with weights bounded by the zero orders: Their shifted real parts still lie in $[-a,a]$, so the same bounds below apply. This does not establish which spectral sum the actual cutoff gives. The construction invoked on p. 520 uses positive Sobolev degree; (10.3.2.3)–(10.3.2.4), p. 454, allow clipped contributions at the boundary. A trace premise must state which terms it includes.

**Admissible tests and uniform bounds.** Fix real $z_0>1$. Take smooth cutoffs $0\le\chi,\psi\le1$ with $\chi(y)=0$ for $y\le1$, $\chi(y)=1$ for $y\ge2$, $\psi(y)=1$ for $y\le1$, and $\psi(y)=0$ for $y\ge2$. For integers $n\ge2$ use

$$f_{n,z}(x)=\chi(nx)\psi(x/n)(e^{-zx}-e^{-z_0x}),\qquad x>0.$$

Each test vanishes near norm one, and no mollification is needed. Let $K$ be a compact subset of $D_a=\{z:\Re z>a\}$. Uniformly on $K$, the uncut difference is $O_K(x)$ at zero, so the Archimedean integrand is bounded there. At infinity the kernel and both exponentials decay. Dominated convergence gives a locally uniform limit $A(z)$ of the Archimedean term, holomorphic on $D_a$.

For the spectral term, put $u_{n,z,\sigma}(x)=e^{\sigma x}f_{n,z}(x)$ with $\sigma\in[-a,a]$. Before cutoff the weighted difference is $O_K(x)$ at zero, its first two derivatives are bounded there, and it and its derivatives decay at least as fast as $e^{-\delta x}$ at infinity, where $\delta=\min(\inf_{z\in K}\Re z,z_0)-a>0$. Both $\|u_{n,z,\sigma}\|_1$ and $\|u_{n,z,\sigma}''\|_1$ are bounded uniformly in $n$, $z\in K$, and $\sigma$. In differentiating the lower cutoff twice, the worst terms have size $O_K(n^2 x+n)$ on $[1/n,2/n]$, with bounded integral. Upper cutoff derivatives contribute bounded integrals by exponential decay. Twice integrating by parts in $e^{i\gamma x}$, without boundary terms, gives

$$\left|\int_0^\infty e^{(\sigma+i\gamma)x} f_{n,z}(x)\,dx\right|\le \frac{C_K}{1+|\gamma|^2}.$$

The classical zeta zero count with multiplicities, $N(T)=O(T\log T)$ for $|\Im\rho|\le T$ (compare the bound per unit ordinate window on p. 642), makes this majorant summable over $Z_a$ with weights $m(w)$ (use dyadic ordinate bands). Each integral tends locally uniformly to $(z-w)^{-1}-(z_0-w)^{-1}$ by dominated convergence for that $w$. Hence the cutoff spectral sums converge locally uniformly to the holomorphic function

$$S_a(z)=\sum_{w\in Z_a}m(w)\left(\frac1{z-w}-\frac1{z_0-w}\right),\qquad z\in D_a.$$

The same subtraction that removes the Archimedean divergence thus provides summable spectral bounds. No assertion about conditional convergence of an unsubtracted zero series is needed.

**What can be recovered.** On $\Re z>1/2$, the ordinary Euler series and dominated convergence give the prime term limit $-F(z)+F(z_0)$, where $F(z)=\zeta'(z+1/2)/\zeta(z+1/2)$. The polar integrals there give $b(z)-b(z_0)$ for $b(z)=(z-1/2)^{-1}+(z+1/2)^{-1}$. These two limits are not asserted on all of $D_a$. Substituting on the common half-plane gives

$$F(z)+b(z)=A(z)+S_a(z)+F(z_0)+b(z_0).$$

Meromorphic identity extends this equality to $D_a$. The plus sign on the left uses the positive prime weights, whose Euler series is the **negative** logarithmic derivative, unlike the sign of the limit as written in §1.4.4, p. 29 (compare (B.6.1.12), p. 638). It also gives the cancellation of the residue $-1$ at the zeta pole. Subtraction at $z_0$ changes only a constant, so it cannot hide any pole of $F$ at a zeta zero. Since $A+S_a$ is holomorphic, there is no nontrivial zero with $\Re\rho>1/2+a$, or, by the functional equation, with $\Re\rho<1/2-a$. This is a fixed-width conclusion, not exclusion at the boundaries. Only if the trace input holds for widths tending to zero does this imply RH. It yields no bound on multiplicities on the critical line and does not use or supply the missing Chapter 13 theorem.
