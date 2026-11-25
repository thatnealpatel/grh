# The chi8 bridge: What changes under a character twist

**Claim on paper.** For the primitive even quadratic character modulo $8$, the raw
prefix count is already bounded. The log convolution uses a signed half-line kernel, and
Poisson reflection is about $v=\tfrac12\log 8$, not $v=0$. Neither fact is a
zero-location assertion.

**Small calculation: Prefix and sign.** Write $\chi=\chi_8$, with values $1,-1,-1,1$ on
$1,3,5,7$ modulo $8$ and zero on even integers. For $x\ge0$, the prefix
$A(x)=\sum_{1\le n\le x}\chi(n)$ is $+1$ on $8k+[1,3)$, $-1$ on $8k+[5,7)$, and zero
elsewhere in each period. Sum $g(n)=g(X)-\int_n^X g'(x)\,dx$ with weights $\chi(n)$.
The resulting finite Abel identity gives full weight at an integer upper endpoint
$X\ge1$:
$$
\sum_{1\le n\le X}\chi(n)g(n)=A(X)g(X)-\int_1^X A(x)g'(x)\,dx.
$$
Take $g(x)=f(xe^{-v})$ for even compact smooth $f$ supported away from zero, and $X$
beyond the support. Substituting $x=e^u$ gives
$$
H_{\chi,f}(v)=e^{-v/2}\sum_{n\ge1}\chi(n)f(ne^{-v})=(K_\chi*h_f)(v),
\quad K_\chi(u)=-\mathbf1_{u\ge0}e^{-u/2}A(e^u),\quad h_f(t)=e^{-3t/2}f'(e^{-t}).
$$
No mean-zero condition on $f$ and no separate $n=1$ term are needed. At $v=0$ a bump
with $f(1)=1$ and positive support in $(3/4,5/4)$ gives $1=-\int_1^{5/4} f'(x)\,dx$,
checking the sign.

**Three absolute-convergence domains.** Use $Tq(s)=\int q(v)e^{-(s-1/2)v}dv$ and
$F(s)=\int_0^\infty f(x)x^{s-1}dx$.

1. The raw Dirichlet series is absolutely convergent exactly for $\Re s>1$, since
   $|\chi|$ is one on the odd integers.
2. The bare kernel transform is absolutely convergent exactly for $\Re s>0$: Its
   absolute integral is $\int_1^\infty |A(x)|x^{-\Re s-1}dx$, with a fixed amount of
   support per period. On this domain, finite Abel summation for $g(x)=x^{-s}$ has a
   vanishing boundary term $A(X)X^{-s}$, giving $TK_\chi(s)=-L(s,\chi)/s$. In contrast,
   the raw untwisted floor boundary term does not vanish for $0<\Re s\le1$. Integration
   by parts gives $Th_f(s)=-sF(s)$, so absolute convolution Fubini gives
   $TH_{\chi,f}=LF$ on $\Re s>0$.
3. The observable transform is entire **as an integral**. With Fourier phase
   $e^{-2\pi i x\xi}$, Poisson summation on the eight residue classes uses the Gauss sum
   $$
   \sum_{r\bmod 8}\chi(r)e^{2\pi i kr/8}=2\cos(\pi k/4)-2\cos(3\pi k/4)=\sqrt8\,\chi(k).
   $$
   Evenness halves both full sums, with no zero term. The conductor normalization is
   $$
   H_{\chi,f}(v)=\frac{e^{v/2}}{\sqrt8}\sum_{k\ge1}\chi(k)\widehat f(ke^v/8)=H_{\chi,\widehat f}(\log8-v).
   $$
   The original sum vanishes far left, and the reflected sum decays faster than every
   exponential to the right. This proves entire integral convergence, also with any
   fixed log power inserted. Continuation extends $TH_{\chi,f}=LF$, not the domain of
   absolute kernel Fubini.

**What it does not show.** At an $L$-zero $\rho$ of order $m$, the actual samples
$(TH_{\chi,f})^{(j)}(\rho)$ vanish for $j<m$. For nonzero $f$ the observable order is
$m+\operatorname{ord}_\rho F$, not necessarily $m$. At the simple zero $s=0$, for
example, a nonnegative nonzero bump has $F(0)>0$, while replacing the bump by $xf'(x)$
multiplies $F$ by $-s$ and gives order two. The kernel is not absolutely integrable with
the sample weight there. Pairing the two signed intervals in each period gives the
conditional value
$$
TK_\chi(0)=-\sum_{k\ge0}\int_{8k+1}^{8k+3}\left(\frac1x-\frac1{x+4}\right)dx<0.
$$
The paired terms are $O((1+k)^{-2})$, and any unfinished block tends to zero. The
observable's zero is not a zero of this conditional kernel transform.

**Source and next formal target.** The bridge above is a paper derivation.
[`Chi8Origin.lean`](../../Proofs/Examples/Chi8Origin.lean) checks `Chi8Origin.χ_even`,
`Chi8Origin.conductor_eq`, `Chi8Origin.LFunction_zero`, and
`Chi8Origin.deriv_LFunction_zero_ne_zero`.
[`DirichletPeriodicPrimitives.lean`](../../Proofs/Lemmas/DirichletPeriodicPrimitives.lean)
provides `Masullo.dirichletPartialSum_data` for nonprincipal characters. Specialize the
finite Abel identity to the literal $\chi_8$ prefix first, using
`Finset.sum_range_by_parts'` for the discrete endpoint bookkeeping and then the
real-cutoff integral identity. Check $X=1$ and the full integer endpoint before changing
variables to the half-line convolution.
