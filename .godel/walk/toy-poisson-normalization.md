# The toy Poisson sum needs the lattice covolume

## Printed claim

Masullo, *The Music of the Primes*, §1.2.8, printed p. 17, claim
beginning “By the Poisson Summation Formula, this equals” and its display.
For $\gamma>1$ and $\varphi\in C_c^\infty(\mathbb R_{>0})$, the preceding
paragraph displays $\sum_{m\in\mathbb Z}M(\varphi)(z_m)$, where
$z_m=2\pi im/\log\gamma$ and $M$ uses $t^s\,dt/t$. The Poisson paragraph
equates it to $\sum_{k\in\mathbb Z}\varphi(\gamma^k)$, with no prefactor.
In Example 1.8.1.1, printed p. 41, the corresponding display does include
$\log\gamma$. The rendered formula crops on pp. 17 and 41 of the PDF were
checked as raster images via terminal pixel plots, separately from the
chapter Markdown and raster OCR. Both printed page numbers are PDF
ordinals. The PDF SHA-256 was verified as
`e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5`.

## Checked scope

Set $L=\log\gamma>0$ and $g(u)=\varphi(e^u)$, a compactly supported smooth
function on $\mathbb R$. For the Fourier convention with kernel
$e^{-2\pi i\xi u}$, the change of variables $u=\log t$ gives
$M(\varphi)(z_m)=\widehat g(-m/L)$. The Fourier samples are absolutely
summable by rapid decay, so replacing $m$ by $-m$ leaves their sum unchanged.
The lattice $L\mathbb Z$ with counting measure gives the quotient Haar
measure of total mass $L$, hence Plancherel measure on the dual lattice is
$1/L$ times counting measure. Thus the Poisson identity is
$$
\sum_{m\in\mathbb Z}M(\varphi)(z_m)
  =L\sum_{k\in\mathbb Z}\varphi(\gamma^k).
$$
In particular, take $\gamma=e^2$. Let $g(u)=\exp(1-1/(1-u^2))$ for
$|u|<1$ and $g(u)=0$ otherwise. This smooth bump has $g(0)=1$ and
support $[-1,1]$. Then $\varphi(t)=g(\log t)$ is an admissible test with
support $[e^{-1},e]$, so only $k=0$ contributes to the lattice sum.
The left side of the printed equation is $2$, whereas its right side is
$1$. The missing covolume factor, not the sign in the indexing, causes
the failure.

The appeal to Poisson summation is Masullo's. His Theorem D.1.2.7(3),
printed p. 749, uses the Plancherel normalization from Situation D.1.2.6;
that appendix locator was checked in the chapter Markdown, not in the
rendered page. The log-coordinate specialization, sign reindexing, and
counterexample here are the reviewer's. The scope is the scalar identity
only: It neither checks the preceding operator and transpose trace claims
nor reviews the following support-vanishing claim.

## Accepted Lean evidence

At `9b447a5ce120c101fb0fd341378d877f2bb469c9`,
`Proofs/Lemmas/ScaledPoisson.lean` declares `Masullo.schwartz_scaled_poisson`.
For a complex-valued Schwartz function $b$ on $\mathbb R$ and any real
$t>0$, it equates $\sum_n b(tn)$ to $t^{-1}$ times
$\sum_n\widehat b(t^{-1}n)$, with both sums indexed by $\mathbb Z$.
Its argument uses Mathlib's Schwartz Poisson theorem at zero after
positive dilation. Apply it with $b=g$ and $t=L$. This is an additive
Fourier statement, not a direct formalization of the Mellin change of
variables, the multiplicative counterexample, or the trace formula. No
Lean proof or declaration is added here.

A fresh `lake build --wfail +Lemmas.ScaledPoisson` and scratch import in
the campaign workspace based on the cited revision gave:

```text
Masullo.schwartz_scaled_poisson : ∀ (b : SchwartzMap ℝ ℂ) {t : ℝ},
  0 < t → ∑' (n : ℤ), b (t * ↑n) = t⁻¹ • ∑' (n : ℤ), (FourierTransform.fourier b) (t⁻¹ * ↑n)
```

`#print axioms` reported only `propext`, `Classical.choice`, and
`Quot.sound`.

## Independent review

A fresh independent Yah review of the pinned source and accepted
`9b447a5ce120c101fb0fd341378d877f2bb469c9` confirmed the missing
factor from separate rendered pixel inspection of both displays. It
derived the factor by dilating the unit-lattice Poisson formula, checked
the same bump counterexample, and independently checked the signature
and axioms by importing the accepted theorem, not rebuilding it. It
confirmed that the theorem has an explicit Schwartz function, an
implicit positive scale, and sums over all integers, including zero;
there is no separate summability hypothesis. The mathematical refutation
here is the rendered-source comparison and the counterexample based on
the Lean scaled Poisson theorem. Lean does not state the refutation in
multiplicative coordinates.
