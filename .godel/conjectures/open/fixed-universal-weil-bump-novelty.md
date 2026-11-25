---
evidence_revision: 0310a071f9cb4685281a0d9fde9f1ce23f5d774f
---

# Does the fixed universal Weil bump warrant an external note?

**Claim to test:** The [two-edge calculation](../../primers/weil-complements.md)
may warrant a narrow external note if using one explicit, fixed,
pole-free bump yields a useful consequence beyond the neighboring
criteria. The paper argument supports a fixed-test criterion, not a
priority claim or a new zero-free region.

For one real smooth compactly supported $\phi$, let
$C(y)=\int\phi(x+y)\phi(x)\,dx$ and
$\Psi(z)=M_\phi(z)M_\phi(-z)$, where $M_\phi(z)=\int\phi(x)e^{zx}\,dx$.
The precise package to compare uses a single $\phi$ fixed before the
separation and exponent are chosen, with $M_\phi(\pm1/2)=0$ and
$\Psi(\rho-1/2)\ne0$ at every nontrivial zero. The paper construction
convolves tilted uniform densities paired with their reflections on
intervals $[-\epsilon_n,\epsilon_n]$, with $2\sum_n\epsilon_n<r<1/8$.
For $\theta>1/2$ and $U_n(w)=2\sinh(\epsilon_n w)/w$ (continued at zero),
the normalized factors are $U_n(\theta+z)U_n(\theta-z)/U_n(\theta)^2$.
Their zeros lie only on $\Re z=\pm\theta$. The product has no zeros in
the centered strip and decays rapidly on the imaginary axis, giving a
smooth compact density $g$. Then $\phi=(\partial^2-1/4)g$ kills both
polar moments.

For this bump the prime-power sum
$S(L)=\sum_{n\ge2}\Lambda(n)n^{-1/2}C(\log n-L)$ satisfies
$S(L)=O(e^{aL})$ exactly when all shifted zeros are in
$|\Re(\rho-1/2)|\le a$, for each $a\ge0$. The exact two-pulse block has
diagonal $Q(\phi)$ and mixed entry $-S(L)+O_\phi(e^{-5L/2})$. The decay
term matters for exact block positivity. At a shifted zero $z_\rho$ with
$\Re z_\rho=\alpha\ge0$, the paper residue argument gives
$\limsup_{L\to\infty}e^{-\alpha L}|S(L)|\ge m_\rho|\Psi(z_\rho)|$.
It does not give the first violating separation.

**Closest checked precedents:** [Danesh, v1, §4 Lemma 3 and Theorem 4, and §5](https://arxiv.org/abs/2611.10726v1)
gives the translated pole argument with a bump chosen for a target zero,
a two-interval criterion with shrinking widths and varying pairs, and
the moving prime-power formula. [Suzuki, Theorems 1.1, 1.6, and 1.7](https://doi.org/10.1112/jlms.12785)
gives fixed-scalar criteria; the mixed entry here is a compact smoothing
of the distributional second derivative of Suzuki's screw function, in
the corresponding sign convention. [Connes–Consani, §3 and Appendix C](https://arxiv.org/html/2006.13771#A3)
already uses the pole-killing differential operator for a criterion
quantified over all qualifying tests. This comparison is not an
exhaustive priority search.

**Discriminating test:** Check fixed-translate precedents specifically
for a universal pole-free witness and the same endpoint constant. Then
name a consequence the neighboring criteria do not already supply.
The actual packing-complement embedding gives a concrete comparison to
try: Does the fixed witness enable an independent estimate or a sharper
obstruction for a specified operator or test class? If the only gain is
changing the quantifiers in an already RH-equivalent prime estimate,
retain it as an internal lemma and cite the antecedents. No priority
claim follows from not finding the exact package verbatim.
