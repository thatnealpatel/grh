---
evidence_revision: 022676f32fb32118354a025cb57b7c48d5dac9cf
outcome: parked
---

# A uniform bound for two separated Weil packets

Fix a real smooth packet $b$ of support diameter at most $0.1$. Let $B(z)=\int b(x)e^{zx}\,dx$, require $B(\pm1/2)=0$, and assume $H(z)=B(z)B(-z)$ is nonzero at $z=\rho-1/2$ for every nontrivial zeta zero with $\Re\rho>1/2$. For the rational Weil form the claim is $|K(t)|\le K(0)$ for every $t\ge0$, where $K(t)=Q(b,T_t b)$.

**Parked:** We have a [bounded interval of separations](weil-two-packet-finite-separation.md), not control independent of separation. Reopen with a signed prime-sum estimate uniform in $t$, or a positivity-preserving extension that identifies the extended kernel with this particular $K$.

At $t=\log 2$ the prime cross term for this narrow packet is $-(\log 2)\|b\|_2^2/\sqrt2$, in addition to the archimedean term. At large $t$ the continuous prime main term cancels by the moment conditions, but applying the classical prime number theorem error bound to the smoothed sum still gives a growing envelope.

The spectral diagnostic is stronger: For $\Re s>1/2$ the unilateral Laplace transform is $\sum_\rho H(\rho-1/2)/(s-(\rho-1/2))$, counting multiplicities (the zero symmetry removes the choice of translation sign). Smoothness gives normal convergence off the poles. Bounded $K$ would make the transform holomorphic on $\Re s>0$, excluding any right-of-line zero by the nonvanishing hypothesis. Conversely, under RH the spectral coefficients are nonnegative squared moduli. These are paper arguments, not a proof of the uniform bound or a Lean result. The [Gaussian truncation test](gaussian-translate-uniform-localization.md) rules out one proposed way of extending the window.
