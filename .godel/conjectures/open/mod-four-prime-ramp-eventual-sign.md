---
evidence_revision: bbca37033019090f6f40e6223b5054d382c9d789
---

# Eventual sign of the genuine mod-four prime ramp

Let $\chi$ be the primitive real character modulo $4$. For
real $X\ge1$ set

$$P(X)=\sum_{p<X}\chi(p)\log p\,\log(X/p).$$

**Proposition to test:** There exists a real $X_0$ such that
$P(X)\le0$ for every real $X\ge X_0$ if and only if every
nontrivial zero of $L(s,\chi)$ has real part $1/2$. The sum
uses only genuine primes, natural logarithms, and the
unnormalized ramp, with no modulation. Neither side assumes
any rate, sampling, ordinate independence, or family average.

**Source and payoff:** Bob's [endpoint comparison, (1) and
its signed-pair use](../../bob/fixed-strip-endpoints.md#the-product-mean-at-the-original-endpoint-weight)
uses the prime ramp after division by the cutoff. Taking
$(d_i,d_j)=(1,-4)$ at an odd base conductor and $v=0$ gives
this fixed character. The [unsigned-edge Mellin argument](../../bob/unsigned-edge-rh.md#an-endpoint-lower-bound-and-its-mellin-obstruction)
at `5f22f5a60aef2da44527fee5b442065015202396` suggests the
one-sided transfer. This equivalence is operator-proposed,
not a premise or result of either landing. If it holds, an
independently proved eventual sign would locate the zeros
for this character alone. The prior reweighting cards are
not hypotheses here.

**Discriminating test:** In the sign-to-zero direction,
form the Mellin transform of the nonnegative tail of $-P$.
Price all higher powers on the open right half-plane of
interest, check real-axis analyticity and whether any zero
pole can cancel there, and test Landau and reflection. In
the reverse direction derive the smoothed prime-power
formula with multiplicities and control its lower-order
terms. Compute the leading square correction in the same
ramp normalization, and compare it to a certified absolute
bound on the entire critical-line residue sum. Test the
completed beta log derivative at $1$ and an elementary
bound on $L'/L(1,\chi)$, without sampling zeros. An
insufficient absolute bound would not refute the sign.
