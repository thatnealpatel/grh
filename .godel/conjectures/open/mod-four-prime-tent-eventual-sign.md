---
evidence_revision: dca062832345d6f827769b6a1af9b923d21e3b0e
---

# Eventual signs of the local mod-four prime tent

Let $\chi_4$ be the primitive real character modulo $4$.
For real $X\ge1$ use only genuine primes and natural logs:

$$P(X)=\sum_{p<X}\chi_4(p)\log p\,\log(X/p),\qquad
W(X)=P(16X)-2P(4X)+P(X).$$

**Proposition to test:** There exists a real $X_0\ge1$
such that $W(X)\le0$ for every real $X\ge X_0$ if and
only if every nontrivial zero of $L(s,\chi_4)$ has real
part $1/2$. No sign of $P$, rate, sampled signs, or
independence of zero ordinates is assumed.

**Source and payoff:** This operator conjecture changes
the weight in the [all-cutoff prime ramp criterion](../closed/mod-four-prime-ramp-eventual-sign.md)
at the evidence revision and the [polynomial-grid criterion](../closed/mod-four-prime-ramp-polynomial-grid-sign.md)
at `e96c4611fa01385ff9c6345f1dc4ab27ec8425f8`. The
original ramp is Bob's [equation (1)](../../bob/fixed-strip-endpoints.md#the-product-mean-at-the-original-endpoint-weight)
at `bbca37033019090f6f40e6223b5054d382c9d789`, with
$(d_i,d_j)=(1,-4)$ and $v=0$, before cutoff normalization.
Neither source asserts this local criterion. It would
identify a weighted comparison of actual residue-class
prime counts in one multiplicative interval that would
imply zero location if proved unconditionally.

**Discriminating test:** Compute the exact supported
weight, its center, and its signs prime by prime. Apply
the same rescalings to the prime-power explicit formula,
preserving multiplicities and the square coefficient and
comparing the square main term with the absolute residue
cost on the zero-line hypothesis. Test whether
$C=\sum_\rho |\rho|^{-2}<2/9$ follows from elementary
rational enclosures at $1$ for the completed beta log
derivative, using the alternating derivative and certified
log series tails rather than sampled zeros. For the other
direction transform the nonnegative tail of $-W$, track
all finite-endpoint terms, and check real regularity and
noncancellation by the kernel before applying Landau and
reflection. A failed absolute budget alone would not
refute the criterion. No single-tiling claim is tested.
