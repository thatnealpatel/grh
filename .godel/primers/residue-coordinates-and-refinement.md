# Residue buckets: New coordinates or more information?

**Claim.** Changing coordinates can expose a relation without adding
information. Finer data can instead preserve a distinction that the
coarser data discarded. Neither move guarantees an estimate.

**Small example: Change coordinates.** Put five tokens at residue $1$
and two at residue $3$ modulo $4$. Multiplying each residue by $3$
swaps the buckets:

| Reading | Before | After |
|---|---:|---:|
| Bucket counts $(A,B)$ | $(5,2)$ | $(2,5)$ |
| Total and difference $(A+B,A-B)$ | $(7,3)$ | $(7,-3)$ |

The second reading is reversible. It makes the swap act independently
on two coordinates: Keep the total and negate the difference. The
swap's trace, the sum of its matrix's diagonal entries, is $0+0$ in
bucket coordinates and $1+(-1)$ in the new coordinates. What canceled
was the operator's diagonal sum, not the imbalance of the tokens.

**Small example: Keep finer data.** Multiplication by $3$ and by $7$
induces the *same* swap on odd residues modulo $4$. No change of
coordinates on those buckets can distinguish the operations. Modulo
$8$, a token starting at $1$ lands in $3$ or $7$, respectively. The
extra residue bit preserves a distinction lost under reduction.

**What it does not show.** Splitting a bucket does not constrain how
its weight is allocated. Even equal limiting shares need not mean a
small absolute gap: For large $x$, weights $x/2\pm x^{0.8}$ have equal
limiting shares and a gap $2x^{0.8}$. These are toy weights, not a
claim about primes.

**Source.** The sum and difference are the two unnormalized Fourier
coefficients on the multiplicative group of odd residues modulo $4$.
The table gives the entire calculation.
