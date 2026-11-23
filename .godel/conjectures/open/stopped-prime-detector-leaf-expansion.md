---
evidence_revision: 8fd18679a5334cd52b99a5171749867b108cb53d
---

# Does the public stopped expansion instantiate the finite detector?

## Proposition

Let $U>1$ be real, $S$ the finite set of primes with
$b_p>0$ in Alice's slice, $\chi$ a complex Dirichlet
character modulo a prime $q$, and $t$ real. Write
$z=\sum_{p\in S} b_p\chi(p)p^{it}$ and assume $z\ne0$.
For an ordered length-$k$ tuple in $S^k$, retain it iff
all proper prefix products are $<U$ and its full product
is $\ge U$. Define $d_{k,n}$ by summing $\prod_i b_{p_i}$
over these tuples with full product $n$, once per tuple.
For any natural $N$ with $U\le 2^N$, the public theorem
`finite_normalized_leaf_expansion` yields

$$1=\sum_{k=0}^N z^{-k}\sum_n d_{k,n}\chi(n)n^{it},$$

where the inner sum is over actual leaf products and
no leaf has length past $N$. Character zeros do not
remove leaves or change their coefficients.

## Source and payoff

Eve: `Proofs/Lemmas/StoppedPrimeProductMoment.lean`,
`finite_normalized_leaf_expansion`, at the evidence revision.
Alice: `145f6475d9f7c45884ea3843e66cb016d5e56fa3`,
`.godel/alice/stopped-conductor-window.md`,
“A length-stopped moment,” lines 17–21. The identity
supplies the finite nonzero-level detector; the hybrid
mean-value estimate is out of scope.

## Discriminating test

At the exact evidence revision, import the public Lean
module from a scratch client. Independently define ordered
leaves, product fibers, weights, and the Dirichlet phase;
apply the public theorem to the resulting symbolic identity
with finite cutoff. Check strict proper-prefix inequality,
inclusive endpoint, degree/product grouping, and that the
monoid phase works with zero character values. Independently
enumerate $S=\{2,3,5\}$, $U=12$, weights $(1,2,4)$,
quadratic character mod $7$, and $t=0$, comparing the leaf
coefficients at $12$ and $30$ and the exact normalized sum.
