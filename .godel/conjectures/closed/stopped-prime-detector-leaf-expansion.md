---
evidence_revision: 8fd18679a5334cd52b99a5171749867b108cb53d
outcome: established
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

## Adjudication

The public identity specializes to the stated detector. A scratch
Lean 4.36.0 client imported the module rebuilt from the evidence
revision, with only pinned dependencies on the import path. It
represented $S^k$ by functions from `Fin k` to the subtype $S$,
then took their coordinatewise image in natural-valued functions.
This map forgets membership proofs, not order: Two preimages of a
word agree at every position. The client tested the full product
against $U$ inclusively and every proper prefix strictly, using
factors of one outside the prefix. `Finset.prod_filter` and
pointwise membership give equality with `stoppedTuples`. Taking the
product image and summing weights on each product fiber then give
`stoppedProducts` and `coefficient` by definition, once per word.

For $a(n)=\chi(n)n^{it}$, `map_one` holds, and `map_mul` follows
from character multiplicativity and `Complex.mul_cpow_ofReal_nonneg`
on natural casts. This is a monoid map into complex numbers, not
into their units. At a nonunit residue, `MulChar.map_nonunit` gives
$a(n)=0$ without changing the leaf set or its weights. Substituting
this map into `finite_normalized_leaf_expansion` at nonzero $z$ and
rewriting the inverse power proved the independently stated identity.
If $k>N$, the length-$N$ prefix has product at least $2^N\ge U$,
contrary to the proper-prefix test. Thus degree $N$ is included even
at $U=2^N$. The client also applied `stopped_length_le` to its own
leaves. The identity, cutoff, and nonunit checks used no `sorryAx`.

As a diagnostic, recursive first crossing and exhaustive ordered
words through degree four gave the same leaves: 3, 17, and 3 at
degrees 2, 3, and 4. At 12 all three orders of $(2,2,3)$ qualify,
giving $d_{3,12}=6$. At 30 the orders starting with $(3,5)$ or
$(5,3)$ stop early; the other four give $d_{3,30}=32$. With the
specified character, $z=-5$ and $(P_0,\ldots,P_4)=(0,0,32,34,-5)$,
so the exact normalized sum is $32/25-34/125-1/125=1$. The proof
is the symbolic specialization, not this fixture. It supplies the
identity for Alice's degree-wise triangle inequality at line 21;
it does not establish a hybrid estimate.
