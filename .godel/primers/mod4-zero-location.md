# Mod-4: What would locate the zeros?

**Claim.** Let $\chi_4$ be $+1$ on $1\bmod 4$, $-1$ on $3\bmod 4$, and
zero on even integers. Set $D(x)=\sum_{n\le x}\Lambda(n)\chi_4(n)$,
where $\Lambda(p^k)=\log p$ and other integers have weight zero. An
unconditional bound $D(x)=O_\varepsilon(x^{1/2+\varepsilon})$ for every
$\varepsilon>0$ would settle GRH for $L(s,\chi_4)$, not ordinary RH or
all of GRH. The constant can depend on $\varepsilon$.

**Why it would suffice.** For $\Re s>1$, partial summation identifies
$-L'(s,\chi_4)/L(s,\chi_4)$ with
$s\int_1^\infty D(t)t^{-s-1}\,dt$. The bound would make this integral
holomorphic in $\Re s>1/2$: On each compact subset, choose an
$\varepsilon$ smaller than its distance to the line. A zero there
would force a pole of the logarithmic derivative. The functional
equation then rules out nontrivial zeros left of the line as well.
This argument needs neither a trace nor an explicit sum over zeros.

**Small example.** In $D$, the prime $3$ and its square $9$ carry the
same base weight $\log 3$ with opposite signs. Every odd prime square
has positive sign. The raw prime-only difference and $D$ differ by
$O(\sqrt x)$: Chebyshev's bound controls the squares, and higher powers
cost $O(x^{1/3}\log x)$. Thus the same target for the raw prime-only
difference would also suffice. The *smoothed* prime-only sum is a
third reading: It weights each prime term by $\log(x/p)$. In the
smoothed prime-power sum, squares alone contribute
$(2+o(1))\sqrt x$ because the weight at a square is $\log(x/p^2)$.
A small smoothed total can therefore hide a large prime-only term.

**What it does not show.** This is a reduction, not a bound. A
conditional estimate derived from the zero-line hypothesis cannot
supply the independent arithmetic input. Neither a small total nor
a finite run of negative smoothed prime-only values settles the
asymptotic question.

**Source.** Mathlib's `DirichletCharacter.LSeries_twist_vonMangoldt_eq`
gives the Dirichlet-series identity on $\Re s>1$. The project proves
the smoothed square asymptotic in
[`PrimeSquareCorrection.lean`](../../Proofs/Examples/PrimeSquareCorrection.lean).
