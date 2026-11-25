# Gaussian integers: Two counts, one discrepancy

**Claim.** A second reading can make a signed expression easier to
understand without changing the complex variable. The ordinary integers
and Gaussian integers align their zeta coefficients by *ideal norm*,
the size of the quotient by an ideal. The factorization is
$\zeta_{\mathbb Q(i)}(s)=\zeta(s)L(s,\chi_4)$, where $\chi_4$ is $+1$ on
$1\bmod 4$, $-1$ on $3\bmod 4$, and zero on even integers.

**Small example.** Compare the Euler factors at $5$ and $3$. The prime
$5=(2+i)(2-i)$ gives two Gaussian prime ideals of norm $5$, versus one
ordinary prime ideal of norm $5$. The prime $3$ stays prime in
$\mathbb Z[i]$, but its Gaussian ideal has norm $9$, so the norm-$3$
column has no Gaussian prime and one ordinary prime. Splitting and
inertia explain the two signs; they are not labels attached by hand.

There are two different comparisons:

- **All ideals:** The coefficient of $n^{-s}$ in the Gaussian zeta
  function is $\sum_{d\mid n}\chi_4(d)$. It cannot be negative because it
  counts ideals. At $n=5$ the sum is $2$; at $n=3$ it is $0$.
- **Prime powers:** Taking negative logarithmic derivatives instead
  gives $\psi_{\mathbb Q(i)}(x)-\psi_{\mathbb Q}(x)=D(x)$, where
  $\psi_K$ counts prime-ideal powers of norm at most $x$, weighted by
  the log of the underlying prime ideal's norm, and
  $D(x)=\sum_{n\le x}\Lambda(n)\chi_4(n)$. At norm $9$, the Gaussian
  weight is $\log 9$ and the ordinary weight is $\log 3$, so the
  difference is $+\log 3$, not zero.

**What it does not show.** Nonnegativity of the all-ideal coefficients
says nothing directly about the sign or size of the prime-power
discrepancy. The identity permits comparing the two counts together;
it does not provide an estimate for their difference.

**Source.** The factorization follows prime by prime: $p\equiv1\bmod4$
splits, $p\equiv3\bmod4$ is inert, and $2$ ramifies. See also the
[Dedekind zeta function](https://en.wikipedia.org/wiki/Dedekind_zeta_function).
