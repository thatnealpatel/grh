---
evidence_revision: b6b5fe8ce1c7334f815ba2515ee02969b09b996e
outcome: established
---

# Test onset two for the discounted triangular sign

Use natural logarithms. Let $h=\mathbf1_{[0,\log 2]}*
\mathbf1_{[0,\log 2]}$, $d=\varphi(q)$, and
$\delta_q=1/(\sqrt2\,10^6\lceil\log(2q)\rceil)$ for integer
$q\ge2$. Set
$$H_q(X)=(1-\delta_q/d)X-\sum_{p\nmid q}(\log p)
(1-\delta_q\mathbf1_{p\equiv1\bmod q})h(\log(p/X)).$$

**Proposition:** For every integer $q\ge2$, assume GRH for
all primitive inducers of the characters modulo $q$,
including zeta. Then $H_q(X)\ge\sqrt X/25$ for every real
$X\ge2$, with no restriction linking $X$ and $q$. For each
fixed such $q$ and integer $B\ge1$, joint GRH for that
family is equivalent to $H_q(n^B)\ge0$ for every integer
$n\ge2$.

**Source and payoff:** The [explicit discounted sign](../closed/order-two-explicit-discounted-sign.md)
at the evidence revision gives the exact full $K$ and
$K_2$ formulas and establishes the same margin starting at
$2^{512}$. Its forward use for the sampled criterion is
the implication strengthened here. The [Landau converse](../closed/order-two-log-discount-sampled-sign.md)
is pinned at `69d5d30993da9b1de65d9d7930f06a86664cfa0b`.
Failure of the new margin would not invalidate either
landing, and failure of a sufficient estimate alone would
not refute the new margin or the sign criterion.

**Discriminating test:** Write $Y=\sqrt X$,
$H_{\rm all}=X-P_{\rm all}$, and
$Q_2(Y)=\sum_p(\log p)h(2\log(p/Y))$. Use the exact split
$H_q=H_{\rm all}+P_{\rm bad}-\delta_q(X/d-P_1)$.
Restore the favorable ordinary trivial residues in
$H_{\rm all}$ and check $H_{\rm all}\ge Q_2-wY$ with
$w=(3+2\sqrt2)D_0$, $D_0=2+\gamma_E-\log(4\pi)$.
For $Y\ge4096$, test against the $K_2$ mean $kY$,
$k=6-4\sqrt2$, charging $10D_0\sqrt Y$, $2/(Y-1)$,
and $(\log2)\theta(\sqrt{2Y})$. In an open interval of
multiplicative width two, each base contributes at most
one proper prime power; at width four, at most two.
Check $\theta(t)\le t\log4$ by induction using the even
and odd central binomial coefficients. For all $X\ge2$,
test the identity-class correction using $108Y\log(2q)$
for zeros, $10$ for trivials, $3\log q$ for omitted Euler
factors, and $2\log2\,\theta(2Y)$ for powers; charge
less than $0.0002Y$ after the discount. No enumeration in
$q$ is required. Recheck the grouped residues and the
same-series strip iteration in the pinned converse.

For $256\le Y\le4096$, test $Q_2(Y)/Y$ at spacing $1/8$,
with threshold $315/1000$. Extend from a nearest gridpoint
by continuity and $|Q_2'|\le2\theta(2Y)/Y<6$ on smooth
pieces. For $2\le X\le256^2$, test $H_{\rm all}(X)/Y$
at $X=2$ and $X=(j/128)^2$ with threshold $200/1000$.
Extend from the preceding gridpoint on the $Y$ scale:
$Y-Y_i\le1/128$, $X-X_i\le2Y/128$, and on smooth
pieces $|H_{\rm all}'(X)|\le1+\theta(4X)/X<7$.
Continuity permits summation across the finitely many
knots between any two gridpoints. These are two different
prime-sum certificates, not tests at integer $X$ alone.

## Reproduction code and error bound

Use Python 3 without `-O`. All comparisons and split
indices are integer or rational. Put $T=10^{16}$. Python
`Decimal.ln` is correctly rounded to nearest; at 44-digit
precision for the positive integer inputs below, the
absolute rounding error is at most $0.5\cdot10^{-42}$
(the logarithms are in $[0,18]$). Scaling by $T$ is an
exact decimal exponent shift. Truncating to integer then
has error less than two units relative to $T\log n$.
The scale logarithm `z` thus has error at most eight
units for $X=(j/128)^2$, two for $X=2$, and four for
$Y=j/8$. The scaled tent factor on either arm has error
at most 16 units, including when a true endpoint lies
exactly on the arm. The true scaled tent factor is at
most $T$, and the approximate prime log is less than
$19T$. Expanding the difference of a product bounds its
error by $(2+19\cdot16)T<400T$. Prefixes are exact sums
of the same integer logs and squares, so subtracting
prefixes adds no further rounding error. Charge $400T$
per selected prime, with opposite signs for a lower
bound on a prime sum and a lower bound on its deficit.
`per_mille` floors the resulting certified lower bound.
At $X=2$ use $3/2>\sqrt2$ for the denominator after
checking that the certified deficit is positive.

The rational check uses the four-term lower arctangent
sum at $1/5$ and one-term upper sum at $1/239$ in Machin's
identity. The function `f` is a positive partial sum for
$\log x$ at $x>1$, with $(x-1)/(x+1)$ as its argument.
Since the harmonic sum minus $\log4096$ exceeds
$\gamma_E$, `D` strictly upper bounds $D_0$. The bound
`log2_hi` sums two terms of the analogous log series and
uses a geometric majorant for the remaining terms.

```python
from bisect import bisect_right
from decimal import Decimal, localcontext
from fractions import Fraction as F
from functools import lru_cache
from math import isqrt

T = 10**16
N = 262144


def constants():
    p0 = F(314159, 100000)
    machin_lo = 16 * sum(F((-1)**j, (2*j+1)*5**(2*j+1))
                         for j in range(4)) - F(4, 239)
    assert p0 < machin_lo

    def f(x):
        u = (x-1)/(x+1)
        return 2*sum(u**(2*j+1)/(2*j+1) for j in range(10))

    D = 2 + sum(F(1, j) for j in range(1, 4097))
    D -= 15*f(F(2)) + f(p0/2)
    t, u, l = F(1414214, 10**6), F(1, 3), F(694, 1000)
    log2_hi = 2*(u + u**3/3 + u**5/(5*(1-u*u)))
    assert t*t > 2 and log2_hi < l
    assert 10*D < F(47, 100) and 2*t*l*l < F(137, 100)
    assert (3+2*t)*D < F(27066, 100000)
    assert 6-4*t > F(34314, 100000)
    assert 8*l*l < 4 and 1+8*l < 7 and 8*l < 6
    assert F(7248, 100000)-F(184, 6400)-F(2, 4096*4095) \
        - F(2, 10000) > F(1, 25)
    assert F(315, 1000)-(F(315, 1000)+6)/(16*256) \
        > F(312, 1000)
    assert F(312, 1000)-F(27066, 100000)-F(2, 10000) \
        > F(1, 25)
    assert F(200, 1000)*F(127, 128)-F(7, 64) \
        - F(2, 10000) > F(1, 25)


@lru_cache(None)
def L(n):
    with localcontext() as c:
        c.prec = 44
        return int(Decimal(n).ln().scaleb(16))


def sieve():
    s = bytearray(b'\x01')*(N+1)
    s[:2] = b'\x00\x00'
    for p in range(2, isqrt(N)+1):
        if s[p]:
            s[p*p:N+1:p] = bytes((N-p*p)//p+1)
    return [p for p in range(2, N+1) if s[p]]


constants()
P = sieve()
S1, S2 = [0], [0]
for p in P:
    v = L(p)
    S1.append(S1[-1]+v)
    S2.append(S2[-1]+v*v)


def weighted(lo, mid, hi, z, m):
    a, b, c = [bisect_right(P, n) for n in (lo, mid, hi)]
    up = m*(S2[b]-S2[a]-z*(S1[b]-S1[a]))
    down = (2*L(2)+m*z)*(S1[c]-S1[b])-m*(S2[c]-S2[b])
    return up+down, 400*T*(c-a)


def per_mille(num, den, y_num, y_den):
    return (1000*num*y_den)//(den*y_num)


def small(num, den, z, y_num, y_den):
    s, e = weighted(num//den, 2*num//den, 4*num//den, z, 1)
    b = num*T*T-den*(s+e)
    assert b > 0
    return per_mille(b, den*T*T, y_num, y_den)


def middle(j):
    s, e = weighted(j//8, isqrt(2*j*j)//8, j//4, L(j)-L(8), 2)
    return per_mille(s-e, T*T, j, 8)


j0 = isqrt(2*128**2)+1
A = [(small(2, 1, L(2), 3, 2), 0)]
A.extend((small(j*j, 128**2, 2*(L(j)-L(128)), j, 128), j)
         for j in range(j0, 256*128+1))
B = [(middle(j), j) for j in range(8*256, 8*4096+1)]
print('primes', len(P), bisect_right(P, 8192))
print('small', len(A), min(A), 'endpoint', A[0])
print('middle', len(B), min(B))
assert min(A)[0] >= 200 and min(B)[0] >= 315
```

## Adjudication

**Two suffices.** In fact the lower bound is strict. This is a
strengthening of the forward use at lines 175–181 of the evidence
revision, not a correction to its result for $X\ge2^{512}$.

**Full sums and signs.** At lines 53–93 the full Mangoldt sum for
scale $U\ge2$ and transform $F$ is the pole term minus both zero
sums. In $X-P_{\rm all}$ this leaves a *positive* trivial sum
$\sum_{j\ge1}X^{-2j}K(-2j)$; each summand is nonnegative. Adding
back the proper powers costs nothing in this lower bound and gives
at least the exact square sum $Q_2(Y)$. On RH the nontrivial sum
is bounded in modulus by $wY$ (Landau pin, lines 121–130). Thus
$$H_{\rm all}(X)\ge Q_2(Y)-wY.$$
At scale $Y\ge4096$, apply the full formula instead to $h(2v)$.
Its pole is $kY$, and $|K_2(\rho)||\rho|^2\le
2(2^{1/4}+1)^2<10$. Here the trivial sum is subtracted; its size
is at most $2\sum_{j\ge1}Y^{-j}/j^2\le 2/(Y-1)$. Removing proper
powers to get $Q_2$ costs at most $(\log2)\theta(\sqrt{2Y})$:
Two powers of one base have ratio at least two and cannot both be
in $(Y,2Y)$, while either endpoint has weight zero.

For $\theta(t)\le t\log4$, induct on integers $n$, starting at
zero and one. At $n=2m$ bound $\theta(n)-\theta(m)$ by the log
of the central binomial coefficient. At $n=2m+1$ bound
$\theta(n)-\theta(m+1)$ by $\log\binom{2m+1}{m}$. In each case the
primes in the difference divide the coefficient, and the coefficient
is at most $2^{2m}$ (two equal maxima in the odd row). The inductive
bounds give $n\log4$ in both cases; taking floors handles real $t$.

**All moduli.** Set $\ell=\log(2q)>1$. The primitive conductor
bound at evidence lines 130–142 charges each full nontrivial sum
at most $108Y\ell$: On GRH the reciprocal-square zero mass for a
nonprincipal inducer is less than $3(\log r+5)$, $r\le q$, and
$|K(\rho)||\rho|^2<6$. Zeta is covered by $D_0$. The full trivial
sum costs less than 10. Restricting to bases coprime to $q$ costs
at most $\sum_{p\mid q}(\log p+\log4)\le3\log q$ by counting
exponents in $[X,4X]$ and using $h<1$. Averaging with weight $1/d$
keeps these budgets unchanged, gives pole $X/d$, and selects powers
congruent to one. To get $P_1$, remove proper powers: Each base
is at most $2Y$ and has at most two powers in $(X,4X)$, since the
third has ratio at least four to the first. Their total cost is at
most $2\log2\,\theta(2Y)\le8(\log2)^2Y<4Y$. Hence
$$|X/d-P_1|\le108Y\ell+10+3\log q+4Y<200Y\ell.$$
The exact split and $\lceil\ell\rceil\ge\ell$ give
$H_q(X)>H_{\rm all}(X)-0.0002Y$ even when $q>X$.

**Three real intervals.** The rational inequalities in `constants`
now give, for $Y\ge4096$,
$$H_q(X)/Y>0.07248-1.84/64-2/(4096\cdot4095)-0.0002>1/25.$$
Here $1.84$ pays for $10D_0+\sqrt2\log2\log4$, both terms having
relative loss proportional to $1/\sqrt Y$.

For the other intervals I checked the two grid sums against the
arms $m(\log p-\log U)$ and $2\log2-m(\log p-\log U)$, with
$(m,U)=(1,X)$ or $(2,Y)$. In the latter case the last rising-arm
prime satisfies $64p^2\le2j^2$; `isqrt(2*j*j)//8` is the exact
integer cutoff. The sign of the $400T$ allowance is adverse in both
calculations. I reran the block above with assertions enabled in
Python 3.12.3 (SHA-256 of the block including its final newline:
`6a122fbeca542c2586e27f9180bdd1ccdd5d13874d21ef70020a1a845b4cb575`).
The sieve gave 23,000 primes through 262,144 and 1,028 through 8,192.

* For $2\le X\le256^2$, the minimum of the 32,588 floored lower
  bounds in units of $Y/1000$ was 306 at $j=2219$; the endpoint
  $X=2$ gave 358. Use only $H_{\rm all}(X_i)\ge0.20Y_i$. On smooth
  pieces $|H_{\rm all}'|\le1+\theta(4X)/X<7$. Continuity at all
  knots makes this a Lipschitz bound on the interval. The preceding
  node (including the initial endpoint) has $Y_i/Y\ge127/128$ and
  $X-X_i\le2Y/128$. After the discount the ratio is greater than
  $0.20(127/128)-7/64-0.0002>1/25$.
* For $256\le Y\le4096$, the minimum of the 30,721 floored lower
  bounds for $1000Q_2(Y_i)/Y_i$ was 331 at $j=2048$. Use only
  $Q_2(Y_i)\ge0.315Y_i$. Here $|Q_2'|\le2\theta(2Y)/Y<6$ off the
  knots, again with continuity. The nearest node has distance at
  most $1/16$, so $Q_2(Y)/Y\ge0.315-(6+0.315)/(16\cdot256)>0.312$.
  After the zero budget and discount, $0.312-0.27066-0.0002>1/25$.

**Samples.** Fix $q$ and integer $B\ge1$. The forward implication
now covers every $n\ge2$. Conversely, such signs give an eventual
nonnegative tail. At the Landau pin, lines 153–206 apply to the
same $H_q$ without GRH: The grouped coefficient is
$K(z)(m_\zeta(z)-\delta_q S(z)/d)$, never zero by irrationality
and $K(z)\ne0$ in the strip. Any real zero above $1/2$ has negative
coefficient since zeta has none there. The $O_q(\sqrt X)$ remainder
needs no GRH for removing proper powers, by the width-four count.
If $\Re z\le a$ for all zeros, the sub-first coefficient moments
justify the cell subtraction for the sample series in
$\Re s>b=\max(1/2,a-1/B)$, with these coefficients as residues.
The nonnegative tail cannot have real convergence abscissa above
$b$: A regular point there contradicts Landau, and a pole with
negative residue contradicts nonnegativity from the right. Thus
convergence excludes all poles in the strip. Iterating from $a=1$
with the same series gives $\Re z\le1/2$, and family reflection
gives joint GRH. Dropping $n=1$ changes only an entire term. The
finite grids certify two ordinary-prime inequalities, not GRH or
the infinitely many sampled signs.
