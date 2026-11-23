# Forty harmonics are necessary at the half-budget for $A=1.57$

At $A=157/100$, put $T=(2/\pi+1/A)/2$, half the available angular error above $2/\pi$. The first 40 harmonics suffice by the [consecutive majorant](initial-harmonic-budget.md). **Every choice of at most 39 positive integer frequencies fails:** There is a circle probability law whose complex moments vanish at all the chosen frequencies, but whose integral of $f(s)=|\sin(s/2)|$ is strictly above $T$. Here $s=2v-\pi$, so these are the same angular queries as in [Alice's sparse lower bound](../alice/sparse-harmonic-budget.md). There is no upper cutoff on the indices.

Fix the queried set $J$. If $k\le31$ is missing, use Alice's density $1-\cos(ks)$ against normalized uniform measure in this coordinate. It kills all the queries and integrates $f$ to $2/\pi+2/[\pi(4k^2-1)]>T$, as can already be checked at $k=31$. Otherwise let $M=\{32,\ldots,40\}\setminus J$ have size $m\ge1$. There are at most $m-1\le8$ queried indices above 40.

For each $n\in M$ start with the uniform law on $s_l=(2l+1)\pi/n$, $0\le l<n$. It kills all frequencies not divisible by $n$ and has $f$-mean $C_n=1/[n\sin(\pi/(2n))]$ by the geometric sum. For every $j\in D_n=\{j\in J:n\mid j\}$ add an independent symmetric shift $\pm\pi/(2j)$. Convolution preserves every zero moment, and its $j$th factor kills frequency $j$. If $\delta$ is the sum of these shifts, bound the absolute sine on the shifted grid from below by the signed sine on its real lift. Since $\delta$ is symmetric, its sine term averages to zero, giving

$$ \int f\ \ge\ C_n\,\mathbb E\cos(\delta/2)=C_n\prod_{j\in D_n}\cos(\pi/(4j)). $$

If this law fails to exceed $T$, then $d_n=1-T/C_n$ satisfies

$$ 0<d_n\le 1-\prod_{j\in D_n}\cos(\pi/(4j))\le\frac{\pi^2}{32}\sum_{j\in D_n}j^{-2}. $$

Here $1-\prod a_j\le\sum(1-a_j)$ for factors in $[0,1]$ and $1-\cos x\le x^2/2$. Every member of $D_n$ exceeds 40 since $n$ is missing and $2n>40$. In particular some member must satisfy $j\le\pi/(2\sqrt{d_n})$ by the bound of eight on their number. The following strict upper bounds $H_n$ on that threshold are smaller than $\operatorname{lcm}(n,n')$ for every $n<n'\le40$.

| $n$ | 32 | 33 | 34 | 35 | 36 | 37 | 38 | 39 | 40 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| $H_n$ | 140 | 150 | 160 | 180 | 200 | 240 | 290 | 390 | 850 |
| Least lcm with a later index | 160 | 396 | 612 | 280 | 360 | 1406 | 760 | 1560 | None |

Consequently if every shifted grid failed, the $m$ missing indices would require $m$ distinct queried multiples above 40, an impossibility. Conversely the degree-40 Hermite majorant integrates to $C_{41}<T$ on **every** law with its first 40 moments zero. This proves sharpness of the count, not uniqueness of the optimal set. For a deterministic adaptive test with at most 39 queries use its path of zero answers on uniform measure: The witness returns the same answers, though uniform measure lies below $T$. These are tests on circle laws, not constructions of primes or lower bounds for arguments using other arithmetic information.

**Certificate.** For $b(t)=1/2+25t/157$ and $z=\pi/(2n)$, $T/C_n=b(\pi)\sin(z)/z$. The rational checks below use Machin's formula and the alternating arctangent and sine series.

```python
from fractions import Fraction as Q
from math import lcm

L, U = Q('3.1415926535'), Q('3.1415926536')
def S(b, m):
    return sum(Q((-1)**k, (2*k+1)*b**(2*k+1)) for k in range(m))
assert L < 16*S(5,8)-4*S(239,9) < 16*S(5,9)-4*S(239,8) < U
assert U < Q(157,50)*(1 + Q(2,4*31**2-1))
def b(t):
    return Q(1,2) + 25*t/157
for n,h in enumerate([140,150,160,180,200,240,290,390,850],32):
    d = 1 - b(U)*(1 - (L/(2*n))**2/6 + (U/(2*n))**4/120)
    assert 4*h*h*d > U*U
    assert all(lcm(n,r) > h for r in range(n+1,41))
assert b(L)*(1 - (U/82)**2/6) > 1
```
