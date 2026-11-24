# Fixed-mean negative slabs extend joint matching to gap $.663$

In the $(10,2)$ shallow comparison at depth $c=39/20$, for every real $s$
and $13/25\le d\le663/1000$, one fixed prime angular law admits a shallow
completion giving **both** zero second answers at $3t$ at shifts $s,s+d$.
The completion can depend on the pair. The law still matches every first
translate at the two heights, gives the required zero answers at orders two
through ten at $t$, and has failure mean $>8/9$. Together with the
[previous strip](gap-51-hull.md) and its predecessors this covers
$0\le d\le663/1000$. Hence a two-term scalar separator on this common-law
path must have like signs and $663/1000<d<4$. These are abstract laws, not
measurements at actual failures.

## The full slabwise moment interval

Start with the [half-gap mixture](half-gap-mixture.md) at
`d15c01a4fdc2f34b5a35fca5f3eee16a2a91c0ab`, before the one-block change.
Let $P(x)=4x^3-3x$, $A=\mathbb EX$ and $B=\mathbb EP(X)$ for $X\in[-1,1]$.
At fixed $A=a$, the exact possible range for $B$ on a slab is

$$
[\ell(a),u(a)],\qquad
\ell(a)=\begin{cases}-1&a\le1/2,\\P(a)&a>1/2,\end{cases}
\qquad u(a)=-\ell(-a).
$$

For $a\le1/2$ the lower endpoint is realized by the mean-$a$ law on
$\{-1,1/2\}$: $P=-1$ at both atoms and $P\ge-1$ everywhere. For $a\ge1/2$,
$P(x)-P(a)-P'(a)(x-a)=4(x-a)^2(x+2a)\ge0$ on $[-1,1]$, so the atom at $a$
minimizes. Reflection gives the upper endpoint. Mix the two endpoint laws
with upper-law weight $(B-\ell)/(u-\ell)$ (choose the lower law if $u=\ell$).
Both laws have mean $a$, so every interior value is attainable too. On the
fixed negative slabs these choices are independent **before** imposing the
nonlocal $B$ cap and shift tests.

A numerical fit varied all 184 negative slab moments over those intervals,
using sampled cap and direction-price constraints. The certified witness
instead uses the checker's integer displacements in millionths, added to
baseline $B$ and clipped to the exact intervals. It reconstructs each slab's
atomic law and independently recomputes its two moments over $\mathbb Q$;
128 of the moments are strictly interior. Leave the law unchanged at $z\ge0$
and to the left of the first knot. All of $A$ is identical, so the original
bound $\|G_A\|_\infty<.6186604<C_{10}$ still holds. Only the zero-weight
region of the failure integral $\int z_+e^{-z}\mathbb E\sqrt{(1+X)/2}\,dz$
was changed, preserving the surplus $>9.48\cdot10^{-8}$. The
[fixed-spline estimates](single-shift-10-2.md#matching-with-one-shift-at-a-time)
still give zero limiting higher prime answers: the cutoff at $-12$ is
unchanged, and the altered angular moments are bounded.

## Replay of the continuum tests

Run from the repository root with SageMath 10.9 and assertions enabled:

```sh
sage .godel/bob/check-negative-slab-strip.py
```

The checker pins and replays the baseline, then applies its 128-bit ball
routines to the new profile. The Taylor cap test uses 110 intervals on
$[0,64]$, conjugation for negative frequencies, and a jump bound for the tails.
It compares the jump formula against direct integration of the slabs and
certifies $\|G_B\|_\infty<1.19<C_1$. Thus the new $m=-G_B/C_1$ matches the
first answers at $3t$ and $v=1-|m|^2$ is positive.

For each $(s,d)$ the required inequality in every real direction $(a,b)$ is

$$\int |a+b e^{idx}|v\,d\mu\ \ge\ |aS(s)+bS(s+d)|,$$

where $S(s)=\Re\int e^{isx}m^2\,d\mu$. The inherited
[quadratic and chord estimates](half-gap-mixture.md#a-quadratic-allowance-for-unequal-positive-coefficients)
normalize nonzero directions by $|a|+|b|=1$ and check both signs, every
coefficient ratio, and singletons. They interpolate
the signed bounds at fixed coefficients, not the nonsmooth minimum over
directions. The replay covers $[-8-.663,8]\times[.52,.663]$ with 1,158
rectangles at normalized slack $>5\cdot10^{-6}$, including a uniform Fourier
tail $<1.051\cdot10^{-62}$. Outside this shift interval both centers have
magnitude $<.02$ by grid chords and exponential-polynomial tails; the uniform
capacity bounds $C(d)>.4$ and $V-R(d)>.04$ pay the outer costs. Compact convex
separation then supplies one second-moment completion per pair, not merely
a separate completion per direction. Neither the search nor any sampled
optimum is used in certification; $.663$ is not an upper bound on this route.
