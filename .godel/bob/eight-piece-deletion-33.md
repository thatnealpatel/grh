# Delete-33: Release any four finite slabs

At $c=39/20$, keep $X=0$ left of $-144/25$, both unfolded
first caps, and simultaneous second replies at $(-7,6,19)/25$.
Use the [1,257-knot baseline](deletion-laws/delete-33-tail-baseline.txt).
On each retained finite slab one may choose **any** constant
probability law independently, not necessarily the reference law.
The law from $29/5$ onward is arbitrary measurable. Then:

* Dividing each of the first three nonnegative slabs into eight
  equal pieces gives $M-8/9<-4.60062\cdot10^{-8}$.
* Allowing arbitrary measurable laws throughout $[0,3/200)$ still
  gives $M-8/9<-4.13718\cdot10^{-8}$.
* Allowing arbitrary measurable laws on **any four** original
  finite slabs gives $M-8/9<-3.83838\cdot10^{-9}$.
* Allowing arbitrary measurable laws on **all negative** original
  finite slabs gives $M-8/9<-4.68429\cdot10^{-8}$. In this case
  the nonnegative finite slabs still have arbitrary constant
  laws, not fixed reference values.

Here $X=2u^2-1$, $T(X)=4X^3-3X$, $(A,B,U)=\mathbb E(X,T(X),u)$
for $u\in[0,1]$, and $M=\int_0^\infty te^{-t}U(t)\,dt$.
No regional condition is required. These are profile-class
exclusions, not an all-real exclusion.

## Certificate and replay

Use the [moved tangent inequality](three-midpoints-deletion-33.md#the-center-is-not-a-law)
with the [new cut and center table](deletion-laws/delete-33-eight-piece.json):
577 first cuts on $A$, 426 on $B$, one second cut, and 419 signed
raw $B$ jump corrections at original knots. The center $Z$ need
not be a law. Ambient positivity of $Q$ gives the linear upper
price with constant $-8/9+\sum_{\rm first}w_i+\sigma(d+Q(Z))$.
The finite cell score is maximized over all atoms using the
integrated primitive coefficients, with no restrictions on jumps
of competitor moments. Neither the search's tail discretization
nor its floating-point Gram factorization is used in replay.

The checker encloses the following terms in Sage balls (rounded
here):

| Term | Value |
|:--|--:|
| Constant plus finite atom supports | $-0.0147915284560820353989$ |
| Pointwise tail controls through $48$ | $0.0147914820310787765200$ |
| Tail interpolation allowance | $8.374041\cdot10^{-11}$ |
| Remote allowance | $3.349721\cdot10^{-10}$ |
| Sum on the eight-piece mesh | $-4.6006290764\cdot10^{-8}$ |

To price any set of measurable releases, start from the unsplit
mesh, whose price $P$ is about $-1.9200840981\cdot10^{-7}$.
For each original slab $i$, compute an upper increment $D_i$ by
subtracting its unsplit atom bound from a pointwise atom integral
bound. Clamp the increment at zero and round upward. On
$1/1600$ cells the integral bound comes from interpolating the
score of each fixed atom at both endpoints and the midpoint.
Each Bernstein control admits its own atom maximum. Charge
also the uniform integrated third-derivative remainder,
including the mass term, as on the tail. No law is differentiated.

For a release set $S$ the upper price is $P+\sum_{i\in S}D_i$.
Thus the sum of the four largest increments prices every set of
at most four slabs, without assuming where the release lands.
The four largest are at starts $0,1/200,1/100,3/200$; in units
of $10^{-9}$ they are about $56.9077,50.2166,43.5123,37.5334$.
For all negative slabs the added allowance is about
$145.1654\cdot10^{-9}$. This last test strengthens the earlier
[measurable-negative result](measurable-negative-deletion-33.md),
which froze the nonnegative finite slabs to the reference.

The same sum with five releases has positive upper price,
$2.86494\cdot10^{-8}$, attained as a **price bound** by the first
five nonnegative slabs. Releasing every finite slab has positive
upper price $5.18163\cdot10^{-7}$. Neither sign produces a
feasible law. For a five-release extension, fit on the current
worst five slabs first, then reprice the best five over the whole
mesh with the new certificate; the maximizing set can change.

Run from the repository root with SageMath 10.9 and assertions enabled:

```sh
/opt/sage-10.9/bin/python .godel/bob/check-three-midpoints-33.py --certificate eight-piece
```
