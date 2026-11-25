# Delete-33: Both first caps admit high mass and a flat-B splice

At depth $39/20$, dropping only the inherited quadratic
condition $Q(V_B)\le d$ leaves a high-mass law for **every**
mask in the [80-mask signed frontier](eight-knot-local-q-33.md).
In fact each such law obeys both first caps on the entire
real frequency line, not just the 581 and 62 sampled disks,
and has $M-8/9>0.000212$. On the slab $[-216,-214]/400$
the weighted mean of $A$ exceeds $1/4$, its signed drop is
$3/2$, and $B$ is identically $1$. The same construction
has $Q(V_B)-d>0.49$: It is not a law for the parent test.
Thus a mass-dependent cap on the drop below $3/2$, or on
this local mean below $1/4$, cannot follow from the first
caps, the partition, and the high mass alone. Improving the
frequency sampling in either first cap cannot fix this.

## One anchor for all masks

Use the common-atom convention $X=2u^2-1$, $T_3(X)=4X^3-3X$,
and $(A,B,U)=\mathbb E(X,T_3(X),u)$. Write $a$ for the
$A$ column of the [1,257-knot reference](deletion-laws/delete-33-tail-baseline.txt),
scaled by $9999/10000$. Set $A=a$ off the two adjacent
slabs starting at $-218/400$ and $-216/400$. On the first
set $A=a(-218/400)+a(-216/400)-1/4$. On the second put
$A=1$ then $-1/2$, split at $-215/400$. The two original
slabs have equal length, so the two-slab unweighted integral
of the scaled reference is unchanged. The weighted mean
uses $e^{-z/2}\,dz$ and is about $0.25046875$.

On every slab and on the constant infinite last piece,
take the deterministic atom $u=\sqrt{(1+A)/2}$. This
sets $B=T_3(A)$, rather than reusing the reference $B$.
Both fields vanish left of $-144/25$. The checker verifies
$A\in[-1,1]$ and computes $M$ with the exact slab weights
from $(1+z_+)e^{-z_+}$. The anchor has
$M-8/9>0.0002837$. The inherited Taylor-box cap checker
proves $\|V_A\|_\infty<0.99999$ and
$\|V_B\|_\infty<0.999$, including both unbounded frequency
tails. The unmodified lattice kernel computation, with the
quadratic direction of the eight-knot certificate, gives
$Q(V_B)-d=0.491671171969428\ldots$.

## Turn all required extra knots into genuine splits

Every surviving mask spends eight knots, with exactly one
on $[-216,-214]/400$. More generally the argument permits
any seven other interior knots on finite original slabs,
at any positions distinct within each slab. Keep the anchor
on the distinguished slab. On an original slab with $n$
extra knots, take the same atom formula on its ordered
subpieces with $A_j=A_{\rm anchor}-j\varepsilon/7$ for
$j=0,\dots,n$, where $\varepsilon=10^{-8}$. The rational
anchor values on all these slabs are at least $\varepsilon$
from both endpoints of $[-1,1]$. Each extra knot is a
change of atom (and of $A$); the tail stays constant.

The construction changes $A$ pointwise by at most
$\varepsilon$ and $B$ by at most $9\varepsilon$, because
$|T_3'|\le9$. With $z_0=-144/25$, the normalized Fourier
field formula in the [local quadratic certificate](eight-knot-local-q-33.md)
then bounds the changes uniformly by
$$
e_A=2e^{-z_0/2}\varepsilon/C_t<10^{-6},\qquad
e_B=18e^{-z_0/2}\varepsilon/C<3\cdot10^{-6}.
$$
The factor $\bar w/w$ has modulus one. Both full caps
therefore survive. The atom inequality
$|\sqrt{s}-\sqrt{t}|\le\sqrt{|s-t|}$ costs at most
$\sqrt{\varepsilon/2}<0.000071$ in $M$, since the mass
weight integrates to one. The special drop, mean, and
flat $B$ are unchanged.

Finally $d\mu=dx/(2\pi|1/2+ix|^2)$ has total mass one.
For the anchor's $B$ field $V$ and perturbation $W$,
$|V|<1$ and $|W|\le e_B$ imply
$$
|Q(V+W)-Q(V)|\le (2e_B+e_B^2)
\left(\sum_m|q_m|+\sum_s|\lambda_s|\right)<0.001.
$$
The absolute coefficient sum bounds $|q|+|H|$ everywhere.
This computation does not use a triangle inequality for
squared seminorms. It also applies to knot positions off
the lattice: Only the anchor evaluation needs the lattice
kernel. Thus the entire witnessed family violates the
quadratic test by more than $0.49$.

## Replay and proof decision

From the repository root, with assertions enabled:

```sh
PYTHONDONTWRITEBYTECODE=1 /opt/sage-10.9/bin/python .godel/bob/check-eight-knots-first-caps-33.py
```

The checker uses exact rationals and 128-bit balls. It
checks the anchor and the uniform perturbation estimates,
not a finite sample of possible knot placements. No mask
export or numerical optimizer is required.

Keep the joint $(A,B,U)$ law and a genuinely $Q$-sensitive
constraint in the next exclusion attempt. The high-mass
witness here and the lower-mass fixed-field laws in the
[fiber result](tail-fiber-deletion-33.md) do not interpolate
into a certified feasible endpoint. Preserving the two
reference fields and reoptimizing the atoms is already
priced below the mass target there.
