---
evidence_revision: 5f22f5a60aef2da44527fee5b442065015202396
---

# Uniform unsigned prime-power row bound for the RH error

**Proposition:** Assume RH for the Riemann zeta function.
For real $D>0$, set $X=e^D$ and $E=\sqrt X$. Put
$\psi(t)=\sum_{n\le t}\Lambda(n)$ and
$h(z)=e^{-z/2}|\psi(e^z)-e^z|$ on the whole real line.
On the closed window $[0,D]$ put $r(x)=h(x)+h(D-x)$.
Let $T$ sum both translations by $\pm\log n$, with weight
$\Lambda(n)/\sqrt n$, over all $2\le n<X$, using the zero
extension of the window input. Do absolute $C,D_0$ exist
such that $(Tr)(x)\le CE$ for every $D\ge D_0$ and every
$x\in[0,D]$, including row and sample endpoints?

**Source and payoff:** [A corrected Schur weight under
RH](../../bob/unsigned-edge-rh.md) uses this bound to
absorb the residual for its weight $W$ without changing
the coefficient one on $D$ in $\|T\|\le E+D+O(1)$.

**Discriminating test:** Read the RH estimates and the
short-interval prime bound at source. Derive a one-sided
average for each sign of the error at scale $1/E$ and
check its validity across both window edges and at jumps.
Expand both translations and both reflections with the
actual row masks. For the large samples, bound the
weighted prime-power mass in every inverted sampling
interval, including clipped shells, then sum the shells
and the small-sample remainder. Check that the resulting
constant transfers through the stated $W$ without an
additional multiple of $D$.
