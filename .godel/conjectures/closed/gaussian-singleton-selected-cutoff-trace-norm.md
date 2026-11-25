---
evidence_revision: 7f7e24f7e1dc4cddb20aab6d4343b8b1f460ca82
outcome: established
---

# Do selected Gaussian singleton cutoffs converge rapidly in trace norm?

Use the exact weight-four Gaussian block of the
[corrected singleton kernel card](../open/gaussian-singleton-corrected-kernel-series.md):
$G=C_{\mathbb Q(i)}$, $a=1/2$, $I=\{0\}$, $s=4$,
$w=(1+\log^2|\cdot|_F)^2$, and $\varphi=b_0\eta$ with its
fixed prescribed positive-log bump. Write $A=A(\varphi)$,
$P=P_a^{\mathrm{spec}}$, and $Z(t)=L(1/2+it,\bar\eta)$ for
the completed function. Here $\mu$ is quotient Haar.

**Claim:** There is one sequence $R_j\in[j+1/4,j+3/4]$ for
all sufficiently large integers $j$ such that the truncation
$T_{R_j}$ of the full quotient biorthogonal coordinate sum
for $PA$ to all $|t|\le R_j$ and all their allowed jets has
$\|PA-T_{R_j}\|_{\mathcal S_1}=O_A(j^{-A})$ for every
$A>0$. The associated corrected output-first Haar kernels
then converge in $L^2(w(x)w(y)^{-1}\,d\mu(x)d\mu(y))$.
These are the original coordinate sums at the selected
heights, not orthogonal compressions or new observables.

**Source and payoff:** The antecedent card uses the
single-character rectangles of (10.4.3.14), PDF pp. 466–467,
and the coordinate density of (10.4.3.21), p. 469. Proving
this would identify the actual kernel along selected cutoffs
in a stronger operator topology, not settle all prefixes or
supply any diagonal trace or global limit-order equivalence.

**Discriminating test:** In the positive log Fourier $H^2$
quotient, verify the full biorthogonal family and coordinate
normalization by the [capped jet totality](../../obligations/trace-theta-totality-qi.md)
and local interpolation at the actual zeros. Use the
[inherited zero count](../../obligations/trace-spectral-singleton-qi.md)
to seek a polynomial-width interval free of absolute zero
heights in every stated window. Test whether cutoffs flat at
every zero give exactly the original smoothed coordinate sum,
including both components at a double jet. Bound each
successive multiplier difference in $H^2$ through derivative
order two, and its quotient rank by the capped annular jet
count. Test summability with rapid tail and identification of
the limit with $PA$; verify the lift and
[Haar normalization](../../obligations/trace-spectral-singleton-kernel-qi.md).
Use a close pair or a double jet as a control for a split or
nonflat cutoff, not as a counterexample on the actual data.

## Proof

On the surviving left-action $\bar\eta|_{G^1}$ block, let
$c=\mu_1(G^1)$ and $X=H^2(\mathbb R)/D$ in the transported
$(1,2,1)$ squared derivative norm. By capped jet totality,
$D$ is exactly the common kernel of the coordinates
$\ell_{t,k}([u])=c\,i^{-k}u^{(k)}(t)$ for $Z(t)=0$ and
$0\le k<n_t=\min(\operatorname{ord}_t Z,2)$. The bilinear
Haar pairing cancels the angular factors, and differentiating
$e^{itx}$ gives the stated normalization, without a twist.
For each $(t,k)$ take the class of
$i^k(v-t)^k\rho_t(v)/(c\,k!)$, with $\rho_t$ smooth, compactly
supported away from all other zeros, and one near $t$. Such
neighborhoods exist since the zeros are locally finite. The
class has one unit coordinate and all other coordinates zero;
uniqueness in $X$ gives the full biorthogonal vector $\psi_{t,k}$.
No uniform norm estimate on these vectors is needed.

By the [angular factorization](../../obligations/trace-spectral-angular-qi.md)
$PA=S\bar A Q$ on this block and vanishes off it, where $Q=S^*$
and $S$ is the orthogonal lift. The quotient convolution is
multiplication by $m(t)=c\int b_0(x)e^{itx}\,dx$ modulo $D$.
For $k\le2$, integration by parts arbitrarily often against
$(ix)^k b_0(x)$ gives $|m^{(k)}(t)|\ll_M(1+|t|)^{-M}$.

In $[j+1/4,j+3/4]$ partition at the distinct interior absolute
zero heights. There are at most $N(j+1)$ partition points in
the interior by the signed, multiplicity-counted Jensen bound.
Take the closed middle half $[a_j,b_j]$ of the leftmost longest
gap and its midpoint $R_j$. Even when an endpoint of the window
is a zero, the selected interval contains no absolute height.
Its width is at least $1/(4(N(j+1)+1))\gg j^{-2}$. This rule
includes empty windows, treats both signs together, and gives
$1/2\le R_{j+1}-R_j\le 3/2$ independently of $M$.

Let $\chi_j(t)=h((|t|-a_j)/(b_j-a_j))$, where $h$ is a fixed
smooth profile equal to one on $(-\infty,0]$ and zero on
$[1,\infty)$. It is constant near zero and near every ordinate,
with $\|\chi_j^{(k)}\|_\infty\ll j^{2k}$ for $0\le k\le2$.
Every smooth symbol with bounded derivatives through order two
preserves $D$ by Leibniz. Write $\overline M_g$ for the induced
multiplier. If $B_R v=\sum_{|t|\le R,k<n_t}\ell_{t,k}(v)\psi_{t,k}$
(the sum uses the allowed nonnegative $k$), then
$$
F_j:=\overline M_{\chi_jm}=B_{R_j}\bar A.
$$
Indeed, for every representative $u$, the two sides have the
jets of $mu$ at all retained ordinates and zero jets elsewhere.
At a retained double jet this uses $(\chi_jmu)'=(mu)'$ there,
not just $\chi_j=1$. Equality of all jets implies equality in
$X$. Thus $SF_jQ=T_{R_j}$ is the original finite sum, even if
some individual biorthogonal vectors have large norms.

For $g_j=(\chi_{j+1}-\chi_j)m$, the support lies in
$j+1/4\le |t|\le j+7/4$. Leibniz on both transitions and the
intervening plateau gives
$\max_{k\le2}\|g_j^{(k)}\|_\infty\ll_M j^{4-M}$. This bounds
the multiplier norm up to a fixed constant: Expand $(g_ju)'$
and $(g_ju)''$ in the derivative norm, then take the infimum
over representatives for the quotient. By the finite-sum
identity, $F_{j+1}-F_j$ has range in the span of the vectors
for $R_j<|t|\le R_{j+1}$. Its rank is at most the capped count
there, at most $N(j+2)=O(j^2)$. Thus
$$
\|F_{j+1}-F_j\|_1\le
\operatorname{rank}(F_{j+1}-F_j)\,\|\overline M_{g_j}\|
\ll_M j^{6-M}.
$$
Starting with a finite-rank $F_j$, the increments telescope in
trace norm for $M>7$. The limit is $\bar A$, since the omitted
symbol $(1-\chi_j)m$ vanishes inside $|t|<a_j$ and its first
two derivatives and value are $O_M(j^{4-M})$ on the entire
exterior. The same multiplier estimate gives operator-norm
convergence to $\bar A$. Summing from $j$ gives trace-norm
error $O_M(j^{7-M})$; take $M>A+7$ for any requested $A$.

The isometry $S$ identifies $S(\bar A-F_j)S^*$ with the
quotient error plus a zero summand, preserving singular values.
The lifted term has output $S\psi_{t,k}(x)$ and input density
$A'\eta_{\chi,t,k}(y)$ against $d\mu(y)$. With $\nu=w\mu$ the
Haar kernel is $K_\mu(x,y)=w(y)K_\nu(x,y)$, so its mixed norm
is exactly the Hilbert–Schmidt norm. The latter is bounded by
the trace norm, proving the same rate for the corrected kernels
with no reciprocal weight inserted in Haar integration.

**Control and limit of the test:** If two positive model zeros
$p,q=p+10^{-30}$ straddle a cut, a smooth profile taking one
and zero there needs slope of magnitude at least $10^{30}$.
No such split is required here: A transition of width
$\gg j^{-2}$ is selected in an empty interval, not at a
prescribed pair. At any double jet, changing a retained cutoff
germ from $(1,0)$ to $(1,1)$ adds $(mu)(t)$ to its unnormalized
derivative coordinate. The actual construction avoids both
errors. These controls are not data about Gaussian zeros. An
arbitrary prefix can split a close pair or an absolute-height
tie; this proof does not bound that prefix. The broader card
remains open. No diagonal, trace value, or equivalence of
global orderings follows.
