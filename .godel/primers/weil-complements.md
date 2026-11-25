# Weil complements: Two edge bumps detect the missing estimate

**Claim on paper.** The actual [packed space $V_R$](weil-windows.md) leaves two empty
edge strips. A two-dimensional test in its $L^2$ orthogonal complement reduces a
necessary lower bound to a smoothed prime-power discrepancy. Even a subexponential lower
error for this test would be an RH-level result.

**Edge calculation.** The shifted left support and common right cutoff leave
$(-R,-R+2-\log 2)$ and $(R-1/2,R)$ empty. Fix a real, nonzero $\phi\in C_c^\infty(-r,r)$
with $0<r<1/8$. Translate it to centers $\pm(R-1/4)$, giving orthogonal
$\phi_+,\phi_-\in V_R^\perp$. Write $L=2R-1/2$. With $M_f(s)=\int f(v)e^{sv}\,dv$,
use the reflected Weil form
$B(f,g)=\sum_\rho m_\rho M_f(z_\rho)\overline{M_g(-\bar z_\rho)}$,
where $z_\rho=\rho-1/2$ and $m_\rho$ is the order of the strip zero $\rho$. Write
$Q(f)=B(f,f)$, and put
$$
C_\phi(y)=\int\phi(x+y)\phi(x)\,dx,\qquad
\Psi_\phi(s)=M_\phi(s)M_\phi(-s),\qquad c_\phi=\Psi_\phi(1/2).
$$
The mixed correlation is $F(t)=C_\phi(t-L)$, and its transform is $e^{sL}\Psi_\phi(s)$.
On the diagonal a simultaneous translation leaves the correlation unchanged. The
$2\times2$ compression in the normalized bump basis has diagonal
$Q(\phi)/\|\phi\|_2^2$ and conjugate off-diagonals with modulus
$|B(\phi_+,\phi_-)|/\|\phi\|_2^2$. Its minimum eigenvalue is
$$
\frac{Q(\phi)-|B(\phi_+,\phi_-)|}{\|\phi\|_2^2}.
$$

Apply the scalar radial formula to the mixed profile $F$ (equivalently, polarize the
formula on autocorrelations). For large $R$ only the positive prime shifts meet $F$. Set
$$
S_\phi(L)=\sum_{n\ge2}\frac{\Lambda(n)}{\sqrt n}C_\phi(\log n-L),\qquad
D_\phi(L)=S_\phi(L)-c_\phi e^{L/2},
$$
where $\Lambda(p^k)=\log p$ and $\Lambda$ is zero otherwise. The pole terms are
$c_\phi(e^{L/2}+e^{-L/2})$. With $F(0)=0$ and $F(-t)=0$ for $t>0$, the real-place
contribution to the zero sum is $-\int_0^\infty F(t)e^{-t/2}/(1-e^{-2t})\,dt$. Its
leading term cancels the smaller pole term. Subtracting the prime term therefore gives
$$
B(\phi_+,\phi_-)=-D_\phi(L)+O_\phi(e^{-5L/2}).
$$
A lower bound $-\delta_R\|f\|_2^2$ on the smooth complement would force
$|D_\phi(L)|\le Q(\phi)+\delta_R\|\phi\|_2^2+O_\phi(e^{-5L/2})$.

**Residue test on paper.** Because $2r<\log2$, $S_\phi$ vanishes for $L\le0$. Absolute
unfolding for $\Re s>1/2$ gives
$$
\int_0^\infty D_\phi(L)e^{-sL}\,dL
=\Psi_\phi(s)\left(-\frac{\zeta'}{\zeta}(1/2+s)\right)-\frac{c_\phi}{s-1/2}.
$$
The pole at $1/2$ cancels. At $z_\rho=\alpha+i\gamma$ the residue is
$-m_\rho\Psi_\phi(z_\rho)$. In fact
$\limsup_{L\to\infty} e^{-\alpha L}|D_\phi(L)|\ge m_\rho|\Psi_\phi(z_\rho)|$: If the
limsup is finite, continue the Laplace identity into $\Re s>\alpha$, multiply by $x>0$
at $s=z_\rho+x$, and let $x\downarrow0$. The initial bounded interval contributes zero
in the limit, and the tail is bounded by the limsup plus arbitrary slack, using
$x\int_0^\infty e^{-xL}dL=1$.

To kill both pole moments, fix a real even $\psi\in C_c^\infty(-1,1)$ with positive
integral and use $\phi=(\partial^2-1/4)[\lambda^{-1}\psi(\cdot/\lambda)]$,
$0<\lambda<r$. Then $M_\phi(s)=(s^2-1/4)M_\psi(\lambda s)$. For each strip zero the
exceptional dilations are discrete, since $M_\psi(0)>0$ and $z_\rho\ne\pm1/2$. One fixed
dilation outside the countable union sees every zero; now $D_\phi=S_\phi$.

**What it does not show.** A known line zero gives $\limsup |S_\phi|>0$ for this bump,
ruling out $o(1)$ coupling but not positivity: The coupling need not exceed the fixed
diagonal. A hypothetical off-line zero with $\alpha>0$, available by symmetry if there
is any, would give negative Rayleigh quotients of size at least $c e^{2\alpha R}$ along
a subsequence. The arithmetic estimate to test is $S_\phi(L)=O_{\phi,\eta}(e^{\eta L})$
for every $\eta>0$ for the one fixed generic bump. Conversely, assuming RH, the cross
term is a Fourier series in $L$ with weights $m_\rho|M_\phi(i\Im\rho)|^2$ summing to
$Q(\phi)$, hence $|B(\phi_+,\phi_-)|\le Q(\phi)$. Thus even a lower error
$O_\eta(e^{\eta R})$ for every $\eta>0$ on just this family would imply RH, without
the mixed packing estimate; RH would give zero error. The prime-sum target is smoothed
square-root-scale control at prime scale $e^L$, not relative prime number theorem
accuracy. It supplies no direct arithmetic comparison with the diagonal.

**Source.** Checked ingredients are `Masullo.rationalIdeleRadial_explicit_formula` in
[`RationalIdeleRadialExplicitFormula.lean`](../../Proofs/Theorems/RationalIdeleRadialExplicitFormula.lean),
`Masullo.rationalLocalRadialFourier_tsum_eq_vonMangoldt` in
[`RationalLocalRadialSum.lean`](../../Proofs/Theorems/RationalLocalRadialSum.lean), and
the tested Gamma evaluation `Masullo.compactLogMellin_GammaReal_evaluation` in
[`GammaRealMellin.lean`](../../Proofs/Props/GammaRealMellin.lean). The mixed edge
compression, residue bound, and estimate required of the complement are paper
deductions, not Lean conclusions.
