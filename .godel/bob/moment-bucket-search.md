# Find the rare heights without reading the whole shell

The [dyadic moment bound](dyadic-prime-pair-moments.md) counts exceptional unit intervals but does not list them. For a frozen retained shift there is a Las Vegas algorithm to **list a buffered cover**, in expected $t^{3/4+o(1)}$ bit operations at fixed amplitude, or $t^{17/20+o(1)}$ down to amplitude $m=X^{-1/10}$. This is on $[t,5t/4]$, not on the whole reconstruction band. It uses positivity of the original modulus moment, not of any individual signed gap. The randomized step tests collisions of integer indices only. Acceptance of a cover does not rely on a probabilistic estimate of any prime phase.

## Positive input and its cost

Use the frozen supports, real weights, and unrounded log ratios in [the cap test](retained-shell-overshoot.md). In the bit model supply the discrete support, the integer order $h=\lfloor\log(t/4)/(2D)\rfloor$, and integer $u_0,N$ with $N$ a power of two, $N\asymp t$, so $u_0+[0,N-1]$ covers the shell (allow a polylogarithmic extension for boundary cells). The exact input $q$ specifies $t$ and the weights; the support convention avoids assuming a separation oracle at transcendental endpoints. Rounding the order down one more unit with certified slack costs no exponent. Write $A=\sum_p w_p=O_K(1)$, $y_j=|Z_d(u_0+j)|^{2h}$, and $S=\sum_{0\le j<N}y_j$.

Expand $Z^h$ into multisets $\alpha$ of size $h$, with multinomial coefficient times $\prod w_p^{\alpha_p}$ and frequency $\mu_\alpha=\log\prod ((p+d)/p)^{\alpha_p}$. Since $hD=\tfrac12\log t+O(D)$ and $\log h=D/2+O(\log D)$, the number of multisets is at most $\binom{\lfloor X\rfloor+h}{h}\le t^{1/4+o(1)}$. Thus

$$y_j=\Re\sum_{a=1}^{M}c_a e^{ij\theta_a},\qquad M\le t^{1/2+o(1)},\quad \sum |c_a|=A^{2h},$$

using all ordered **pairs of multisets**, $\theta_a=\mu_\alpha-\mu_{\alpha'}$, including $e^{iu_0\theta_a}$ in the coefficient. No expansion into permutations and no need to merge duplicate differences. For an empty support return the empty list.

Put $T=\max(t,N)$ and center $u_c=u_0+(N-1)/2$. Majorize the padded interval by $4\operatorname{sinc}^2((u-u_c)/T)$ with $\operatorname{sinc}(x)=\sin(x)/x$. Its angular transform vanishes outside $[-2/T,2/T]$. Multiplication by the moment enlarges that bandwidth by at most $O(hD/X)=o(1)$, so the sum of this product on the whole integer lattice equals its integral by Poisson summation (absolutely summable tails and compact transform). Nonnegativity on the entire lattice is important. In the integral all nonzero differences disappear: Their rational arguments have numerator and denominator at most $X^{2h}$ and hence $|\theta_a|\ge X^{-2h}\ge4/t$. At zero the multisets coincide by the least differing start's prime valuation. Therefore

$$S\le 4\pi T h!\big(\sum w_p^2\big)^h\le 4\pi T (h A\,8D^2/X)^h\le t^{3/4+o(1)}.$$

This does **not** delete nonzero differences from a block sum. Use a dyadic $\tau\in[\theta_0/2,\theta_0]$ for the desired node-moment threshold $\theta_0$. A fixed constant fraction smaller also works if selecting by coarse relative enclosures. Compute $S$ by the geometric formula below to absolute error $\tau/8$ and choose $K_0=\lceil1+(\widehat S+\tau/8)/\tau\rceil$. Thus $1+S/\tau\le K_0\le3+S/\tau$; finding an operational mass bound itself takes no scan.

## Find the positive blocks

A block at length $s\mid N$ has index $b$ and mass $Y_b=\sum_{v<s}y_{bs+v}$, where indices start at zero. Start with the whole interval. After each split consider only children of survivors. Given at most $8K_0$ candidates at one level, choose a modulus $p$ such that the number of colliding **candidate pairs** modulo $p$ is at most $K_0$. For $B=N/s$ blocks use $p=B$ when $B\le P=\lceil C K_0\log^2(2N)\rceil$. Otherwise draw a uniform prime in $[P,2P)$, rejecting it unless the check passes. A difference $<N$ has at most $\log N/\log P$ prime divisors there and the interval has $\gg P/\log P$ primes. Conditional on these candidates the expected collision count is $O(K_0^2\log N/P)\le K_0/2$ for adequate absolute $C$. Uniform integer rejection with a deterministic polynomial-bit primality test and sorting the candidate residues suffice; the collision count is the sum of $\binom{m_r}{2}$ for their multiplicities $m_r$. Rejected primes need no transforms.

For every $r<p$ estimate $H_r=\sum_{b\equiv r\ (p)}Y_b$ to absolute error $\tau/8$, **including all blocks**, and keep candidates in residues estimated at least $\tau/2$. An ancestor of a hit $y_j\ge\theta_0$ never drops out. A flagged residue has true mass at least $3\tau/8$. The number of survivors is at most

$$8S/(3\tau)+\sum_r\binom{m_r}{2}<4K_0,$$

because $m\le1+\binom m2$ for $m\ge1$. This reestablishes the candidate bound after splitting, even if most flagged bucket mass comes from noncandidates. At singleton blocks apply the same buffered test directly to $y_j$ at the survivors: The returned list contains every hit at $\theta_0$, and every entry has $y_j\ge3\tau/8$. No comparison at an exact transcendental threshold is promised.

## Why one layer does not cost a full scan

Let $G_l(z)=\sum_{0\le j<l}z^j$. With $B=ep+d_0$, $0\le d_0<p$, put $l_r=e+1_{r<d_0}$. Exactly, including empty buckets and zero frequencies,

$$H_r=\Re\sum_a c_a G_s(e^{i\theta_a})G_{l_r}(e^{ips\theta_a})e^{irs\theta_a}.$$

The formula follows by writing $j=s(r+kp)+v$. Likewise $S=\Re\sum_a c_aG_N(e^{i\theta_a})$. Evaluate $G$ by binary composition of the pairs $(z^u,G_u)$ and $(z^v,G_v)$ to give $(z^{u+v},G_u+z^uG_v)$. There is no division at a near resonance.

There are only two possible coefficient lists $d_a=c_aG_sG_{l_r}$, each of total absolute mass at most $V=N\max(1,A^{2h})$. For either list let $F$ be the least power of two $\ge p$. Approximate $Fs\theta_a/(2\pi)$ within $1/4$ and round the approximation to integer $k_a$. The exact residual $v_a=Fs\theta_a/(2\pi)-k_a$ has modulus at most $3/4$, including a grid tie. For $0\le r<p$ the remaining phase is $e^{2\pi i r k_a/F}e^{2\pi i(r/F)v_a}$. Bin $d_a(2\pi i v_a)^j/j!$ by $k_a\bmod F$, take a positive-sign unnormalized radix-two DFT, and multiply output $r$ by $(r/F)^j$. Sum these transforms for $0\le j<J$. Taylor's integral remainder on the real angle gives absolute error at most $V(2\pi)^J/J!$. In both applications $V=t^{O(1)}$ and $1/\tau=t^{O(1)}$, so $J=O(\log t)$ suffices for $\tau/32$.

For clarity about bit complexity, all multinomials and prime products before taking logs have $O(\log t)$ bits. Enumerate multiplicity vectors in polynomial-in-$\log t$ cost per vector (including writing all $O(X)$ entries). Logs can use binary reduction and the convergent atanh series on $[1,2]$; algebraic powers defining $t$ use integer root approximation. For rotations reduce by an integer multiple of a sufficiently accurate $2\pi$ and use Taylor series on a bounded residual. Compute $\pi$, for example, by a Machin arctangent series. All unreduced arguments and chosen reduction integers are $t^{O(1)}$, so guard bits for the subtraction are necessary. The integer $k_a$ selected above is held fixed in subsequent refinements; no equality test at a rounding boundary is used.

One conservative precision budget is $C_1\log^2 t$ fractional bits. Past the elementary inputs and exact integers, the coefficient products, geometric powering, Taylor recurrences, **balanced** bin additions, FFT butterflies, and final combinations have depth $O(\log t)$. Exact intermediate magnitudes are $t^{O(1)}$: The powers in geometric composition have modulus one, sums have modulus at most their length, and the Taylor coefficient lists have total absolute mass $\le e^{2\pi}V$. Multinomial factors can be applied after the products of weights. Each rounded operation on these bounded numbers amplifies an incoming absolute error $\le1$ by at most $t^{O(1)}$, plus the last-place error (Taylor division is by a positive integer). The indicated precision with sufficiently large $C_1$ therefore gives total arithmetic error $<\tau/32$ even after cancellation. Elementary inputs to that precision, with the guard bits just described, take polynomial-in-$\log t$ bit work. Balanced reductions can be implemented by sorting contribution records. Each accepted layer thus costs $(M+p)(\log t)^{O(1)}$ bit operations. With $O(\log t)$ layers and expected $O(1)$ prime attempts per layer, the entire expected cost including direct final checks is

$$(M+1+S/\tau)(\log t)^{O(1)}.$$

Here the polynomial hides processing of the polylogarithmic-size support per direct test. This is sensitivity to *mass*, not a guarantee proportional to the actual number of peaks.

## Transfer and check

For continuous amplitudes $\ge b$ use node threshold $\theta_0=(b/2)^{2h}$, since $|Z'|\ll_K D/X=o(b)$ even for $b=m$. Both adjacent integer nodes of such a point are covered for large $t$. This costs $t^{3/4+o(1)}$ at fixed $b$ and $t^{17/20+o(1)}$ at $b=m$, since $m^{-2h}=t^{1/10+o(1)}$. At fixed amplitude clear the complement below, say, $b=a/2$. On covered unit cells the original signed statistic can be tested with error $O_K(1/n)$ including interpolation (indeed $|( |Z|^2)'|\ll_K D/X=o(1/n)$). The dense deletion error is $O_K(1/n)$ as before. This preserves the coefficient of $\log n/n$, not an exact bounded additive constant. At the small cutoff the same cover with $b=(1-2X^{-1/5})m$ permits retrieval of all relevant nodes of the [buffered high-branch grid](genuine-high-shell.md), including its outer boundary nodes if padded. Evaluate the *actual* correction and kernel there; do not substitute the hash moment for the weighted sum. Relax fine comparisons slightly if undecided, with an additional $o(X^{-1/5}m)$ buffer. There is still no bound on the resulting arithmetic budget.

[The interval checker](check-moment-buckets.py) tests the two-length batching identity, geometric composition, Taylor gridding, and FFT against direct positive block energies. It uses 44 genuine prime edges at $q=100000007,d=26$ on 256 consecutive integer translates, with $h=1$ as an evaluator test; a second partition tests an angular grid tie and empty residues. Run with `/opt/sage-10.9/bin/python .godel/bob/check-moment-buckets.py`. This is not a benchmark of the full adaptive algorithm. The running time above is proved in the stated input model. Neither the time nor the dyadic mass bound excludes an overshoot at any specified height. For a common-dip test in a single polylogarithmic neighborhood direct real evaluations there are cheaper than a shell search.
