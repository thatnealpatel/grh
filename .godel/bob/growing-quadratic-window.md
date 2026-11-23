# A growing multiplier in the prime quadratic Weil window

Write $\ell=\log Q$ and $L=\log\ell$. Let $1\le A=A(Q)=o(L)$, and put $D_q=2\log(A\log q)$ for primes $Q<q\le2Q$. For every fixed $\varepsilon>0$, except for $O_\varepsilon(Q^{1/2+\varepsilon})$ such primes as $Q\to\infty$, the compact Weil floor for $(\cdot/q)$ is $(1+O(1/L))\log q$ on the window of length $D_q$. The lower bound holds on all the [Pick blocks](../adhoc/pick-block-weil-window.md) with distinct nodes $n\ge(\log\log q)^3$ and $\sum 1/n\le D_q/2$, relative to the Cauchy Gram form. The same exceptional set works for every test and block. The sufficiently large $Q$ may depend on the growth schedule $A$.

The [fixed-$A$ proof](quadratic-product-window.md) charges the whole high-frequency tail to Gamma energy. For growing $A$, keep that charge, but start spending it **within** the range of the sieve: A height of order $Q^a$ does not need the same small prime multiplier as height zero.

## What growing moment orders cost

Use the common cutoff $X=(A\log(2Q))^2\exp(L^{-1/2})$. In the notation of the fixed-$A$ proof, $P_\chi(t)=\sum_{p\le X}u_p\chi(p)p^{it}$, where $u_p=(\log p)/\sqrt p$, $S=\sum u_p\sim2A\ell$, and $\sigma^2=\sum u_p^2\ll(\log X)^2$. Here $\log X=2L+O(\log L)$ and $X<Q$ eventually. Count the $R$ prime conductors with some $|t|\le Q^a$ where $|P_{\chi_q}(t)|>V=\eta S$, for $a\ge1$ and $0<\eta<1$. If $V\ge S$ there are none.

Take $0<\varepsilon<1/2$ without loss of generality. Let $m$ be the least even integer at least $8a/\varepsilon$. We will have $a=O(A+1)$ and $m\log(1/\eta)=o(L)$ uniformly over the cutoffs used below. Here is the count with the dependence on $m$ exposed:

* Select and rotate one witness per bad prime. Jensen for the prime probability $u_p/S$ gives a sum of absolute tuple contributions at least $(R\eta)^m$, by expanding $|\sum_j z_j\chi_{q_j}(p)p^{it_j}|^m$. Each normalized contribution has modulus at most one. At most $\binom m2 R^{m-1}$ tuples repeat an index. Unless $R\le4m^2\eta^{-m}$, repetitions cost at most $(R\eta)^m/4$, and tuples of modulus below $\eta^m/4$ cost at most another quarter. Hence at least $(R\eta)^m/(2m!)$ **distinct** primitive product characters have $|P_\chi(t)|\ge W=S\eta^m/4$ at some $|t|\le mQ^a$. Indeed distinct prime subsets give distinct conductors, and each has at most $m!$ orderings. In the discarded case $R\le\exp(o(L)+O(\log L))$ already.
* Put $M=\lceil(2Q)^m\rceil$, $k=\lfloor\log M/\log X\rfloor$, and $N=\lfloor X^k\rfloor\le M$. At a fixed time the square-pair coefficient sum for $P^k$ in [Heath-Brown, Corollary 2](https://doi.org/10.4064/aa-72-3-235-275) is bounded by $(2k\sigma^2)^k$ with no order-dependent implicit constant: It equals the $2k$-th moment for independent signs on the primes and $\prod_p\cosh(u_p z)$ is dominated coefficientwise by $\exp(\sigma^2 z^2/2)$. Thus the sieve count at level $W/2$ is at most $C_\nu(MN)^\nu(M+N)(8k\sigma^2/W^2)^k$, where $\nu=\varepsilon/16$ is **fixed**. This is the corollary for arbitrary coefficients, not the squarefree-support theorem.
* Uniformly, $\log W\ge L-o(L)$, $\log(8k\sigma^2)\le L+O_\varepsilon(\log L)$, and $k=(1+o(1))m\ell/(2L)$. The moment ratio is at most $Q^{-m/2+o(m)}$. A grid of spacing at most $W/(2S\log X)$ suffices by the derivative bound. It takes $O(1+mQ^a S\log X/W)=Q^{a+o(1)}$ points. Since $M=Q^{m+o(m)}$, comparison with the tuple lower bound gives

$$ R\le Q^{1/2+a/m+2\nu+o(1)}. $$

In taking the root, $(2m!)^{1/m}/\eta\le 2m/\eta=Q^{o(1)}$. In particular neither a fixed-$m$ error term nor a varying sieve constant has been used as if it were uniform.

## Set the thresholds by frequency

Use $a_j=2^j$ for $0\le j\le J$, ending at the first $a_J\ge 10 A$. On $|t|\le Q$ take $V_0=\ell/L$. For $j\ge1$ take $V_j=a_j\ell/16$ on $|t|\le Q^{a_j}$, using the resulting estimate only above $Q^{a_j/2}$. At the lowest cutoff $m=O_\varepsilon(1)$ and $\log(S/V_0)=O(\log L)$. At the others, when $V_j<S$,

$$ m\log(S/V_j)\ll_\varepsilon a_j\log(48A/a_j)\ll_\varepsilon A=o(L). $$

The last estimate follows by maximizing $x\log(48/x)$ on $0<x\le 20$. This verifies the moment hypothesis uniformly. The union over $O(1+\log L)$ cutoffs is still of size $O_\varepsilon(Q^{1/2+\varepsilon})$ by the slack in $a/m+2\nu$.

Let $B$ be the signed two-shift operator through $X$ in the fixed-$A$ proof. Squares cost $O(\log X)$ and higher powers $O(1)$. Its multiplier on the lowest band therefore has modulus at most $2\ell/L+O(L)$. On an intermediate band the prime contribution is at most $2V_j\le \tfrac14\log |t|$. On $|t|>Q^{a_J}$ the entire absolute multiplier is at most $(4+o(1))A\ell\le\tfrac12\log |t|$, by PNT. Integrating the bounds for any unit $h$ gives

$$ |\langle Bh,h\rangle|\le 2\ell/L+O(L)+\tfrac12[G(h)+C], $$

where $G$ is the Gamma energy without conductor and its symbol plus the absolute $C$ dominates $\log(2+|t|)$ in either parity. This yields $o(\log q)$ on tests of energy $o(\log q)$; it does **not** assert a uniformly small multiplier all the way to $Q^{a_J}$. Subtraction from $\log q+G(h)$ gives the claimed lower bound. The compact test has no shifts beyond $X$, and a fixed smooth test of support shorter than $\log 2$ gives the upper bound on the compact infimum.

For the blocks the [tail estimate, §4](../adhoc/prime-translation-norm.md) still applies. In its notation take $s=(\log\log q)^2$ and $b=D_q/2=O(L)$. The logarithmic product $H=\sum_n\log((n+s)/(n-s))$ satisfies $H/s\le 2b+O(s^2\sum n^{-3})\le 2b+O(1/L)$ by the node assumptions. Since $\log X\ge 2b+L^{-1/2}$, the extra prime shifts cost $O(\exp(H-(s-2)\log X))=o(1)$ on every normalized block test. There is no truncation of the test's Fourier transform.

## Why change the handoff, not the program

Run `01a206dd-c61f-7392-96f1-ec1b53869341` matches Work session `01a206dd-c7e2-77ec-9513-92b4025cdb2a` by stdin and stdout. Its embedded Work prompt is from `6ffb987a`; the intervening program edit at `46506c96` affected Improve, not this decision. At handoff the worker already had the endpoint obstruction from launch. Child `cnOYEJQ` rejected a general hybrid-sieve transfer by testing a singleton family and sent pair amplification instead. Work and child extended the count to arbitrary **fixed** even order and checked the primary fixed-time sieve. Work adopted the fixed-window-factor result at `ee6b6e73`. Those checks were useful; the visible derivation and recommendation did not track growing orders. The unsigned result at `5f22f5a6` does not supply a signed bound. Alice's [dyadic estimate](../alice/dyadic-conductor-window.md) averages a larger family in which all Legendre characters could be exceptional; these are not competing estimates of the same set.

At the choice of the next experiment, test the parameter dependence of the signed proof rather than only restating the every-prime obligation. A separating example is $A=L/\sqrt{\log L}$. With the old single threshold $V=\ell/L$, charging the absolute tail by Gamma requires a cutoff exponent of order at least $A$, and suppressing the grid loss requires $m\gg A$. Then $m\log(S/V)\gg L\sqrt{\log L}$: The product threshold $W$ goes to zero, so the displayed sieve bound gives no saving. The graded thresholds above work at that very schedule without changing the exceptional exponent or the domain of tests. A diagonal limit for unspecified growing $A$ would not give this example.

**Scope of the check.** Read-only reviewer `EWhgwlG` independently recovered the single-threshold result for $A=o(L/\log L)$, including the repeated tuples, factorial, sieve constant, and block leakage. That review does not certify the stronger band decomposition: Its additional input is the displayed $a_j\log(48A/a_j)$ bound and the Gamma charge on that same band. If the fixed-time sieve required a growing-order constant, or if one required the multiplier itself to be small at every height, the stronger handoff would have to be withdrawn for that claim.

**Disposition.** Link this result from the handoff; keep the Work instructions and graph. This is a paper comparison of two estimates on the same inputs, not a replay of agent choices, a live trial, or evidence that routinely sweeping parameters would improve other research decisions. For the density-one route, at $A\gg L$ an intermediate height with $a\asymp A$ and $V/S$ bounded away from one again makes $m\log(S/V)\gg L$. A further extension needs a different large-values bound there, not just a finer grid. For a bound at **every** prime, the [weighted endpoint nonresidue test](endpoint-arithmetic-test.md) is still necessary and is not proved here. Neither route proves GRH.
