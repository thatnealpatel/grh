# A fixed-character window across the first prime

Let $\chi=\chi_{-4}$ be the odd primitive character of conductor four. Write $D$ for support diameter (twice the reciprocal budget in the [Pick limit](pick-block-weil-window.md)). Use the standard conductor-normalized completion. For complex $u$ supported on $[0,D]$ set $A(t)=\int u(x+t)\overline{u(x)}\,dx$ with zero extension. In the centered Weil form the archimedean multiplier is $\Re\psi(3/4+iy/2)+\log(4/\pi)$ and the prime contribution is $-2\Re\sum_{n<e^D}\chi(n)\Lambda(n)A(\log n)/\sqrt n$. There are no pole terms. Translation of the support changes neither expression.

**Lower bound.** At $D=111/100$ the *whole form* satisfies $Q(u)\ge\|u\|_2^2/50$. The comparison below is analytic; the final one-dimensional inequalities are checked by ordered sums in 100-bit ball arithmetic in [chi4-endpoint-cert.py](chi4-endpoint-cert.py) (Sage 10.9, not a Lean verification). In particular this includes the nonzero $n=3$ term, rather than removing it by a support condition. The value $111/100$ is not claimed optimal.

Put $c=\psi(3/4)+\log(4/\pi)$ and $w(t)=e^{-3t/2}/(1-e^{-2t})$ for $t>0$. The digamma difference integral, with its integration variable equal to $2t$, and Plancherel give

$$Q_{\rm arch}(u)=c\|u\|^2+2\int_0^\infty w(t)(\|u\|^2-\Re A(t))\,dt.$$

Use $h(x)=1-a(2x/D-1)^2$ inside the window, $a=9/20$, and $h=0$ outside. This weight is positive throughout the window. For each pair of interior points bound $2\Re(\bar u(x)u(y))$ above by $|u(x)|^2 h(y)/h(x)+|u(y)|^2 h(x)/h(y)$. This gives $Q_{\rm arch}\ge\int |u|^2 V_h$ with

$$V_h(x)=c+\int_0^\infty w(t)\big[2-(h(x+t)+h(x-t))/h(x)\big]dt.$$

One may first cut off $t$ at zero, then pass to the limit for smooth interior tests. Equivalently, the discarded interior difference is a nonnegative weighted square. By log-form density the conclusion extends to the window form domain (contract support and mollify as in the Pick note). The boundary jumps of the *comparison weight* do not require the test to jump. At this $D$, only $\log3$ is active. The two endpoint strips participating in the overlap are disjoint: $D<2\log3$. Applying $2|uv|\le |u|^2+|v|^2$ to its autocorrelation bounds the prime contribution below by $-(\log3/\sqrt3)\int_E |u|^2$, with $E=[0,D-\log3]\cup[\log3,D]$. It would be incorrect to multiply the operator cost by the lengths of these strips. The logarithmic boundary potential, not small overlap measure alone, pays that cost.

For reproducibility, write $U(s)=\int_0^s tw(t)dt$, $B(s)=\int_0^s t^2w(t)dt$, and $T(s)=\int_s^\infty w(t)dt$. On $0<x\le D/2$, Taylor expansion of the quadratic on each interior side gives exactly

$$V_h=c+T(x)+T(D-x)+\frac{4a[B(x)+B(D-x)]/D^2-h'(x)[U(D-x)-U(x)]}{h(x)}.$$

Indeed each one-sided integrand is $1-h(x\pm t)/h(x)$: On its interior part the constant $1$ cancels $h(x)/h(x)$, and beyond the endpoint only $1$ remains. The other half follows by reflection. On the uniform grid $s_j=jD/8192$, $w$ and $tw=e^{-t/2}t/(2\sinh t)$ are decreasing, the latter with limit $1/2$ at zero. For each cell the script lower-bounds both $T$ terms at the larger argument by right sums plus sixteen positive exponential integrals beyond $D$. It lower-bounds $B$ at the smaller argument using $s_j(s_{j+1}w(s_{j+1}))$ on each summation cell. It upper-bounds the difference of $U$ directly by *left sums on the enlarged interval* $[s_j,D-s_j]$. On the left half $h$ increases and $h'$ is nonnegative and decreases, so division and multiplication in the sign-separated terms have the indicated one-sided bounds. Each of the 4096 cells passes $V_h-(\log3/\sqrt3)1_E>1/50$, including cells straddling an endpoint of $E$.

**Limit of the argument.** This comparison bounds the signed translations by absolute values. It is a short-window certificate, not a mechanism for proving positivity for every diameter. In particular it gives no sign at $D=2$ ($b=1$), where $3,5,7$ all occur. Positive Rayleigh quotients of fixed sine trials at that diameter bound the floor only from above. A different [circle comparison](chi4-circle-window.md) certifies that larger diameter.
