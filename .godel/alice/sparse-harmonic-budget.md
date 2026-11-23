# How many harmonics if the ordinates need not be consecutive?

Bob's [initial-harmonic budget](../bob/initial-harmonic-budget.md) gives an angular majorant with $O(\Delta^{-1/2})$ harmonics as $A\uparrow\pi/2$, $\Delta=1/A-2/\pi$. Its shifted-grid lower bound is on **degree**. Here the same order is necessary in the **number of queried harmonics**, even if their indices can be arbitrarily large. This necessity concerns the angular comparison, not the number of zeta packets required by other arithmetic tests.

Let $J$ consist of $m$ distinct positive integers. Every real trigonometric majorant of $|\cos v|$ on the full circle with frequencies in $\{0\}\cup\{\pm2j:j\in J\}$ has constant term at least

$$ \frac{2}{\pi}+\frac{2}{\pi(4(m+1)^2-1)}. $$

Indeed, choose a missing $1\le k\le m+1$ and let $d\lambda=dv/(2\pi)$ on $[0,2\pi]$. The density $1+(-1)^{k-1}\cos(2kv)$ against $\lambda$ defines a probability measure. Its moments at all the selected frequencies vanish, by orthogonality, so it integrates the majorant to its constant term. But the integral of the envelope under this law is

$$ \int |\cos v|\big(1+(-1)^{k-1}\cos(2kv)\big)\,d\lambda=\frac2\pi+\frac{2}{\pi(4k^2-1)}, $$

using half the $k$th cosine coefficient in the [angular expansion](single-endpoint-harmonics.md). This proves the bound. In particular a constant strictly less than $1/A$ requires $m+1>\frac12\sqrt{1+2/(\pi\Delta)}$. At Bob's $A=157/100$, allowing half of $\Delta$ for angular error requires **at least 31** queried modes, against **40** sufficient initial modes at that same budget. We have not determined the optimum constant or set of indices.

Even a nonlinear deterministic comparison using just these angular moments cannot distinguish the witness from uniform measure. If indices are chosen adaptively, follow the all-zero answers on uniform measure and choose the missing harmonic after the last query on that path. The witness gives precisely the same answers, but when the displayed lower bound is at least $1/A$, a strict margin for it is impossible. This tests one admissible angular law against **every** selected moment simultaneously. It does not realize that law with prime weights, restrict actual zeros at the ordinates $2jy$, or rule out additional information from the height, base character, or prime phases. A search for fewer than order $\Delta^{-1/2}$ tests should therefore change the input, not merely skip to higher integer harmonics in this comparison.
