# A complementary right-sector prime law

In the depth-$39/20$ spline comparison of [two-term-10-2.md](two-term-10-2.md), the [248-slab right-sector law](right-sector-10-2.txt) is admissible and has **normalized scalar slack greater than $3.58\cdot10^{-5}$** throughout

\[
-9/50\le s\le 1/2,\qquad 6/5\le d\le 2,\qquad
H(x)=a e^{isx}+b e^{i(s+d)x},\quad ab\ge0,\quad |a|+|b|=1.
\]

Here $s$ is always the earlier shift. At the reported residual $(s,d,a)=(0,32/25,3/5)$ with $b=2/5$, SageMath encloses the capacity at $0.40616248503757005\ldots$, the absolute center at $0.40330873124089258\ldots$, and their difference at $0.002853753796677473713\pm 3.40\cdot 10^{-22}$. For comparison, using the same normalization, the mid-gap and hard-pair profiles give negative slack at that point, about $-0.003409500390915$ and $-0.001495010698025$, respectively. The new law is not asserted to cover $1\le d<6/5$ or to cover opposite signs. This is a directional result in the spline comparison model, not an arithmetic realization or a result on zeta zeros.

## Exact data and replay

Knots are stored as $64z_j$ and each row gives exact integer pairs $(10^8X,10^8p)$. The law before $-10$ is $X=0$ and the last row is constant from $16$ onwards. The [checker](right-sector-check.py) substitutes the rational table, verifies nonnegative probabilities summing exactly to one, and encloses the angular surplus above $8/9$ at $8.1538562353004695\ldots\cdot 10^{-7}$. It proves the strict global cap bounds $\|G_A\|_\infty<618660/10^6$ and $\|G_B\|_\infty<119516/10^5$ (505 and 107 finite Taylor boxes, with tails beyond 64), both stronger than the required depth-$39/20$ caps.

From the repository root, in SageMath 10.9 with assertions enabled:

```sh
sha256sum .godel/bob/right-sector-10-2.txt
sage .godel/bob/right-sector-check.py
```

The checked SHA-256 is `3edc2b026e86288a8c60ec18906abd7843b915a6793d54cabcda9a7046136f70`. The replay completed with 311 accepted rectangles and minimum normalized slack lower bound above $0.0000358461854882$. With the Sage environment's Python, `--point-only` limits the check to admissibility and the residual. Likewise, `--baseline midgap-sector` and `--baseline hard-pair` replay the respective negative residuals; they do not recheck the baseline caps.

The full check uses the [mid-gap certificate's](midgap-sector-10-2.md) signed-center interpolation, with imbalance nodes $0,1/8,3/16,1/4,5/16,3/8,1/2,3/4,1$. For $\eta=|a-b|$, the capacity is concave in $\eta^2$ since its integrand is a square root of an affine function of $\eta^2$, integrated against the positive measure $(1-|m|^2)d\mu$. At each corner, the checker minimizes the capacity chord minus $(|S(s)+S(s+d)|+\eta|S(s)-S(s+d)|)/2$ exactly as a quadratic in $\eta$ on each adjoining-node interval. The absolute-center formula takes the worse of the two orientations and the two center signs. Curvature bounds extend the signed branches to each rectangle before taking their infimum; a uniform Fourier-tail allowance of $10^{-12}$ is subtracted. The residual point also has a separate direct binomial-capacity check without using the imbalance chords.

## Discovery replay (not a certificate)

The [discovery patch](right-sector-discovery.patch) reconstructs the adapted scratch script from the tracked two-term fitter at base `620a1b57ce4a5ff715c853a5b0742ce9ff7370cb`. The retained table was first emitted at zero-based exchange round 7 with Clarabel 0.11.1 (`faer`), SciPy 1.18.1 and four solver threads. The sampled test at that round gave minimum normalized slack about $.000489$; the solver status was `NumericalError` (primal and dual residuals about $8.88\cdot10^{-10}$ and $3.80\cdot10^{-7}$). Neither the sampled minimum nor the solver status certifies the table. The exact probability recovery and independent ball-arithmetic replay determine the result.

```sh
work=$(mktemp -d)
patch -s -o "$work/right-sector-fit.py" .godel/bob/search-two-term-law.py \
  .godel/bob/right-sector-discovery.patch
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 "$FIT_PYTHON" -u \
  "$work/right-sector-fit.py" --out "$work/right-sector-local" \
  --refine --left 10 --atoms 96 --steps 13 --mean 8e-7 --fpad 1.2e-5 \
  --seconds 14 --slo -.18 --shi .5 --dlo 1.2 --dhi 2
```

`FIT_PYTHON` is the Python interpreter with those solver packages. Because the solve is time limited, the exact replay input is the checked-in table, not a regenerated output. A broad single-law fit through the $d=1$ edge had negative sampled margin; this was not an infeasibility certificate. The next decision is whether a law mixture and the existing certificates cover the lower-gap directions.
