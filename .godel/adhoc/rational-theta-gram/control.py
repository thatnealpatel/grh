"""Finite controls for the weighted theta Gram calculation in handoff.md."""

from math import ceil, factorial, floor

from sage.all import QQ, RealBallField

R = RealBallField(160)
alpha = QQ(1) / 4


def poly_tail(x, rate):
    """Integral from x to infinity of (1+y²)² exp(-rate*y) dy."""
    rate = R(rate)
    terms = (
        coeff * factorial(p) / QQ(factorial(p - i)) * x ** (p - i) / rate ** (i + 1)
        for p, coeff in [(0, 1), (2, 2), (4, 1)]
        for i in range(p + 1)
    )
    return (-rate * x).exp() * sum(terms)


def mass(lo, hi, h):
    """4h times the weight integral on a cell; hi=None denotes infinity."""
    if lo < h and (hi is None or h < hi):
        return mass(lo, h, h) + mass(h, hi, h)
    rate = 1 + 2 * alpha if lo < h else 1 - 2 * alpha
    left = poly_tail(R(lo / h).log(), rate)
    right = 0 if hi is None else poly_tail(R(hi / h).log(), rate)
    return 4 * (left - right)


def bound(h, coeffs, periods):
    """Enclose the full Gram quadratic form of a real coefficient vector."""
    columns = range(2, len(coeffs) + 2)
    points = sorted({QQ(i) / k for k in columns for i in range(k + 1)})
    cells = []
    for u, v in zip(points, points[1:]):
        height = sum(c * floor(k * (u + v) / 2) for k, c in zip(columns, coeffs))
        if height:  # Skip the zero cell at r=0, where the bare weight diverges.
            cells.append((u, v, height**2))
    inside = sum(p * mass(n + u, n + v, h) for n in range(periods) for u, v, p in cells)
    tail = sum(p * (v - u) for u, v, p in cells) * mass(QQ(periods), None, h)
    factor = (1 + QQ(1) / periods) ** 5
    return inside + tail / factor, inside + tail * factor


def report(label, lo, hi):
    # Suggest decimal endpoints and verify that the balls are strictly inside.
    scale = 10**7
    left = QQ(floor(float(lo) * scale) - 1) / scale
    right = QQ(ceil(float(hi) * scale) + 1) / scale
    assert R(left) < lo and lo < hi and hi < R(right)
    print(f"{label}: [{float(left):.7f}, {float(right):.7f}]")


# B=2, m=2, h=1. Both normalizations in the note give C22=-1.
short = mass(QQ(1) / 2, QQ(1), QQ(1))
lo, hi = bound(QQ(1), [1], 512)
assert short > 0 and short < lo
report("Full Gram, m=2", lo, hi)
report("Full trace, m=2", -1 / lo, -1 / hi)
print("Clipped trace at X=0:", -1 / short)

# A signed combination on the m=8 grid, enclosed at two tail resolutions.
coeffs = [2, -3, 0, 1, -2, 1, 1]
coarse = bound(QQ(1) / 4, coeffs, 8)
fine = bound(QQ(1) / 4, coeffs, 256)
assert coarse[0] < fine[0] and fine[1] < coarse[1]
report("Eight-cell quadratic form, N=8", *coarse)
report("Eight-cell quadratic form, N=256", *fine)
