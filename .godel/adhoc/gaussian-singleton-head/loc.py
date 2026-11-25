"""Bracket real critical-line zeros by signs of a truncated theta DFT."""

from pathlib import Path

from flint import acb, arb, arb_poly, ctx

ctx.prec = 800
h = arb(1) / 256
N = 65536
dt = 2 * arb.pi() / (h * N)
last = 11001
tol = arb("1e-205")
pi = arb.pi()
assert last * dt < 271

# Analytic truncation errors (see certificate.md), enclosed in Arb.
def sum_cubes(r):
    return r * (1 + 4 * r + r * r) / (1 - r) ** 4


assert sum_cubes((arb(-1) / 2).exp()) < 200
assert 9 * arb(1).exp() * sum_cubes(arb(-1).exp()) < 1000
alias = 22000 * (271 - 2 * pi / h).exp() / (1 - (-2 * pi / h).exp())
r = (arb(242) / 241) ** 3 * (-pi).exp()
shell = (12 + h) * 9 * arb(15).exp() * 241**3 * (-241 * pi).exp() / (1 - r)
y = arb(6).exp()
r = (-2 * y * h).exp()
samples = 2000 * h * (-2 * y).exp() * r / (1 - r)
assert shell < arb("1e-300") and samples < arb("1e-300")
assert alias + shell + samples < tol

# Exact integer coefficients of the real theta polynomial through norm 240.
coef = [0] * 241
for x in range(-15, 16):
    for y in range(-15, 16):
        n = x * x + y * y
        if n <= 240:
            coef[n] += x**4 - 6 * x * x * y * y + y**4
p = arb_poly(coef)
v = [0] * N
for j in range(1537):
    x = j * h
    val = h * (5 * x / 2).exp() * p((-pi * x.exp()).exp())
    v[j] = v[-j] = val
v = acb.dft(v)

brackets = []
for j in range(1, last + 1):
    left, right = v[j - 1].real, v[j].real
    if (left > tol and right < -tol) or (left < -tol and right > tol):
        brackets.append(j)
assert len(brackets) == 298 and brackets[0] > 1
assert arb("0.15808") < v[0].real - tol and v[0].real + tol < arb("0.15809")
Path(__file__).with_name("idx").write_text(" ".join(map(str, brackets)) + "\n")
print("positive brackets, first and last right indices:", len(brackets), brackets[0], brackets[-1])
print("center (including analytic error): (0.15808, 0.15809)")
