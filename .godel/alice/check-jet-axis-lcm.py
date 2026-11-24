"""Check the exact numerical prices in jet-axis-lcm.md."""

from fractions import Fraction as Q
from math import comb


def cubic_exponent(m, r):
    # Start with the quotient ranks and covolume counts of the two jet spaces.
    b = comb(m - 1, 2) - comb(r, 2)
    a = comb(m + 2, 2) - comb(r + 1, 2) - b
    S = comb(m + 2, 3) - comb(m - 1, 3) - comb(r + 1, 3) + comb(r, 3)
    L = comb(r + 1, 2) * (m - r + 1) - comb(r, 2) * (m - r - 1)
    V, R = comb(a, 2), r * a
    K = Q('.2696') * S + Q('2.110') * L - Q('.7998') * R - Q('.4044') * b
    return V, R, b, K


def check():
    V, R, b, K = cubic_exponent(10000, 1200)
    tau = Q('.0207')
    T = K - tau * V
    assert T / b == Q(23533757663, 123164002500)
    assert T / V == Q(759153473, 33444000000) < Q('.023')
    assert T / (V + R) == Q(23533757663, 1123164000000) < Q('.021')
    single = (K - tau * (V + R)) / b
    double = (K - tau * (2 * V + R)) / b
    assert single == Q(21745277663, 123164002500) > 0
    assert double == Q(284262863, 123164002500) > 0
    assert Q('.0024') - double == Q(11330743, 123164002500) > 0
    assert Q('.7198') * V > K  # No-crossing fallback with the full LCM.
    assert Q(1121, 8125) - (Q('.1276') + tau / 2) == Q(1, 52000)

    cap = 2 * (Q(1121, 8125) - Q('.1276'))
    assert cap == Q(337, 16250)
    A, B, C = Q('.2022') - 9 * cap, -Q('.2894') + 3 * cap, Q('.8672')
    linear, constant = Q('.0674') + cap, -Q('.1348')
    # Both expressions have degree at most two: a is linear, and the
    # cubic terms in S and L cancel. In (u,v) coordinates the three
    # values on each axis determine its restriction, and (1,1) fixes uv.
    for u, v in ((0, 0), (1, 0), (2, 0), (0, 1), (0, 2), (1, 1)):
        m, r = 3 + u + v, 1 + v
        V, R, _, K = cubic_exponent(m, r)
        expanded = A * m * m + B * m * r + C * r * r + linear * (3 * m - r) + constant
        assert K - cap * (2 * V + R) == expanded, (m, r)
    assert A > 0 and 4 * A * C - B * B > 0
    assert 8 * linear + constant > 0  # 3m-r >= 8.


if __name__ == '__main__':
    if not __debug__:
        raise SystemExit('Run without -O to check assertions.')
    check()
    print('Checked the axis-LCM prices and all-degree two-copy obstruction.')
