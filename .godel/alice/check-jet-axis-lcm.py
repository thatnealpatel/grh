"""Check the exact numerical prices in jet-axis-lcm.md."""

from fractions import Fraction as Q
from math import comb


def check():
    m, r = 10000, 1200
    a = 3 * m - r
    b = ((m - 1) * (m - 2) - r * (r - 1)) // 2
    S = (3 * m * m - 3 * m + 2 - r * r + r) // 2
    L = r * m
    V, R = comb(a, 2), r * a
    tau = Q('.0207')
    K = Q('.2696') * S + Q('2.110') * L - Q('.7998') * R - Q('.4044') * b
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
    assert A > 0 and 4 * A * C - B * B > 0
    assert (Q('.0674') + cap) * 8 - Q('.1348') > 0  # 3m-r >= 8.


if __name__ == '__main__':
    if not __debug__:
        raise SystemExit('Run without -O to check assertions.')
    check()
    print('Checked the axis-LCM prices and all-degree two-copy obstruction.')
