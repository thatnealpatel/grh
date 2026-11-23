#!/usr/bin/env python3
"""Exact certificates for high-endpoint-harmonics.md (standard library only)."""

from fractions import Fraction as F
from math import comb, factorial

M = F(8, 9)


def chebyshev(x, n):
    """T_0(x), ..., T_n(x)."""
    t = [1, x]
    for _ in range(2, n + 1):
        t.append(2 * x * t[-1] - t[-2])
    return t


def moments(u, w, n):
    assert len(u) == len(w) and all(0 <= x <= 1 for x in u)
    assert all(y > 0 for y in w) and sum(w) == 1
    values = [chebyshev(2 * x * x - 1, n) for x in u]
    return [sum(y * v[j] for y, v in zip(w, values)) for j in range(n + 1)]


def atomic(nodes, initial_weights, js, upper):
    # Recover the last two weights from mass one and mean M.
    u, w = list(map(F, nodes.split())), list(map(F, initial_weights.split()))
    left = 1 - sum(w)
    w.append((M - sum(x * y for x, y in zip(u, w)) - u[-1] * left) / (u[-2] - u[-1]))
    w.append(left - w[-1])
    assert sum(x * y for x, y in zip(u, w)) == M
    c = moments(u, w, max(js))
    assert all(abs(c[j]) < upper for j in js)


def positive(b, depth=0):
    # De Casteljau subdivision of a Bernstein polynomial at 1/2.
    if min(b) > 0:
        return 1
    assert depth < 30 and b[0] > 0 and b[-1] > 0
    left, right = [b[0]], [b[-1]]
    while len(b) > 1:
        b = [(x + y) / 2 for x, y in zip(b, b[1:])]
        left.append(b[0])
        right.append(b[-1])
    return positive(left, depth + 1) + positive(right[::-1], depth + 1)


def dual(active, other_coefficients, multiplier, lower):
    # The last signed coefficient makes the l1 norm exactly one.
    a = list(map(F, other_coefficients.split()))
    a.append((1 - sum(map(abs, a))) * (1 if active[-1] > 0 else -1))
    lam = F(multiplier)
    assert lam > 0 and sum(map(abs, a)) == 1
    assert all(j * aj > 0 for j, aj in zip(active, a))
    coeff = {abs(j): aj for j, aj in zip(active, a)}
    n = 2 * max(coeff)
    p = [lam * M - lower, -lam] + [F(0)] * (n - 1)
    prev, t = [1], [0, 1]
    for k in range(2, n + 1):
        nxt = [0] + [2 * x for x in t]
        for i, x in enumerate(prev):
            nxt[i] -= x
        prev, t = t, nxt
        if k % 2 == 0 and k // 2 in coeff:
            for i, x in enumerate(t):
                p[i] += coeff[k // 2] * x
    b = [sum(p[i] * F(comb(k, i), comb(n, i)) for i in range(k + 1)) for k in range(n + 1)]
    return positive(b)


# Data: (prefix, signed dual support, dual weights except last, multiplier,
#        primal nodes, primal weights except last two, lower, upper).
CASES = [
    (6, (1, -3, 6), '.980673900835295641 -.018210729102903977', '3.386647987848700283',
     '.853890275310016760 .985719071274225019', '', '.58702475785', '.58702475786'),
    (8, (1, -3, 6, -8), '.979793889974763509 -.018445562684079448 .001402935397663223',
     '3.377682704476077607', '.851718852889036571 .967357105748489014 1',
     '.708172827935998431', '.58709557246', '.58709557248'),
    (20, (1, -3, 6, -9, 11, -14, 17, -20),
     '.980227271013721719 -.018035486408649877 .001169974095017470 -.000339356128105081 '
     '.000156207620059150 -.000045031966513948 .000019318923981666',
     '3.384207945551764265', '.849602733973088424 .909439513472601037 .965988680799548218 '
     '.990779179794838806 1', '.667063345202722405 .069032508545263942 .103117691826249086',
     '.58712243824', '.58712243825'),
]


# Centers u_i and unnormalized weights for the box-smoothed law.
BOX = """
.99998758322 .00526843657   .99994643923 .00309155390   .99973330310 .00191564371
.99960580610 .02050800821   .99863135950 .01513077922   .99834181846 .00185044026
.99692894648 .01625338220   .99635670184 .00321542067   .99518878736 .00904725848
.99475701352 .00649461459   .99198533954 .00400912819   .99144373366 .02704157198
.98794324987 .01389421031   .98767472174 .00313377717   .98362439439 .00285608158
.98339909389 .02122378053   .97974077745 .02108611951   .97918041125 .00233262936
.97240654744 .01209187786   .97238418576 .00991384107   .96736940661 .00059948526
.96734512087 .02138935799   .95930827970 .01920919422   .95925414293 .00084436365
.95264828865 .02771919421   .91470762169 .00815315617   .91420345043 .02395194225
.91189746696 .00228493433   .89279533775 .00038531296   .89244972080 .02077732707
.88927175934 .01198245606   .86548052843 .01700844197   .86500006112 .01529300529
.84890432143 .40245389829   .84875232922 .22758937492
"""


def check_box():
    entries = list(map(F, BOX.split()))
    u, w = entries[::2], entries[1::2]
    total = sum(w)
    w = [y / total for y in w]
    h, upper, n = F(1, 125), F('.58712483'), 212
    assert (1 - h * h / 24) * sum(x * y for x, y in zip(u, w)) > M
    assert n * h <= 2 and 1 / ((n + 1) * h) < upper
    for j, cj in enumerate(moments(u, w, n)[1:], 1):
        x = j * h
        # sinc(x) is positive here and the Taylor sum through x^12 is an upper bound.
        sinc_upper = sum((-1)**k * x**(2*k) / factorial(2*k+1) for k in range(7))
        assert abs(cj) * sinc_upper < upper
    print('All harmonics < .58712483 for the box law: 1..212 exact, tail by 125/j.')


def check_single():
    # Isolate the original s_* and check the constants in the high-j shift argument.
    def equation(a):
        return (1 + a) * (1 + (4*a*a - 1)**2) - 9

    lo, hi = F('.86011432899420'), F('.86011432899422')
    assert equation(lo) < 0 < equation(hi)
    s_lo, s_hi = F('.58664126022350'), F('.58664126022352')
    assert s_lo < 1 - 2*(1 + hi)/9 < 1 - 2*(1 + lo)/9 < s_hi
    atomic('.9981798075 .9978503534 .9796716472 .9787422866 .9104311398 '
           '.9095083694 .8551607655 .8546174684',
           '.1505464289 .0325065441 .0095444913 .0210906321 .0421698943 .0326176912',
           [j for j in range(1, 18) if j != 6], F('.586846'))
    assert F('.586') < s_lo < s_hi < F('.586641265')
    r = F(1, 18**2)
    assert F(13, 24) + r < F('.586')  # cos(1) <= 1 - 1/2 + 1/24
    cost = F('.414') - (1 - r) * F('.586') * (F(1, 2) - r / 24)
    assert cost > 0 and F('.586641265') + r * cost < F('.587018')
    assert F('.587018') < F(CASES[0][-2])
    print('Best single added index is 6: other j <= 17 cap .586846, j >= 18 cap .587018.')


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('Run without -O to enable the certificate checks.')
    for n, active, a, lam, nodes, weights, lower, upper in CASES:
        assert all(1 <= abs(j) <= n for j in active)
        pieces = dual(active, a, lam, F(lower))
        atomic(nodes, weights, range(1, n + 1), F(upper))
        print(f'{tuple(map(abs, active))} and 1..{n}: ({lower}, {upper}), {pieces} Bernstein pieces.')
    check_single()
    check_box()
