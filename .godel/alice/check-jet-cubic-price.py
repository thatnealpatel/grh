"""Check the finite smooth-cubic screens in jet-quotient-determinant.md."""

from fractions import Fraction as Q


def jet_counts(degree, order):
    # Sum the monomial layers rather than using the closed binomial formulas.
    rank = sum(j + 1 for j in range(order, degree + 1))
    axis = sum(j * (j + 1) // 2 for j in range(order, degree + 1))
    height = sum((2 * degree - 3 * j) * (j + 1) // 2 for j in range(order))
    return rank, axis, height


def check():
    m, r, D, e = 10000, 1200, 3, 1
    box, height, common, crossing = map(Q, ('.1348', '2.110', '.7998', '.0207'))
    norm, axis, joint, overlap = map(Q, ('.192', '.108', '.080', '.073'))
    rank, axis0, height0 = jet_counts(m, r)
    b, axis1, height1 = jet_counts(m - D, r - e)
    a, S, L = rank - b, axis0 - axis1, height0 - height1
    assert (a, b, S, L) == (28800, 49265601, 149265601, 12000000)
    U, V1, V2 = Q(S, b), Q(r * a, b), Q(a * (a - 1) // 2, b)
    assert (U, V1, V2) == (Q(149265601, 49265601), Q(11520000, 16421867),
                           Q(138235200, 16421867))
    # A new modulus needs a new divisibility argument before changing this credit.
    T = 2 * box * U + height * Q(L, b) - common * V1 - crossing * V2 - box * D
    den = 123164002500
    assert T == Q(23533757663, den)
    assert U > 3 and U - V1 - 3 < 0 < U - V1 - 2

    margins = (
        ('norm screen', norm - T, Q(113730817, den)),
        ('one-axis I', (2 * U - V1 - 3) * axis - T, Q(7833330067, den)),
        ('one-axis II', (U - 1) * axis - T, Q(3466242337, den)),
        ('one-axis III', U * axis - box - T, Q(165447070, den)),
        ('joint', (2 * U - 3) * joint - V1 * overlap - T, Q(305922137, den)),
        ('joint isotropic fallback', 3 * crossing - (box - overlap), Q(3, 10000)),
        ('crossing budget', Q(1121, 8125) - (Q('.1276') + crossing / 2), Q(1, 52000)),
    )
    for name, actual, expected in margins:
        assert actual == expected and actual > 0, (name, actual, expected)


if __name__ == '__main__':
    if not __debug__:
        raise SystemExit('Run without -O to check assertions.')
    check()
    print('Checked the finite cubic screens, isotropic fallback, and crossing budget.')
