"""Check the exact exponent prices in global-three-ratio.md."""

from fractions import Fraction as Q


def prices(radius):
    pivot, smooth = Q('.22'), Q('.5')
    slope = smooth - pivot
    first_height = Q('2.500')
    second_height = Q('3.165')
    divided_width = Q('2.110')
    w_cutoff = 2 * first_height - divided_width
    v_cutoff = 2 * second_height - divided_width
    mask = Q('.118')
    private = 2 * (Q('1.445') - (Q('4.220') - Q('3.960')) - Q('.115') - mask)
    usable = private - radius
    assert 0 <= usable <= w_cutoff
    first_output = smooth * w_cutoff - slope * usable

    # Cancel the pivot height between the two affine upper bounds.
    relation_weight = slope / smooth
    assert relation_weight * pivot == (1 - relation_weight) * slope
    v_crossing = pivot * v_cutoff
    second_output = v_crossing + relation_weight * (pivot * (2 * mask) + smooth * radius)
    assert second_output >= v_crossing

    pure_d = pivot * Q('2.110') + (smooth - 2 * pivot) * mask
    pure_d += Q('.390') + relation_weight * smooth * radius
    return first_output, second_output, pure_d


def check():
    radii = tuple(map(Q, ('.796', '.636', '.980')))
    assert tuple(prices(r)[i] for i, r in enumerate(radii)) == tuple(
        map(Q, ('1.13476', '1.1355552', '1.13568'))
    )
    common = max(prices(Q('.530')))
    assert common == Q('1.1058752')
    assert common + Q('.030') == Q('1.1358752') < Q('1.136')
    assert Q('.430') + (common + Q('.030')) / 2 == Q('.9979376')


if __name__ == '__main__':
    if not __debug__:
        raise SystemExit('Run without -O to check assertions.')
    check()
    print('Checked the three global ratio prices and the common-radius budget.')
