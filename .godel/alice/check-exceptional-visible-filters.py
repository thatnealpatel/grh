"""Check exact exponents in exceptional-visible-filters.md."""

from fractions import Fraction as F
from math import comb


def check():
    tau = F(".159")
    lo = F(".446")
    hi = F(".780") - 2 * tau
    degree, actual, norm_degree = 8, 37, 12
    columns = comb(degree + 2, 2)
    assert columns - 2 - actual == 6  # Supplementary grid rows.
    assert columns - (1 + actual) == 7 > comb(degree - 6 + 2, 2)
    total_k = comb(degree + 2, 3)
    reserved_k = 2 * degree - 1
    norm_power = F(comb(norm_degree + 2, 3), comb(norm_degree - 5 + 2, 2))
    assert norm_power == F(91, 9)

    def determinant_exponent(sigma):
        return (
            (hi - sigma) * total_k
            + F("2.110") * reserved_k
            - (F("2.110") - tau - sigma) * degree
            - (F(".760") - tau) * actual
        )

    def restriction_margin(sigma):
        d = F("2.110") + tau - sigma
        return d - (norm_power * (hi - sigma) + 2 * tau + 3 * sigma)

    assert hi == F(".462")
    largest_filter_factor = (F("2.110") + tau - lo) / 2
    assert F("1.212") - (hi - lo) - largest_filter_factor > F(".28")
    assert determinant_exponent(lo) == -F(".707")
    width = hi - lo
    assert determinant_exponent(hi) == determinant_exponent(lo) - 112 * width
    assert restriction_margin(lo) == F(47, 9000)
    assert restriction_margin(hi) == restriction_margin(lo) + F(55, 9) * width
    small_price = F("1.055") + tau / 2
    large_price = F("1.055") + (F(".780") - hi) / 4
    assert small_price == large_price == F("1.1345") < F("1.1354")
    print("degree-eight quotient: -.707; binary margin: 47/9000; price: 1.1345")


if __name__ == "__main__":
    check()
