"""Compare the prescribed step menu with the capped product on a toy interval."""

from math import prod


def factors(n):
    p = 2
    while p * p <= n:
        a = 0
        while n % p == 0:
            n //= p
            a += 1
        if a:
            yield p, a
        p += 1
    if n > 1:
        yield n, 1


def check_menu(limit, mask, eligible):
    # Enumerate all steps first, independently of the discrepancies tested.
    best = [None] * (limit + 1)
    for b in range(1, limit + 1):
        cost = 1
        for p, a in factors(b):
            if p in mask:
                continue
            if p in eligible and a >= 2:
                cost *= p
            elif p not in eligible and a >= 3:
                cost *= p**2
            else:
                break
        else:
            for i in range(1, limit // b + 1):
                n = b * i
                v = i * cost
                if best[n] is None or best[n] > v:
                    best[n] = v

    for n in range(1, limit + 1):
        expected = prod(p ** min(a, 1 if p in eligible else 2)
                        for p, a in factors(n) if p not in mask)
        assert best[n] == expected, (n, mask, eligible, best[n], expected)


def check_strict_example():
    # Exponent scale q=2^40; no prime is masked or eligible in this test.
    # Actual prime moduli and occupied columns are not needed for a menu test.
    p, r, u = 3, 5, 131071
    assert all(list(factors(x)) == [(x, 1)] for x in (p, r, u))
    n = p**3 * r**4 * u
    cap = p**2 * r**2 * u
    assert n**5 <= 2**156 and cap**5 <= 2**132 and (n // cap)**5 >= 2**24
    for k in range(3, n.bit_length() + 1):
        full = prod(x**a for x, a in ((p, 3), (r, 4), (u, 1)) if a >= k)
        assert full ** (5 * (k - 2)) < 2 ** (24 * k)
    return n


if __name__ == '__main__':
    for eligible in (set(), {2, 3, 11}):
        for mask in (set(), {3, 5}):
            check_menu(12000, mask, eligible)
    print('48000 menu minima checked; mixed-power discrepancy:', check_strict_example())
