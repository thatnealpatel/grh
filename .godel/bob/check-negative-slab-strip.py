"""Replay the fixed-A negative-slab strip with SageMath from the repo root."""
from hashlib import sha256
from pathlib import Path
from runpy import run_path

from sage.all import QQ

if not __debug__:
    raise SystemExit('Run with assertions enabled.')

# Pin the executable inputs from d15c01a4fdc2f34b5a35fca5f3eee16a2a91c0ab.
ROOT = Path('.godel/bob')
PINS = {
    'check-half-gap-mixture.py': '74a14d3ce2ef4dd0377e328b1b5686d6b1036424c5253eb6fbbdf848d2a54940',
    'check-two-term-10-2.py': '43f3b08e01bb2c3f55720c907ca0a799d46534d62165f688698d86077534b6c0',
    'check-single-shift-10-2.py': '105730fd46632724589fdb90aaab2e015c70a57f14275abf94e98dac8bcfed79',
    'check-two-height-radial-witness.py': '11a2eea673ed55b675e8bb94d4e62a4fdbc9be2d3d615a0663e5b23ee920cb75',
    'hard-pair-10-2.txt': 'f8eb1b3ba222cc1884685c2a8ad2b32d7abe47fac5edae8ae6ec50c133c3d713',
    'single-shift-10-2.txt': '9bbe428c71c274b8ce2fa0aa43cc3c72d708058d48c7a15f13588640fd306c70',
}
for name, digest in PINS.items():
    assert sha256((ROOT / name).read_bytes()).hexdigest() == digest, name

base = run_path(str(ROOT / 'check-half-gap-mixture.py'))
z, A, B, H, F = (base[k] for k in ('z', 'A', 'B', 'H', 'F'))
assert base['surplus'] > F(QQ(948)/10**10)

# Add these millionths to B on the 184 negative slabs, in increasing
# left-endpoint order, and clip to the exact feasible interval at fixed A.
# This is witness data, not a floating-point optimizer dependency.
DELTAS = (
    21, -8, -29, -27, 32, 55, 9, -69, -78, 47, 116, 73, -120, -182, -20, 154,
    231, -2, -81, -185, -177, -215, -5, 788, 619, 113, -1518, -853, 1838, 527, -1007, -9713,
    1018, 8871, 7055, 17203, 41121, 8912, -8010, -8238, -7067, -41333, -93877, -115566, -87135,
    -27140, 21226, 21935, -24710, -34441, -52134, -53820, 151731, 215241, 232714, 106234, 4624,
    31485, 131886, 145254, 153527, 119606, -31441, -428307, -70417, -832139, -427889, -413165,
    -135474, 136051, 38548, -5296, -4573, -5288, -13713, -183120, -183845, 32723, 24259, 18934,
    15073, 15077, 30119, 82353, 179095, 694330, 153594, 24, 26, 25, 25, 25, 24, 24, 24, 23,
    23, 23, 23, 23, 23, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22,
    22, 22, 22, 300, 2616, 1228, 380, 257, 3453, 1418, 633, 53, 3725, 1456, 573, 254,
    2185, 961, 191, 194, 1251, 339, 384, 1311, 1626, 405, 227, 1128, 766, 112, 481, 2330,
    550, 172, 1028, 2783, 160, 818, 1827, 1828, 163, 163, 163, 163, 163, 163, 163, 162,
    162, 162, 162, 162, 162, 162, 162, 162, 162, 162, 162, 162, 162, 162, 162, 162,
    162, 162, 162, 162, 162, 162, 162, 162,
)
assert len(z) == 429 and z.index(0) == len(DELTAS) == 184


def cubic(x):
    return 4*x**3-3*x


def two_atoms(a, x, y):
    """Law with mean a supported on x < y; entries are (atom, mass)."""
    assert x <= a <= y and x < y
    return [(x, (y-a)/(y-x)), (y, (a-x)/(y-x))]


half = QQ(1)/2
changed = B.copy()
interior = 0
for j, delta in enumerate(DELTAS):
    a = A[j]
    assert z[j+1] <= 0 and -1 <= a <= 1
    lo = QQ(-1) if a <= half else cubic(a)
    hi = QQ(1) if a >= -half else cubic(a)
    assert lo <= B[j] <= hi
    b = min(hi, max(lo, B[j]+QQ(delta)/10**6))
    interior += lo < b < hi

    # Reconstruct the angular law independently of the clipping formulas.
    low = two_atoms(a, QQ(-1), half) if a <= half else [(a, QQ(1))]
    high = two_atoms(a, -half, QQ(1)) if a >= -half else [(a, QQ(1))]
    lam = (b-lo)/(hi-lo) if lo < hi else QQ(0)
    law = [(x, (1-lam)*p) for x, p in low] + [(x, lam*p) for x, p in high]
    assert all(-1 <= x <= 1 and p >= 0 for x, p in law)
    assert sum(p for x, p in law) == 1
    assert sum(p*x for x, p in law) == a, (z[j], law, a)
    changed[j] = sum(p*cubic(x) for x, p in law)
    assert changed[j] == b, (z[j], law, b)

assert changed[len(DELTAS):] == B[len(DELTAS):]
assert interior > 0
print('Fixed-A fitted slabs:', len(DELTAS), '; strict interior moments:', interior, flush=True)

# certify_cap also compares direct slab integration to the jump formula.
cap = QQ(119)/100
assert cap < H['C1']
H['certify_cap']('negative fit B', changed, cap, z)
base['check_strip'](changed, QQ(13)/25, QQ(663)/1000)
