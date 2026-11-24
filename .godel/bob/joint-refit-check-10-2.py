"""SageMath: certify a fixed rational joint-refit (10,2) separator."""
import argparse
from pathlib import Path
from runpy import run_path

if not __debug__:
    raise SystemExit('Run with assertions enabled.')
base = Path(".godel/bob")
ap = argparse.ArgumentParser(description=__doc__)
ap.add_argument('table', type=Path, nargs='?', default=base / 'joint-refit-10-2.txt')
ap.add_argument('--count', type=int, default=5)
ap.add_argument('--margin', default='0.00000884')
args = ap.parse_args()
prime = run_path(str(base / 'check-paired-10-2.py'))
trace = run_path(str(base / 'check-sparse-10-2.py'))
F = prime['F']
assert prime['h'] == prime['QQ'](1)/25 and prime['c'] == prime['QQ'](39)/20
rows = [tuple(map(int, line.split())) for line in args.table.read_text().splitlines()
        if line.strip() and not line.startswith('#')]
assert all(len(row) == 4 for row in rows)
lattice, *columns = zip(*rows)
assert len(lattice) == len(set(lattice))
at, a3, b3 = ({k: F(v)/10**10 for k, v in zip(lattice, col) if v} for col in columns)
assert len(b3) == args.count
floor = prime['prime_floor']((at, a3), subdivisions=300, M=2048)
t_cost = trace['finite_t'](at, 1024)
third = trace['third_cost'](a3, b3)
margin = floor-t_cost-third
print('Order-two support at 3t:', sorted(b3))
print('Prime floor:', floor)
print('Finite t allowance:', t_cost)
print('3t allowance upper bound:', third)
print('Finite signed margin, lower bound:', margin)
assert margin > F(args.margin) > 0
