"""Refit delete-33 from tabulated atom sites, with the ideal disk price at t.

One fixed-cut Price.solve, no enrichment. Prime rows are constant on half-open
slabs (the last is infinite), and the 512 reflected trace cells are constant
laws in angle. The input weights and input disk values are not used.
The output is a floating-point nomination, not an exact certificate.

Control and portability trial on table pin 766e1d844630083d0987c269b6903528be5f769e:
``--left -192 --right 192`` and ``--left -256 --right 256`` each used one solve
at tol=1e-11 and returned AlmostSolved. Serialized mean minus 8/9 was
+2.43198124e-5 and +2.42664807e-5 respectively; the largest serialized
balance errors in the floating model were 1.14e-9 and 6.08e-10. For the
subsequent exact checks and their scope, see table-fit-decision.md.
Tested with Python 3.12.3, NumPy 2.5.5, SciPy 1.18.1, Clarabel 0.11.1.
"""
import argparse
from collections import Counter
from hashlib import sha256
from pathlib import Path
from runpy import run_path
from time import perf_counter

import clarabel
import numpy as np
import scipy
from numpy.polynomial.legendre import leggauss

BASE = Path(__file__).resolve().parent
UNIT, WEIGHT, NCELL = 10**9, 10**11, 512
SECOND = np.array([-7, 6, 19])
# An equally spaced u grid and the u for X=0, rounded in table units.
NEW = sorted([j * (UNIT // 16) for j in range(17)] + [round(UNIT / np.sqrt(2))])


def read_sites(path):
    data = path.read_bytes()
    rows = [s for line in data.decode().splitlines() if (s := line.split('#', 1)[0].strip())]
    i = rows.index('trace')
    if rows[0] != 'prime' or len(rows[i+1:]) != NCELL:
        raise ValueError('expected prime rows followed by 512 trace rows')

    def atoms(fields):
        if not fields or len(fields) % 2 or min(fields[1::2]) <= 0:
            raise ValueError('expected nonempty site/positive-weight pairs')
        return fields[::2]

    prime = {}
    for row in rows[1:i]:
        z, *f = map(int, row.split())
        prime[z] = sorted(set(atoms(f)))
    if len(prime) != i-1 or not prime or any(not 0 <= h <= UNIT for a in prime.values() for h in a):
        raise ValueError('invalid prime starts or atom sites')
    circle = []
    for row in rows[i+1:]:
        _, _, *f = map(int, row.split())
        circle.append(sorted({h % UNIT for h in atoms(f)}))
    return prime, circle, sha256(data).hexdigest()


def make_price(source, indices, prime):
    # A constant law on a slab integrates each linear ramp exactly at its
    # exponential barycenter; including every knot makes clipping exact too.
    starts = sorted(prime)
    knots = sorted(set(starts) | set(-16 * indices) | {0})
    parent = np.searchsorted(starts, knots, side='right') - 1
    count = Counter(parent[parent >= 0])
    sites = [prime[starts[p]] if p >= 0 else NEW for p in parent]
    a = np.array(knots) / 400
    width = np.diff(a)
    mass = -np.expm1(-width)
    wz = np.exp(-a) * np.r_[mass, 1.]
    offset = np.r_[1 - width * np.exp(-width) / mass, 1.]
    delta = np.array(knots)[:, None] + 16 * indices
    ramp = np.where(delta >= 0, delta/400 + offset[:, None], 0)

    lo, hi = min(indices[0], SECOND[0]), max(indices[-1], SECOND[-1])
    edges = np.pi * (np.arange(NCELL + 1) / NCELL)**2
    x, w = leggauss(12)
    half = np.diff(edges)[:, None] / 2
    phi = edges[:-1, None] + half * (1 + x)
    # Folded Poisson density, evaluated without subtraction near phi=0.
    wt = half * w * np.sinh(.02) / (2*np.pi*(np.sinh(.01)**2 + np.sin(phi/2)**2))
    wx = wt.sum(axis=1)
    Z = np.einsum('ij,ijk->ik', wt, np.exp(1j*phi[:, :, None]*np.arange(lo, hi+1))) / wx[:, None]

    # Populate Price's existing barycenter/character interface directly;
    # its ordinary constructor would generate a different mesh.
    price = source['Price'].__new__(source['Price'])
    price.k, price.shift_bounds = indices/25, (lo, hi)
    price.P, price.v, price.wz = ramp * np.exp(-indices/50), np.maximum(a, 0) + offset*(a >= 0), wz
    price.Z, price.Zt, price.wx = Z, Z[:, indices-lo], wx
    price.Zcost, price.wt = price.Zt, wx
    price.fixed_t, price.fixed_cost = False, 0.
    print(f'slabs={len(knots)} unchanged={sum(c == 1 for c in count.values())} '
          f'subdivided_parents={sum(c > 1 for c in count.values())} '
          f'subdivision_children={sum(c for c in count.values() if c > 1)} '
          f'new={sum(parent < 0)} first_z400={knots[0]} tail_z400={knots[-1]} trace_cells={NCELL}')
    return price, knots, sites


def prime_moments(u):
    x = 2*u*u - 1
    return np.array([u, x, 4*x**3 - 3*x])


def circle_moments(turns):
    z = np.exp(2j*np.pi*turns)
    return np.array([z, z*z])


def distribution(rows, dual, scale, target, moments):
    cells = [[] for _ in target]
    for (i, x), z in zip(rows, dual, strict=True):
        cells[i].append((round(x*scale), z))
    lines, masses, drift, values = [], [], [], []
    for cell, mass in zip(cells, target, strict=True):
        h, z = zip(*cell)
        total = sum(z)
        p = np.maximum(z, 0)
        if not np.isfinite(total) or not p.sum() > 0:
            raise ValueError('missing positive dual mass in a cell')
        p /= p.sum()
        weights = np.rint(WEIGHT*p).astype(np.int64)
        lines.append(' '.join(f'{x} {n}' for x, n in zip(h, weights) if n > 0))
        masses.append(total/mass)
        prob = weights/weights.sum()
        drift.append(np.sum(abs(prob - z/mass)))
        values.append(moments(np.array(h)/UNIT) @ prob)
    print(f'  dual row mass relative error={max(abs(np.array(masses)-1)):.3g} '
          f'max row L1 change after normalization+rounding={max(drift):.3g} min dual={min(dual):.3g}')
    return lines, np.array(values).T


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--left', type=int, required=True)
    ap.add_argument('--right', type=int, required=True)
    ap.add_argument('--table', type=Path, default=BASE/'deletion-laws/delete-33.txt')
    ap.add_argument('--out', type=Path, required=True)
    ap.add_argument('--tol', type=float, default=1e-11)
    args = ap.parse_args()
    if args.left > args.right or args.out.resolve() == args.table.resolve() or not 0 < args.tol < 1:
        ap.error('need left <= right, an output distinct from the input, and 0 < tol < 1')

    start = perf_counter()
    prime, circle, digest = read_sites(args.table)
    source = run_path(str(BASE/'search-two-shift-10-2.py'))
    C, CT = source['C'], source['CT']
    indices = np.arange(args.left, args.right+1)
    price, knots, sites = make_price(source, indices, prime)
    tau = 2*np.pi
    U = {(i, h/UNIT) for i, row in enumerate(sites) for h in row}
    W = {(i, tau*h/UNIT) for i, row in enumerate(circle) for h in row}
    print(f'table_sha256={digest} numpy={np.__version__} scipy={scipy.__version__} clarabel={clarabel.__version__}')
    print(f'first=[{args.left},{args.right}] ({len(indices)} at each of t and 3t) '
          f'second_at_3t={SECOND.tolist()} prime_cuts={len(U)} trace_cuts={len(W)} tol={args.tol:g}', flush=True)
    fit, _, ((u, w), result) = price.solve(SECOND/25, 1, args.tol, (U, W), return_duals=True)
    print(f'status={result.status} iterations={result.iterations} solver_seconds={result.solve_time:.3f} '
          f'r_prim={result.r_prim:.3g} r_dual={result.r_dual:.3g}')
    print(f'primal_obj={result.obj_val:.15g} dual_obj={result.obj_val_dual:.15g} '
          f'dual_surplus={result.obj_val_dual - 8/9:.12g}')
    if fit is None:
        raise SystemExit('No nomination: Price rejected the solve status or objective.')

    # Cone stationarity: prime row mass = wz; circle row mass = C*wx;
    # SOC row = CT*wx*(1, -Re(t), Im(t)). Only the final solved cut lists
    # are aligned with z, not the updated warm sets returned by Price.
    dual = np.array(result.z)
    ne = 2*len(knots) + 4*NCELL
    assert len(dual) == ne + 3*NCELL + len(u) + len(w)
    if not np.isfinite(dual).all():
        raise SystemExit('No nomination: nonfinite cone duals.')
    disk = dual[ne:ne+3*NCELL].reshape(-1, 3)
    t = disk[:, 1:] * [-1, 1] / (CT*price.wx[:, None])
    norm = np.linalg.norm(t, axis=1)
    grid_t = np.rint(UNIT*t / np.maximum(1, norm/(1 - 1/UNIT))[:, None]).astype(np.int64)
    print(f'disk max raw norm={norm.max():.12g} max serialization change='
          f'{np.linalg.norm(grid_t/UNIT - t, axis=1).max():.3g}')
    cut = ne + 3*NCELL
    print('prime:')
    prows, (avg_u, avg_a, avg_b) = distribution(u, dual[cut:cut+len(u)], UNIT, price.wz, prime_moments)
    print('circle:')
    wrows, (m, n) = distribution(w, dual[cut+len(u):], UNIT/tau, C*price.wx, circle_moments)
    mean = (price.v*price.wz) @ avg_u
    t = (grid_t[:, 0] + 1j*grid_t[:, 1])/UNIT
    # Diagnostic in the same floating model, including normalization and rounding.
    err_t = price.P.T @ (price.wz*avg_a) - CT*(price.Zt.T @ (price.wx*t)).real
    err_3 = price.P.T @ (price.wz*avg_b) - C*(price.Zt.T @ (price.wx*m)).real
    err_2 = (price.Z[:, SECOND-price.shift_bounds[0]].T @ (price.wx*n)).real
    err = [np.max(abs(a)) for a in (err_t, err_3, err_2)]
    print('serialized max balance errors (t, 3t, second):', *(f'{e:.3g}' for e in err))
    args.out.write_text(
        '# z*400 then pairs: u*10^9, positive relative weight.\n'
        f'# Numerical nomination: both first spans [{args.left},{args.right}], second [-7,6,19].\nprime\n'
        + ''.join(f'{z} {row}\n' for z, row in zip(knots, prows, strict=True))
        + '# t unit-disk coordinates times 10^9; then pairs: turns*10^9, positive relative weight.\ntrace\n'
        + ''.join(f'{a} {b} {row}\n' for (a, b), row in zip(grid_t, wrows, strict=True)))
    print(f'wrote={args.out} serialized_mean={mean:.15g} serialized_surplus={mean-8/9:.12g} '
          f'wall_seconds={perf_counter()-start:.3f}', flush=True)


if __name__ == '__main__':
    main()
