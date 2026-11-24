"""Nominate (do not certify) a joint delete-33 law on a full first lattice.

See second-disk-cut-decision.md for the cut, replay, and exact checks.
The input provides atom sites only. The output uses the checker's format.
"""

import argparse
from pathlib import Path
import clarabel as cl
import numpy as np
import scipy.sparse as sp
from scipy.optimize import minimize
from numpy.polynomial.legendre import leggauss

UNIT = 10**9
C = np.cosh(1.95) / 3
CT = C / (2 * np.cos(np.pi / 12))
BASE = Path(__file__).resolve().parent


def readrows(path, K, M, d, thin):
    text = path.read_text()
    ix = text.index("\ntrace\n")
    old = {}
    for line in text[:ix].splitlines():
        if line and not line.startswith("#") and line != "prime":
            z, *row = map(int, line.split())
            old[z] = row[::2]
    knots = sorted(old)
    offsites = [0, 500000000, 707106781, 750000000, 875000000, 1000000000]
    start, end = -(400 // d) * K, (400 // d) * M
    keep = [
        z for z in knots if start < z < end and (not thin or (-900 <= z <= 600) or z % thin == 0)
    ]
    starts = np.array(sorted(set([start, 0, end] + keep)))
    sites = []
    for z in starts:
        i = np.searchsorted(knots, z, side="right") - 1
        row = old[knots[i]] if i >= 0 else offsites
        if z <= -900 or z == end:
            row = sorted(set(row + offsites))
        sites.append(row)
    return starts, sites


class Law:
    def __init__(self, table, K, M, d, thin):
        H = 1 / d
        self.r = R = np.exp(-H / 2)
        self.h = H
        self.S = np.array([-7, 6, 19]) * (d // 25)
        self.K, self.M = K, M
        self.starts, self.sites = readrows(table, K, M, d, thin)
        self.ix = np.arange(-M, K + 1)
        self.ns = len(self.starts)
        self.nk = len(self.ix)
        z = self.starts / 400
        # For slab j, mass in the translated coordinate at its left endpoint.
        width = np.r_[np.diff(z), np.inf]
        Ew = np.exp(-width)
        self.mass = np.exp(-z) * (-np.expm1(-width))
        self.offset = 1 - np.r_[width[:-1] * Ew[:-1], 0] / (-np.expm1(-width))
        self.wu = np.where(z >= 0, self.mass * (z + self.offset), 0)

        # F(k)=r^-k*p_k, and D(k)=F(k)-F(k-1) in a subtraction-free formula.
        def dramp(k):
            L = np.maximum(z, (-k) * H)
            U = np.minimum(z + width, (1 - k) * H)
            w = np.maximum(U - L, 0)
            ew = np.exp(-w)
            em = -np.expm1(-w)
            inside = np.exp(-L) * ((L + k * H + 1) * em - w * ew)
            L2 = np.maximum(z, (1 - k) * H)
            after = np.exp(-L2) * (-np.expm1(-np.maximum(z + width - L2, 0)))
            return inside + H * after

        D = np.stack([dramp(k) for k in np.r_[self.ix[1:], K + 1]])
        # Both signs in exp(-i*k*phi). At -M, p_{k-1}=r*p_k exactly.
        rv = R**self.ix
        self.coef = np.zeros((self.nk, self.ns))
        self.coef[0, -1] = R**M
        self.coef[0] = self.coef[0] - rv[0] * R**2 * D[0] / (1 - R**2)
        self.coef[1:] = rv[1:, None] * (D[:-1] - R**2 * D[1:]) / (1 - R**2)
        self.slope = H * self.mass
        self.weights_shape = np.r_[0, np.cumsum([len(s) for s in self.sites])]
        self.np = int(self.weights_shape[-1])
        self.wslab = np.repeat(np.arange(self.ns), np.diff(self.weights_shape))
        self.u = np.concatenate(self.sites) / UNIT
        x = 2 * self.u**2 - 1
        self.atoms = np.stack([x, 4 * x**3 - 3 * x])

    def chars(self, phi):
        phi = np.asarray(phi)
        v = np.exp(-1j * phi[:, None] * self.ix)
        e = self.r * np.exp(-1j * phi)
        tail = e ** (self.K + 1) / (1 - e)
        return v, tail

    def canonical(self, weights):
        A, B = (np.bincount(self.wslab, weights * w) for w in self.atoms)
        X = np.stack([A / CT, B / C])
        return X @ self.coef.T, X @ self.slope, self.wu @ np.bincount(self.wslab, weights * self.u)

    def traces(self, weights, phi):
        a, b, U = self.canonical(weights)
        z, tail = self.chars(phi)
        return a @ z.T + b[:, None] * tail, U

    def solve(self, phi, margin, quadratics, tangents):
        # Variables: prime weights, canonical a_t,b_t,a_3,b_3; b is slope.
        n = self.nk + 1
        total = self.np + 2 * n
        v, tail = self.chars(phi)
        v = np.column_stack([v, tail])
        nv = len(v)
        zero = lambda a, b: sp.csc_matrix((a, b))
        W = lambda q: sp.csc_matrix((q, (self.wslab, np.arange(self.np))), shape=(self.ns, self.np))
        can = sp.csc_matrix(np.vstack([self.coef, self.slope]))
        adj = sp.eye(n, format="csc")
        eq = sp.bmat(
            [
                [W(np.ones(self.np)), zero(self.ns, n), zero(self.ns, n)],
                [-can @ W(self.atoms[0] / CT), adj, zero(n, n)],
                [-can @ W(self.atoms[1] / C), zero(n, n), adj],
            ],
            format="csc",
        )
        mats = [eq, sp.hstack([-sp.eye(self.np, format="csc"), zero(self.np, 2 * n)], format="csc")]
        bs = [np.r_[np.ones(self.ns), np.zeros(2 * n)], np.zeros(self.np)]
        cones = [cl.ZeroConeT(self.ns + 2 * n), cl.NonnegativeConeT(self.np)]
        co = np.zeros((nv, 3, n))
        co[:, 1] = -v.real
        co[:, 2] = -v.imag
        co = sp.csc_matrix(co.reshape(-1, n))
        vb = np.tile([1 - margin, 0, 0], nv)
        for h in range(2):
            mats.append(
                sp.hstack(
                    [zero(3 * nv, self.np + h * n), co, zero(3 * nv, (1 - h) * n)], format="csc"
                )
            )
            bs.append(vb)
            cones.extend([cl.SecondOrderConeT(3)] * nv)
        if tangents:
            ex = np.stack([x for x, _ in tangents])
            bn = np.array([b for _, b in tangents])
            mats.append(
                sp.hstack([zero(len(tangents), self.np + n), sp.csc_matrix(ex)], format="csc")
            )
            bs.append(bn)
            cones.append(cl.NonnegativeConeT(len(tangents)))
        for matq, bb in quadratics:
            qn = len(matq) + 1
            aq = sp.csc_matrix(np.vstack([np.zeros(n), -matq]))
            mats.append(sp.hstack([zero(qn, self.np + n), aq], format="csc"))
            bs.append(np.r_[bb, np.zeros(qn - 1)])
            cones.append(cl.SecondOrderConeT(qn))
        mat = sp.vstack(mats, format="csc")
        rhs = np.concatenate(bs)
        obj = -np.r_[self.wu[self.wslab] * self.u, np.zeros(2 * n)]
        opts = cl.DefaultSettings()
        opts.verbose = False
        opts.max_iter = 55
        opts.tol_gap_abs = opts.tol_gap_rel = opts.tol_feas = 2e-10
        opts.max_threads = 3
        opts.direct_solve_method = "faer"
        opts.time_limit = 120
        print(
            f"model {len(phi)} angles, {self.ns} slabs, {total} vars, nnz={mat.nnz}, {len(tangents)}/{len(quadratics)} second cuts",
            flush=True,
        )
        solver = cl.DefaultSolver(sp.csc_matrix((total, total)), obj, mat, rhs, cones, opts)
        ans = solver.solve()
        print(
            f"{ans.status} iter={ans.iterations} sec={ans.solve_time:.2f} r=({ans.r_prim:.3g},{ans.r_dual:.3g}) obj={-ans.obj_val:.12g}",
            flush=True,
        )
        w = np.maximum(0, np.array(ans.x[: self.np]))
        den = np.bincount(self.wslab, w)
        return w / den[self.wslab]


def gauss(N, h):
    # Folded Poisson measure; clustered mesh, not an angle coverage test.
    edges = np.pi * (np.arange(N + 1) / N) ** 2
    x, w = leggauss(6)
    hh = np.diff(edges)[:, None] / 2
    phi = (edges[:-1, None] + hh * (1 + x)).ravel()
    wt = (
        (hh * w).ravel()
        * np.sinh(h / 2)
        / (2 * np.pi * (np.sinh(h / 4) ** 2 + np.sin(phi / 2) ** 2))
    )
    return phi, wt


class Second:
    def __init__(self, law, N):
        self.phi, self.wt = gauss(N, law.h)
        self.H = np.exp(1j * self.phi[:, None] * law.S)
        v, tail = law.chars(self.phi)
        self.v = np.column_stack([v, tail])
        self.W = self.wt[:, None] * self.H

    def fit(self, a, b, M=1):
        m = self.v @ np.r_[a, b]
        R = 1 - abs(m) ** 2
        m2 = m * m
        target = (self.W.T @ m2).real

        def fun(y):
            h = np.sum(self.H * y, axis=1)
            v = np.sqrt(1 + abs(h) ** 2)
            f = -y @ target + (self.wt * R) @ v
            g = -target + np.sum(self.W * (R * h.conj() / v)[:, None], axis=0).real
            return f, g

        # This convexity holds for admissible m. Tiny negative sampled R is
        # allowed during exchange, NOT in an admissibility claim.
        res = minimize(
            fun,
            np.zeros(3),
            jac=True,
            method="L-BFGS-B",
            bounds=[(-M, M)] * 3,
            options={"gtol": 3e-13, "ftol": 1e-15, "maxiter": 100},
        )
        lam = res.x
        h = self.H @ lam
        n = m2 - R * h.conj() / np.sqrt(1 + abs(h) ** 2)
        res2 = (self.W.T @ n).real
        print(f"  second: lambda={lam} smooth residual={res2} target={target}", flush=True)
        return lam, n, res2

    def quadratic(self, lam, need):
        lam = lam / max(abs(lam))
        h = self.H @ lam
        hmag = abs(h)
        d = (
            np.sqrt(2 * self.wt * hmag)[:, None]
            * (np.exp(0.5j * np.angle(h))[:, None] * self.v).real
        )
        return np.linalg.qr(d, mode="r"), np.sqrt((1 - need) * (self.wt @ hmag))

    def tangent(self, a, b, lam, need):
        z = np.r_[a, b]
        m = self.v @ z
        h = self.H @ lam
        ah = abs(h)
        f = np.sum(self.wt * ((h * m * m).real + ah * (abs(m) ** 2 - 1)))
        q = 2 * self.wt * (h * m + ah * m.conj())
        g = (q @ self.v).real
        return f, g, g @ z - f - need * np.sum(self.wt * ah)


def reconstruct(w, law, lam, degree):
    S, R = law.S, law.r
    # reflect the smooth n function, then cosine/sine Laurent coefficients.
    w = np.round(w * 10**13).astype(np.int64)
    wo = w / np.bincount(law.wslab, w)[law.wslab]
    rows = [
        [int(z), *[int(a) for pair in zip(s, w[l:r]) for a in pair]]
        for z, s, l, r in zip(law.starts, law.sites, law.weights_shape[:-1], law.weights_shape[1:])
    ]
    nt = 1 << int(np.ceil(np.log2(max(8 * degree, 4096))))
    phi = 2 * np.pi * np.arange(nt) / nt
    (t, m), obj = law.traces(wo, phi)
    h = np.exp(1j * phi[:, None] * S) @ lam
    n = m * m - (1 - abs(m) ** 2) * h.conj() / np.sqrt(1 + abs(h) ** 2)
    j = np.arange(-degree, degree + 1)
    den = 10**13
    nc = np.round(np.fft.ifft(n).real[j % nt] * den).astype(np.int64)
    res = (R ** np.abs(S[:, None] - j)) @ (nc / den)
    G = R ** np.abs(S[:, None] - S)
    cor = np.linalg.solve(G, res)
    n2 = np.zeros(nt, dtype=complex)
    n2[j % nt] = nc / den
    n2[S % nt] -= cor
    n2 = np.fft.fft(n2)
    slackt = (1 - abs(t)).min()
    slackm = (1 - abs(m)).min()
    slack2 = (1 - abs(m) ** 2 - abs(n2 - m * m)).min()
    print(
        f"Serialized surplus={obj - 8 / 9:+.9g}, nodal slacks(t,m,second)={slackt:+.9g},{slackm:+.9g},{slack2:+.9g}",
        flush=True,
    )
    if min(slackt, slack2, obj - 8 / 9) > 0:
        return (
            "# Prime: 400z then pairs (10^9 u, relative weight)\n"
            + "".join(" ".join(map(str, row)) + "\n" for row in rows)
            + "# Second: initial index, denominator, then consecutive numerators\n"
            + f"{j[0]} {den}\n"
            + "".join(" ".join(map(str, nc[i : i + 12])) + "\n" for i in range(0, len(nc), 12))
        )


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--denominator", type=int, choices=(25, 50), default=25)
    p.add_argument("--table", type=Path, default=BASE / "deletion-laws/delete-33-minus320.txt")
    p.add_argument("--grid", type=int, default=217)
    p.add_argument("--thin", type=int, default=64, help="outer slab spacing in 1/400 units")
    p.add_argument("--rounds", type=int, default=12)
    p.add_argument("--margin", type=float, default=7e-5)
    p.add_argument("--need", type=float, default=0.001)
    p.add_argument("--tangent", action="store_true", help="use linear cuts (replay control)")
    p.add_argument("--out", required=True, type=Path)
    args = p.parse_args()
    d = args.denominator
    law = Law(args.table, 112 * (d // 25), 110 * (d // 25), d, args.thin)
    sec = Second(law, 512)
    quad = np.pi * np.linspace(0, 1, args.grid) ** 2
    phi = np.unique(np.r_[np.linspace(0, np.pi, args.grid), quad[quad < 0.15]])
    grid = np.linspace(0, np.pi, 12289)
    tangents = []
    quadratics = []
    for _ in range(args.rounds):
        weights = law.solve(phi, args.margin, quadratics, tangents)
        a, b, _ = law.canonical(weights)
        lam, _, _ = sec.fit(a[1], b[1], 400.0)
        cap = (abs(lam) >= 0.999 * 400).any()
        _, g, rhs = sec.tangent(a[1], b[1], lam, args.need)
        cut = np.linalg.norm(lam) > 0 and (cap or g @ np.r_[a[1], b[1]] > rhs)
        if cut:
            if args.tangent:
                tangents.append((g, rhs))
            else:
                quadratics.append(sec.quadratic(lam, args.need))
        (t, m), _ = law.traces(weights, grid)
        mag = np.maximum(abs(t), abs(m))
        mx = []
        for z in (abs(t), abs(m)):
            k = np.flatnonzero((z[1:-1] > z[:-2]) & (z[1:-1] >= z[2:])) + 1
            mx.extend(k[z[k] > 1 - args.margin * 0.65])
        mx = np.array(sorted(set(mx), key=lambda j: -mag[j])[:300], dtype=int)
        new = grid[mx]
        new = new[np.min(abs(new[:, None] - phi), axis=1) > 1e-10]
        phi = np.unique(np.r_[phi, new])
        table = reconstruct(weights, law, lam, 1024 * (d // 25))
        if table is not None:
            args.out.write_text(table)
            return
        if not cut and not len(new):
            raise SystemExit("No sampled nomination and no new cuts or angles.")
    raise SystemExit("No sampled nomination within the solve budget.")


if __name__ == "__main__":
    main()
