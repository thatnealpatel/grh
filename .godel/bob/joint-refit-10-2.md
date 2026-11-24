# Five translates at 3t by joint refitting

In the [(10,2) comparison](sparse-10-2.md) at $c=39/20$, five order-two translates at $3t$ suffice. The [fixed table](joint-refit-10-2.txt) lists $l,10^{10}b_{t,l},10^{10}b_{3t,l},10^{10}h_l$. Write $H_y=\sum_l b_{y,l}e^{ilx/25}$ and $h=\sum_l h_l e^{ilx/25}$. The only nonzero $h_l$ are:

| $l$ | $-9$ | $5$ | $19$ | $33$ | $55$ |
|---|---:|---:|---:|---:|---:|
| $10^{10}h_l$ | $-3586236$ | $-5334370$ | $-4303249$ | $-4283501$ | $1317896$ |

Use the [six-shift construction](sparse-10-2.md#the-two-finite-higher-order-measurements) with these new first masks: At $3t$ the measured multiplier is **$-(C_1/C_2)h$**; at $t$ use the same finite spatial sine kernel at $(L,N)=(1024,2048)$ with the new $b_{t,l}$ in its deconvolution. The Fourier-to-spline conversion multiplies each translated coefficient by $e^{-l/50}$. The largest $|l|$ in $H_t$ is $92$, so $|l|<L$ and $|l|+L-1<N$, the conditions needed for exact recovery of $H_t$. Orders 2 through 10 at $t$ do not contribute to the count at $3t$.

From the repository root, with assertions enabled:

```sh
sage .godel/bob/joint-refit-check-10-2.py
```

The checker encloses the lower prime price $P_0$, the actual finite $t$ allowance $T_{1024}$, and an upper bound for the $3t$ allowance $U(h)$, respectively, near $0.164079498523620$, $0.160771554607183$, and $0.003299099971038$. It checks **$P_0-T_{1024}-U(h)>8.84\cdot10^{-6}$** using the unrounded balls. The prime floor minimizes the same polynomial in the one shared $u\in[0,1]$ at both heights, incorporating $f_y(z)=\sum_l b_{y,l}e^{-l/50}(z+l/25)_+$. It uses endpoints and a second-derivative correction in $u$, radial chords between all knots and intervening nodes, and the endpoint and minimum slope separately on the upper radial tail. All ramps vanish on the omitted lower tail. The $3t$ allowance uses the [full folded trace and angular/spatial upper enclosures](sparse-10-2.md#verification-and-scope) for $C_1\int \max_\theta\Re(H_{3t}e^{i\theta}+he^{2i\theta})\,d\mu$. In particular the spatial fold includes the real-line tails; none of these bounds relies on an optimizer or sample-only acceptance test. The original six-term checker also reproduces its former output unchanged.

The signed upper price is $Q_t+Q_3<-8.84\cdot10^{-6}$ in the shallow comparison. As in the six-term result, fix the masks and take the iterated errors sufficiently small before using this as a screen at a sufficiently large actual failure. This gives no signed lower bound from failure alone.

## What joint refitting changed

The [fixed-support conic search](search-two-shift-10-2.py) frees both real first columns and the coefficients of $h$ on a chosen support. It retains the shared-prime minimum and the $3t$ support-function maximum of the [two-shift search](two-shift-dual-search.md). With `--L=1024` it prices the actual $t$ sum inside the cone (the norm rows use $b_{t,l}/d_{|l|}$, not $b_{t,l}$). The prime chords and averaged trace nodes used during the fit need not give a conservative combined margin. A separate floating reprice uses angular stationary roots and unmerged Gauss trace nodes, with both the finer radial chord and the optimistic radial barycenter. The resulting margins are nominations, not bounds on the best possible fit.

| First columns | $h$ support | finite margin, in $10^{-6}$ |
|---|---|---:|
| Both fixed to the paired table, numerical refit of $h$ | $-23,-9,5,19,33$ | $-18.66$ / $-17.59$ (chord / barycenter) |
| Both free on the **same 67 paired sites** | $-23,-9,5,19,33$ | $>3.848$ (certified) |
| Both fixed to the paired table, numerical refit of $h$ | $-9,5,19,33,55$ | $-24.71$ / $-23.63$ (chord / barycenter) |
| Both free on 143 tapered sites through $\pm92$ | $-9,5,19,33,55$ | $>8.84$ (certified) |

The fixed controls optimized only the second-order coefficients on dense numerical trace cells and repriced with the same finite $t$ construction; they are not certified fixed-first optima. The 67-site joint nominee used $10^{10}h_l=(-1517919,-2806150,-5625837,-4287361,-2926958)$ in the displayed support order. For that fixed rational table the checked prices were $P_0\approx .164061766375277$, $T_{1024}\approx .160760765606582$, $U_{\rm upper}\approx .00329715269829043$, giving $3.8480704\cdot10^{-6}$ of certified margin. This separates the benefit of joint refitting from enlarging the set of first-mask sites. The refined five-shift fit also tested $(-23,-9,5,19,33)$, $(-23,-9,5,33,55)$, and $(-23,5,19,33,55)$; the retained witness was the best on finite repricing.

## Four-shift successor

No four-shift nominee paid on finite repricing. Six finite fits on the 143-site first grid tested $(-9,5,19,33)$, $(-23,5,19,33)$, $(-23,-9,5,33)$, $(-23,-9,5,19)$, $(-21,1,17,34)$, and $(-14,2,18,34)$. The broader screens used 28 coarse supports (deletions and dispersed placements) and 10 completed local perturbations, and two completed expanded-grid fits through $\pm192$, on $(-9,5,19,33)$ and $(-11,4,19,34)$. The expanded nearest case $(-9,5,19,33)$ used an ideal-$t$ search but was repriced against the actual finite cost: $-3.56\cdot10^{-6}$ with radial chords, $-0.93\cdot10^{-6}$ with barycenters, numerically. On the same support the 143-site finite-$t$ fit repriced at $-4.18\cdot10^{-6}$ and $-1.85\cdot10^{-6}$, respectively. The coarse screen had returned a positive cell objective on that support, illustrating why it is not an acceptance test. These are selected fits, not a four-shift exclusion; three was not searched.

To start from the closest support and jointly refit on the larger grid **with** the finite price in the cone (a new proposed probe, not the completed expanded-grid run), use NumPy, SciPy and Clarabel:

```sh
p=.godel/bob/search-two-shift-10-2.py
OPENBLAS_NUM_THREADS=1 python "$p" --pairs='-9,5,19,33' --chord --L=1024 \
  --range=192 --stride=1 --taper --dz=.010 --dx=.10 --iter=8 --save /tmp/joint-four.npz
OPENBLAS_NUM_THREADS=1 python "$p" --check /tmp/joint-four.npz --L=1024 --freeze /tmp/joint-four.txt
```

If the frozen table reprices positively, invoke the checker with Sage's Python interpreter (in this installation, `/opt/sage-10.9/bin/python`):

```sh
/opt/sage-10.9/bin/python .godel/bob/joint-refit-check-10-2.py \
  /tmp/joint-four.txt --count 4 --margin 0.00000001
```

To rerun the certified five's search, use support `-9,5,19,33,55`, `--range=92 --dz=.012 --dx=.11` and the other fit settings above. The ball check of the fixed table, not agreement between solver runs, is the decisive test.
