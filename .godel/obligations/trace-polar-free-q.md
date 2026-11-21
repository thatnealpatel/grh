# The polar-free range needed for the local trace transfer

**Status: Provisional source comparison and a rational local obstruction, not a Lean result.** This checks an upstream premise of the [geometric trace handoff](trace-geometric.md), independently of the Chapter 13 divisor drafts. Both source readers checked text from the [pinned edition](../sources/masullo/README.md); the pages were not visually inspected.

## What Chapter 5 supplies

On p. 515, the proof of Theorem 12.4.1.1 claims that $R_\rho A(\varphi)$ factors through the half-weighted $S$-local theta image of $\mathcal S_{00}(A_{F,S})$. It identifies the image linearly and topologically with $|\cdot|_{F,S}^{1/2} \mathcal S_E(J_{F,S})$, citing Proposition 5.3.4.4 and n. 4 ("Return here after the Proposition is updated"). In the extracted proposition on pp. 263–264 there are only three equivalent conditions: Entireness on the specified isotype, existence of a flat lift with the same zeta transform there, and all-strip decay of the isotypic theta transform. Lemma 5.3.4.3, (5.3.4.2), pp. 261–263, gives a lift for the trivial isotype; its proof constructs it via tensor decompositions, not an operator factorization of $R_\rho A(\varphi)$. Even a topological identification of the theta image would not put the cutoff operator's outputs in it.

The next citation, Lemma C.3.2.2, (C.3.2.5), pp. 695–696, needs more than nuclearity on an ambient space or an identification of test spaces. For $T:E_1\hookrightarrow E_2$ a continuous injection of spaces with the approximation property, it requires a **nuclear** $A_0:E_2\to E_1$ with $A=T A_0$. It then compares the traces of $A$ and $A_0 T$. To apply it on p. 515 one must exhibit that factorization for the same cutoff operator whose trace is computed. Neither the Chapter 5 citation nor this abstract trace lemma establishes its range inclusion. This comparison does not rule out proving the topology assertion separately.

## The literal upper position cutoff does not supply the range

**Project calculation, $F=\mathbb Q$, $S=\{\infty\}$, trivial compact isotype.** Interpret the one-sided position cutoff on pp. 515–517 as a smooth upper cutoff $r(t)$ equal to one for all sufficiently small $t>0$, as in smoothing the upper endpoint of $\mathbf 1_{(0,\lambda]}$. This is not the annular cutoff of Definition 9.3.3.1, p. 427. Consider convolution on the half-weighted real Paley–Wiener level followed by multiplication by $r$. Up to a fixed nonzero normalization, the half-weighted theta image is $f\mapsto 2\sqrt t f(t)$ on even $f$, since the units are $\{\pm 1\}$. Its polar-free subspace comes from functions flat at zero, by (5.3.3.10), p. 252, and (5.3.4.1), p. 259. In particular, a positive-half-line function whose unweighted representative has a nonzero second derivative at zero cannot have a flat lift: The even part of any flat lift is flat.

For any bandwidth $Y>0$, choose a nonzero, even, nonnegative $b\in C_c^\infty((-Y,Y)\setminus\{0\})$. Put $u(\xi)=b(\xi)-2b(2\xi)$ and $f=\mathcal F^{-1}u$, with the $2\pi$ Fourier convention. The two terms have equal integrals, and $u(0)=0$. Thus $f(0)=0$ and $\widehat f(0)=0$. But

$$f''(0)=-4\pi^2\int_{\mathbb R}\xi^2 u(\xi)\,d\xi=-3\pi^2\int_{\mathbb R}\xi^2 b(\xi)\,d\xi\ne0.$$

With no auxiliary places, $f$ is already a generator satisfying the two moments in (7.3.2.12)–(7.3.2.17), pp. 354–355. Its theta image therefore survives the projection onto the closed level; no substitution of an additive Fourier multiplier for the level is needed for this test.

Under convolution by a test $\varphi\in C_c^\infty((1,2))$, the unweighted output before position truncation is, in the convention of (12.4.1.4) and the twisted convolution on p. 515,

$$h(t)=\int_0^\infty \varphi(g) g^{-1/2} f(t/g)\,\frac{dg}{g},\qquad h''(0)=f''(0)\int_0^\infty \varphi(g)g^{-5/2}\,\frac{dg}{g}.$$

The compact support in $g$ justifies the differentiation, and the last integral is nonzero for any nonnegative nonzero $\varphi$ in this class. Also $\varphi(1)=0$. Even if the two Mellin moments at $\pm 1/2$ are imposed, such a nonzero integral is possible: The three distinct powers $g^{-5/2},g^{-1/2},g^{1/2}$ are linearly independent on $(1,2)$, hence their integrations against $C_c^\infty((1,2))$ are independent functionals. The output is $2\sqrt t\,r(t)h(t)$. It agrees with $2\sqrt t\,h(t)$ near zero, so it does not belong to the half-weighted flat image. Mere inclusion of the Paley–Wiener generator in the two-moment kernel does not help.

This refutes range inclusion for the specified one-sided local operator, not the extracted trace formula for a different cutoff. It does not compute a trace or settle the global $S$-piece. An annular position cutoff does repair **range** for this example, since $r h$ then extends evenly with compact support away from zero. The next independent check is to prove a nuclear lift for the **actual fixed-annulus level operator** in this real model, keeping the level projection and the order of composition. Then compare its trace with the required joint-cutoff diagonal; a nuclear factorization alone would not authorize the Fourier replacement or removal of the lower cutoff. The [real joint-cutoff comparison](trace-joint-local-q.md) gives separate obstructions to that replacement.
