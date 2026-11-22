# Short tests separating the rational global and joint local traces

**Scope:** Paper calculation for the project models, not a Lean theorem or an identification of a manuscript shell. Work in the rational trivial compact isotype, at one of the common good widths $0<\alpha<1/2$ and even degree $s=2r\ge4$. Write $M_f(z)=\int e^{zx}f(x)\,dx$. Write $G(f)$ for the trace of the whole global composition, taking the band limit **at fixed position cutoff**, retaining the terminal geometric projection, and then exhausting position. Write $U(f)$ for the [joint local projection limit](trace-joint-local-q.md), with its own specified cutoffs. We compare numbers, without exchanging these limits. The tests below may depend on the width and omitted divisor; no knowledge of their numerical locations is required.

Take any nonempty open interval $I\subset(0,\log 2)$. For tests supported in $I\cup(-I)$ there are no finite prime-power samples or identity terms. The [global model calculation](trace-hardy-diagonal-q.md#removing-the-order-defect-in-the-weighted-rational-isotype) gives $G(f)=-Z_{\rm strip}(f)$, counting full orders *inside* the strip. The [normalized rational explicit formula](rational-explicit-formula.md#checked-rational-radial-idelic-explicit-formula) gives

$$-Z_{\rm full}(f)=\int T(|x|)f(x)\,dx,\qquad T(t)=j(t)-2\cosh(t/2),\qquad j(t)=\frac{e^{-t/2}}{1-e^{-2t}}.$$

Here $j$ includes the two real signs with half Haar measure; the cosh is the pair of polar terms. For $t>0$ the two local densities at $t,-t$ are $h(t),e^{\beta t}h(t)$ respectively, with $\beta=2\alpha$ and $h(t)=j(t)-e^{-t/2}$. In particular the local density on even tests is the average $S(t)=(1+e^{\beta t})h(t)/2$.

## A positive-log calibration with no omitted-zero residual

There is a real $b\in C_c^\infty(I)$ with $M_b(1/2)>0$ such that $f=b'$ annihilates every omitted sample. For this test one obtains the unsplit calibration

$$G(f)-U(f)=-M_f(1/2)=\tfrac12M_b(1/2)>0.$$

Indeed the local density on this ray lacks only $e^{-t/2}$ relative to $j$, and the full and strip sums agree on $f$. This isolates the missing moment without assuming the strip contains every zero. It does not assign that moment to the $S$-part of a lifted diagonal.

Here is the construction, also used below. For the distinct omitted $w_j=a_j+i\gamma_j=\rho_j-1/2$ the [fixed-width zero-density bound](trace-carving-weight-q.md#the-short-window-detects-any-omitted-zero) gives $\sum_{|\gamma_j|>1}|\gamma_j|^{-1}<\infty$. This does **not** hold for the full divisor. Split off a finite conjugation- and negation-stable set so the sum of $d_j=\pi/|\gamma_j|$ on the tail is smaller than any reserved support slack. Convolve the tail probabilities

$$\mu_j=\frac{\delta_0+e^{-a_jd_j}\delta_{d_j}}{1+e^{-a_jd_j}}.$$

Their convolution $\mu$ is the law of the sum of independent displacements bounded in total by $\sum d_j$. Its Mellin transform vanishes at each tail location by the corresponding factor, and is positive on the real axis. Empty tail means $\delta_0$. Let $P_0(z)=\prod_{j\,\mathrm{finite}}(z+w_j)$; this is real. For a real nonnegative nonzero bump $\phi$ with room for the displacements, put $b=P_0(\partial_x)(\mu*\phi)$. The moment multiplier is $P_0(-z)M_\mu(z)$. Since $|\Re w_j|<1/2$, $M_b(1/2)\ne0$; change the overall sign if necessary. Differentiation kills mass, preserves the sample zeros, and does not enlarge support. Only values, not jets, are needed to eliminate terms in a sum weighted by orders. This construction need not keep $b\ge0$: If any omitted nonreal $w$ exists, no nonzero nonnegative smooth $b$ of support diameter at most $\pi/|\Im w|$ kills it. Rotate the phase about the support midpoint and take real parts; the integrand has strictly positive cosine in the interior.

## Even tests rule out repair by reflection averaging

There exists a real **even** $f\in C_c^\infty(I\cup(-I))$ with $M_f(0)=M_f(1/2)=M_f(-1/2)=0$, vanishing at every omitted Mellin sample, for which $G(f)\ne U(f)$. Thus neither removing odd tests, averaging the local answer with its reflection, nor adding either polar moment to that average restores equality. This goes beyond an odd-test asymmetry: The defect survives on the reflection-invariant test space even after eliminating the unknown full-minus-strip residual.

To see this, put $E=S-T$. Cancellation of the $n=0$ term in $j$ gives, for $t>0$,

$$E(t)=e^{t/2}+\frac12\sum_{n\ge1}\left(e^{(\beta-2n-1/2)t}-e^{(-2n-1/2)t}\right).$$

Use the measure and finite polynomial above, now setting $P(z)=z(z^2-1/4)P_0(z)$ and $g=P(\partial_x)(\mu*\phi)$. For $f(x)=g(x)+g(-x)$ all required moments vanish, since the omitted set is invariant under negation. For the remaining pairing, integration by parts and translation give

$$\tfrac12(U(f)-G(f))=\int E(x)g(x)\,dx=\int\phi(y)K(y)\,dy,\qquad K(y)=\int (P(-\partial)E)(y+t)\,d\mu(t).$$

This $K$ is real analytic for $y>0$: The exponential series after differentiation converges normally on $\Re y\ge\delta>0$ after the single growing term is killed, uniformly for $t$ in the support of $\mu$. Its largest surviving exponent is $\lambda=\beta-5/2$ with coefficient $P(-\lambda)M_\mu(\lambda)/2\ne0$. Indeed $0<\beta<1$ separates it strictly from all subsequent exponents, $-\lambda>3/2$ is not a polynomial root, and the real transform of the probability is positive. Dividing by $e^{\lambda y}$ and letting $y\to+\infty$ proves $K\not\equiv0$. In any open subinterval of $I$ leaving the chosen support slack, $K$ therefore has constant nonzero sign on some smaller interval. Choose $\phi$ nonnegative, nonzero, and supported there. This proves the assertion without a numerical zero search or RH.

**Manuscript consequence and limitation:** A repair that makes the entire global trace equal to this local projection with only polar corrections cannot work on the two-sided class of §12.5. There is no inference that the actual $S$-piece is that projection or that the actual orbital tail is zero. The latter needs a [shell-preserving Haar lift](trace-orbital-q.md#main-cutoff-test-no-haar-lift-of-the-literal-shell-kernel); a [separate circle diagnostic](trace-orbital-band-edge-q.md) tests the possible ambiguity of choosing quotient lifts instead.
