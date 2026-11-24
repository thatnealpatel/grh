# The half-step first lattice does not separate delete-33

At $c=39/20$ in the $(10,2)$ comparison, allow arbitrary finite real first masks on $\mathbb Z/50$ at both $t$ and $3t$. Keep the three physical second sites $(-7,6,19)/25$ at $3t$. Every priced margin in this class is less than $-8.7091\times10^{-7}$, including for the finite positive-mask prices on their recoverable frequencies. This is a **joint refit**: The [coarse-lattice law](full-lattice-deletion-33.md) failed even the two first caps on this lattice.

Use the [426-row integer table](deletion-laws/delete-33-half-step.txt) with the same prime conventions. The [bilateral inverse and price proof](full-lattice-deletion-33.md) applies with $h=1/50$, $r=e^{-1/100}$, and second indices $S=(-14,12,38)$. Specifically, for each normalized prime step target $f_k$ form the full sequence $a_k=((1+r^2)f_k-r(f_{k-1}+f_{k+1}))/(1-r^2)$. Below $-220$ it is zero, and above $224$ it is a geometric tail. Convolution with $r^{|k|}$ gives $f_k$ on all of $\mathbb Z$ because the three-term difference of that kernel is the unit mass. This gives both first fields, not just their values on a finite range. In the Gram repair of the supplied second field the adjacent correlation is $r^{26}$, the same physical correlation as before. Subtracting the three Gram coefficients makes the second replies zero identically.

The [ball checker](check-full-deletion-33.py) evaluates the original step integrals. It bounds the tail after $J=3072$ and uses $N=524288$ angles with the derivative and chord losses in the coarse proof. The first $t$ slack is greater than $4.0284\times10^{-6}$; the actual joint $3t$ disk slack is greater than $3.5239\times10^{-6}$ after a Gram correction of norm less than $4.229\times10^{-10}$. These inequalities realize a single conditional circle law at $3t$ and the twelve-angle reply at $t$. The failure mean minus $8/9$ is $8.70912505843\ldots\times10^{-7}$; the margin upper bound is its negative. On each nonnegative slab the trace constraints use only $A,B$, not $U$. A rational three-site refit at exactly the same $A,B$ increased $U$ on 210 slabs. This improved the unpolished surplus $4.33099888531\ldots\times10^{-8}$ without changing either first field or the second polynomial. The first pass with only $262144$ angles did not certify the second disk with the global chord estimate. Doubling $N$ reduces that interpolation loss by four without changing the law.

Replay from the repository root with SageMath 10.9 and assertions enabled:

```sh
/opt/sage-10.9/bin/python .godel/bob/check-full-deletion-33.py --denominator 50
```

The [search decision and nomination command](second-disk-cut-decision.md) are not part of the certificate. Do not repeat the half-step refit. The scope is this lattice and these second shifts, not arbitrary real first translates, the unrestricted three-versus-four minimum, or an arithmetic lower bound.

## Where this witness stops

Keep these primes and ask about the full $k/100$ first lattice. At $t$, the same exact stencil and geometric tail with $h=1/100$ give modulus $>1.00181$ at $\varphi=2\pi(1898/131072)$. Reflection and folding as in the coarse proof make the normalized representer unique. The violation is of the ideal first cap for **these primes**. For arbitrary real shifts the [unfolded first representer](single-shift-10-2.md) is

$$v_t(x)=\frac{\sum_z \Delta A(z)\exp(-z/2+ixz)}{C_t(1/2+ix)}.$$

Its modulus exceeds $1.00251$ at $x=200\pi(1901/131072)$. Both point evaluations are in the checker above. Next try a joint refit with this unfolded representer, imposing the actual three second constraints against the unfolded measure. Test a serialized law on all real frequencies, including its tail. This targets arbitrary first translates rather than another dyadic refinement. A failure of the fit or of one fixed-law cap would not give a separator.
