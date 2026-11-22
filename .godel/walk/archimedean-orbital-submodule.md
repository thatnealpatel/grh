# The introductory Archimedean convolution submodule

**Printed passage.** Masullo, *The Music of the Primes*, §1.2.10,
printed p. 19, from “The linear subspace” through “is a closed
$\mathcal D(J_{F,S})$-submodule.” The inclusion displays the
S-unit theta space on the Archimedean-flat test space on the left,
without a character restriction, and the chosen norm-one isotype of
the full S-local theta space on the right. The display and closing
words were spot-checked directly in rendered pixels of PDF page 19
of SHA-256
`e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5`,
separately from the chapter Markdown, PDF text extraction, and OCR.
The next test-function and trace assertions are not part of this
passage.

**Convolution stability after projection.** Let $H$ be the full
S-local theta isotype for a norm-one character $\omega$, with its
intrinsic topology, and let $q_\omega$ be theta followed by projection
to $H$. Use $M=q_\omega(\mathcal S_\infty)$ as the left side of the
inclusion. This interprets the missing projection in the printed
inclusion; it does not identify the unprojected theta space with a
subspace of $H$. Here the finite factors of $\mathcal S_\infty$ are
unrestricted, as in the [preceding definition](archimedean-orbital-quotient.md).

On the test space, $T_af(x)=f(a^{-1}x)$ for an S-idele $a$ preserves
each coordinate zero hyperplane and preserves flatness by the chain
rule. The convergent S-unit sum is translation equivariant by
commutativity, and the norm-one projection commutes with translation
because $J_{F,S}$ is abelian. Translation invariance alone only puts
the integrated action in the **closure** of $M$ if one integrates in
$H$. Instead, integrate on test representatives:

- The quotient of the S-ideles by the discrete S-units has local
  sections. Over the compact support of a test $\varphi$ on $J_{F,S}$,
  a finite partition of unity in such charts gives a compactly
  supported continuous lift whose S-unit periodization is $\varphi$.
- Integrating translates of one representative against this lift
  stays in $\mathcal S_\infty$. The finite-part translates of each
  finite test have finite orbit on a compact set of finite ideles,
  since the stabilizer is open. The resulting integral is thus a
  finite sum of integrals in the Archimedean Schwartz space, where
  flatness is an intersection of kernels of continuous derivative
  evaluations and is preserved by integration.
- The continuous equivariant map $q_\omega$ takes this integral
  to convolution by $\varphi$ on $H$, by Weil's quotient formula
  with counting measure on the S-units and compatible Haar measures.
  No support restriction over norms greater than one is needed for
  this preservation calculation.

This is the reviewer's check for the projected image under the
S-local quotient and integrated-action setup, not a formal proof of
the literal inclusion. The setup uses Masullo's §2.3 opening on p. 99,
Proposition 2.3.1.2(1) on p. 100, Proposition 5.2.3.2(1) on
pp. 236–237, and the quotient integral formula of Theorem D.1.2.1 on
p. 747. These later readings are provisional from chapter Markdown,
not rendered-page checks. No Lean declaration is used.

**Closedness remains open.** Integration within the flat test space
does not show that $M$ is closed in $H$. The missing step is the
closedness of $\mathcal S_\infty+\ker q_\omega$ in the full adelic test
space, or an equivalent closed-image argument. Theorem 7.3.4.1(1),(3)
concerns the closed all-place polar-free image in the finite-place
principal-value image, not $M$ in $H$. To use that theorem one needs
the comparison from the preceding note, identifying $M$ as the
preimage of that closed space under the actual descended
finite-place product. This passage checks convolution stability for
an interpretation but does not resolve Masullo's closed-submodule
assertion or its use in a Hausdorff trace quotient.
