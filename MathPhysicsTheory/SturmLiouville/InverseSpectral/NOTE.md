## Inverse spectral problems: recovering a potential from numbers

### Why only one unknown function

Spectral data are sequences of numbers. They cannot determine three functions $p,q,w$. The Liouville transformation
$$t=\int_a^x\sqrt{w/p}\,,\qquad \ell=\int_a^b\sqrt{w/p}\,,\qquad y=(pw)^{1/4}X$$
turns $(pX')'+qX=-\lambda wX$ into the normal form
$$y_{tt}+Q(t)\,y=-\lambda y\quad\text{on }[0,\ell],\qquad Q=\frac{q}{w}-(pw)^{-1/4}\,\frac{d^2}{dt^2}(pw)^{1/4},$$
with the same eigenvalues. The boundary coefficients change in a known way. Every triple $(p,q,w)$ with the same $\ell$, $Q$ and boundary coefficients therefore has the same spectrum. At most the normal form is recoverable from spectral data. So the problems in this module fix $p=1$, $w=1$ and take the potential $q$ as the only unknown. Other choices of "one unknown function" are possible. For example, with $p=1$, $q=0$ and $w$ unknown we get Krein's inverse problem for a string with unknown density.

### How much spectral data is needed

**One spectrum is not enough.** For Dirichlet conditions, $q$ and its mirror image $x\mapsto q(a+b-x)$ have the same spectrum. More is true (Pöschel–Trubowitz): the potentials with a given Dirichlet spectrum form an infinite-dimensional manifold, parametrised by the norming constants.

**A heuristic count.** Take $[0,\pi]$ with Dirichlet conditions and $q$ small. First-order perturbation theory (normalised eigenfunctions $\sqrt{2/\pi}\sin nx$) gives
$$\lambda_n\approx n^2-\frac1\pi\int_0^\pi q\,dx+\frac1\pi\int_0^\pi q(x)\cos 2nx\,dx .$$
So one spectrum gives the cosine coefficients $\int q\cos2nx$, $n\ge0$. These functions are symmetric about $\pi/2$, so the spectrum sees only the **even part** of $q$ about the midpoint. The rest of the module follows this count:

| problem | data | what supplies the odd part of $q$ | theorem |
|---|---|---|---|
| `SymmetricSpectrum` | one spectrum | nothing: the odd part is $0$ | Borg (1946) |
| `HalfKnownSpectrum` | one spectrum, $q$ on $[\frac{a+b}2,b]$ | the known half | Hochstadt–Lieberman (1978) |
| `TwoSpectra` | two spectra, different conditions at $b$ | the second spectrum | Borg (1946) |
| `SpectralData` | spectrum $\lambda_n$ and norming constants $\rho_n$ | the norming constants | Gelfand–Levitan (1951), Marchenko (1950) |
| `ambarzumian` | the single number $\lambda_0=0$ (Neumann) | the sign condition $q\le0$ | Ambarzumian (1929) |

The norming constant is $\rho_n=\int_a^bX_n^2w$, for the eigenfunction normalised by its Cauchy data at $a$ (`IsNormalizedEigenfunction`). It is the information an eigenfunction carries beyond its eigenvalue. Gelfand–Levitan keeps **one number per eigenfunction** instead of the whole function, as in `InverseProblem`.

### Where Steklov's expansion enters

All the uniqueness proofs rest on the completeness of the eigenfunctions, which is `steklov_expansion` in this library.

* **Gelfand–Levitan reconstruction.** Compare with $q=0$ (eigenvalues $\lambda_n^0$, norming constants $\rho_n^0$) and put
  $$F(x,t)=\sum_n\Big(\frac{\cos\sqrt{\lambda_n}\,x\,\cos\sqrt{\lambda_n}\,t}{\rho_n}-\frac{\cos\sqrt{\lambda_n^0}\,x\,\cos\sqrt{\lambda_n^0}\,t}{\rho_n^0}\Big).$$
  Solve the linear integral equation $K(x,t)+F(x,t)+\int_a^xK(x,s)F(s,t)\,ds=0$ for $a\le t\le x$. The potential is then $q(x)=-2\,\frac{d}{dx}K(x,x)$ (minus the classical formula, because of the sign convention $y''+qy=-\lambda y$). The equation is derived by expanding the transformation operator $\varphi(x,\lambda)=\cos\sqrt\lambda\,x+\int K(x,t)\cos\sqrt\lambda\,t\,dt$ in the eigenfunctions. That step uses the expansion theorem / Parseval's identity, which is Steklov's theorem.
* **Borg's two spectra.** For two potentials with the same spectral data, $q_1-q_2$ is orthogonal to the products $\varphi_n^{(1)}\varphi_n^{(2)}$ of eigenfunctions. Completeness of these products, proved through the expansion theorem, gives $q_1=q_2$.

So Steklov's theorem is what makes "numbers instead of functions" possible. It turns knowledge of the spectral measure (the $\lambda_n$ with weights $1/\rho_n$) into knowledge of the operator.

### Remarks on the formalisation

* **Sign of $q$.** `Admissible` uses the `Assumptions` of `Problem`, so $q\le0$ and the eigenvalues are $\ge0$. The uniqueness theorems hold on this smaller class too. Theorems that *characterise* spectral data, for example "every sequence $\lambda_n=n^2+c+\ell^2$-small is a Dirichlet spectrum", need $q$ of arbitrary sign. They would need an `Assumptions` without `q_nonpos`.
* **Endpoint derivatives.** `Robin.Operator.apply` uses the two-sided `deriv` at the endpoint, while eigenfunctions are only $C^2$ on $[a,b]$. For a proof by integration by parts (Ambarzumian, below) one wants the one-sided derivative `derivWithin`. Changing this would make such proofs possible.
* **Ambarzumian with $q\le0$.** Multiply $X_0''+qX_0=0$ by $X_0$ and integrate. With Neumann conditions, $-\int X_0'^2+\int qX_0^2=0$. Both terms are $\le0$, so $X_0'\equiv0$, so $X_0$ is a nonzero constant, so $q\equiv0$. For $q$ of any sign, the classical statement needs the whole spectrum: if $\lambda_n=(n\pi/(b-a))^2$ for all $n$, then $q=0$.
