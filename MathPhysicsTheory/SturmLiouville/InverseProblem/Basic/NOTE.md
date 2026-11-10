## Solving the inverse problem: a solution method

### The method in general form

**Data.** An interval $[a,b]$, Robin (e.g. Dirichlet) boundary conditions, eigenvalues $\lambda_0<\lambda_1<\lambda_2<\cdots$ and eigenfunctions $X_n\in C^2[a,b]$, $X_n\not\equiv 0$. They are the eigenpairs of some Sturm-Liouville problem.

**Unknowns.** $p\in C^1$, $p>0$; $q\in C^0$, $q\le 0$; $w\in C^0$, $w>0$, with
$$(p\,X_n')' + q\,X_n + \lambda_n\,w\,X_n = 0 \qquad (n = 0,1,2,\dots).$$

The idea is that the equation looks like a differential equation for $p$, but is in fact a *linear algebraic* equation for the values of the coefficients at a point. Everything below is done step by step.

#### Step 1. Expand the operator

Since $p\in C^1$ and $X_n\in C^2$, $(pX_n')' = pX_n'' + p'X_n'$, so
$$p\,X_n'' + p'\,X_n' + q\,X_n + \lambda_n w\,X_n = 0 .$$

#### Step 2. Divide by $p>0$ and rename the unknowns

Put
$$\alpha = \frac{p'}{p},\qquad \beta = \frac{q}{p},\qquad \gamma = \frac{w}{p}.$$
Then for every $n$ and every $x$
$$X_n'' + \alpha\,X_n' + \beta\,X_n + \lambda_n\gamma\,X_n = 0. \tag{1}$$
*Why this helps:* for a fixed $x$ the numbers $X_n(x),X_n'(x),X_n''(x)$ and $\lambda_n$ are known (they are the data), and (1) is **linear** in the three unknown numbers $\alpha(x),\beta(x),\gamma(x)$. Nothing has to be integrated yet.

#### Step 3. Take three eigenpairs and write the linear system

Use $n=0,1,2$. At each point $x$:
$$\underbrace{\begin{pmatrix} X_0' & X_0 & \lambda_0X_0\\ X_1' & X_1 & \lambda_1X_1\\ X_2' & X_2 & \lambda_2X_2\end{pmatrix}}_{M(x)} \begin{pmatrix}\alpha\\ \beta\\ \gamma\end{pmatrix} = \underbrace{\begin{pmatrix}-X_0''\\ -X_1''\\ -X_2''\end{pmatrix}}_{r(x)} . \tag{2}$$
Three unknowns need three equations; each eigenpair gives one. (More eigenpairs add redundant equations, see step 8.)

#### Step 4. Solve by Cramer's rule

Let $D=\det M$, and let $A,B,G$ be $D$ with the first, second, third *column* replaced by $r$:
$$\alpha = \frac{A}{D},\qquad \beta=\frac{B}{D},\qquad \gamma=\frac{G}{D}\qquad\text{wherever } D(x)\neq 0 .$$
The identities hold for *any* solution $(p,q,w)$ of the inverse problem, so they are necessary conditions: the solution cannot take other values. This note is a mathematical derivation; it is not formalized in Lean yet.

#### Step 5. Why $D\ne0$ almost everywhere

$D$ may vanish at isolated points (always at a boundary point where all $X_n=0$), but never on an interval (the argument is the one used for `solution_unique`). Where $X_n\ne0$,
$$D = X_0X_1X_2\cdot\det\begin{pmatrix}u_0&1&\lambda_0\\u_1&1&\lambda_1\\u_2&1&\lambda_2\end{pmatrix},\qquad u_n = X_n'/X_n,$$
so $D=0$ on an interval means that the points $(\lambda_n,u_n)$ lie on a line. But $m_n=p\,u_n$ satisfy the Riccati equation $m_n' = -(q+\lambda_n w) - m_n^2/p$. Differentiating the collinearity relation of the $m_n$ and using this equation gives $m_1=m_0$ on the interval and then $(\lambda_1-\lambda_0)w=0$, contradicting $w>0$.

So $\{D\ne0\}$ is dense in $(a,b)$, and the *continuous* functions $\alpha,\beta,\gamma$ are determined by their values there: at a zero of $D$ take the limit of $A/D$, $B/D$, $G/D$.

#### Step 6. Recover $p$ by one integration

$\alpha = (\ln p)'$, hence
$$p(x) = p(a)\,\exp\!\Big(\int_a^x \alpha(t)\,dt\Big)$$
(integrate $\alpha$ and exponentiate). The constant $p(a)>0$ cannot be determined: it is the scale freedom of `solution_unique`. Fix it by normalisation, e.g. $p(a)=1$.

#### Step 7. Recover $q$ and $w$

$$q = p\,\beta,\qquad w = p\,\gamma .$$

#### Step 8. Check

Any further eigenpair $(\lambda_n,X_n)$, $n\ge3$, must satisfy (1) with the computed $\alpha,\beta,\gamma$. For data that really come from a Sturm-Liouville problem this holds automatically (a useful test for noisy or suspect data). Also verify $p>0$, $w>0$, $q\le0$ and that $(p,q,w)$ reproduces the boundary conditions' eigenvalues.

#### Remarks

* **Only $X_n$ and $\lambda_n$ are used**, together with $X_n',X_n''$ computed from them; the boundary conditions enter only through the fact that the data are eigenpairs.
* **Shortcut for hand computation.** $r=-X''$ is a vector in $\mathbb R^3$, and Cramer's rule says that $(\alpha,\beta,\gamma)$ are the coordinates of $r$ in the basis of the three columns of $M$. So if $-X_n''$ is visibly a combination $c_1X_n'+c_2X_n+c_3\lambda_nX_n$ with the *same* coefficients for all three $n$, then $(\alpha,\beta,\gamma)=(c_1,c_2,c_3)$ and no determinant has to be evaluated, one only needs $D\neq0$. Both examples below use this.
* **Numerics.** The formulas are ill-conditioned near zeros of $D$ (in particular near the endpoints for Dirichlet conditions). Normalise $p$ at an interior point instead of $a$, or fit $(\alpha,\beta,\gamma)$ by least squares from more than three eigenpairs.

### Example 1: the string, $p=1$, $q=0$, $w=1$

**Data.** Dirichlet problem $X''+\lambda X=0$, $X(0)=X(\pi)=0$ (the vibrating string). Known eigenpairs:
$$\lambda_n=(n+1)^2,\qquad X_n(x)=\sin\big((n+1)x\big),\qquad n=0,1,2,\dots$$
We pretend not to know the equation and recover $p,q,w$ from $n=0,1,2$, that is $\lambda=1,4,9$ and $X=\sin x,\sin2x,\sin3x$.

**Step 1-2.** Derivatives: $X_n'=k\cos kx$, $X_n''=-k^2\sin kx$ with $k=n+1$.

**Step 3.** The system (2) is
$$\begin{pmatrix} \cos x & \sin x & \sin x\\ 2\cos 2x & \sin 2x & 4\sin 2x\\ 3\cos 3x & \sin 3x & 9\sin 3x\end{pmatrix}\begin{pmatrix}\alpha\\ \beta\\ \gamma\end{pmatrix}=\begin{pmatrix}\sin x\\ 4\sin 2x\\ 9\sin 3x\end{pmatrix}.$$

**Step 4.** The right-hand side $-X_n''=k^2\sin kx$ is *exactly the third column* $\lambda_nX_n$. So $A$ and $B$ each contain two equal columns, and $G=D$:
$$A=0,\qquad B=0,\qquad G=D .$$
A direct expansion (checked symbolically) gives
$$D(x) = -16\sin^6 x .$$
It is nonzero on $(0,\pi)$ and vanishes at the endpoints, as predicted in step 5. Hence for $0<x<\pi$
$$\alpha=\frac{0}{D}=0,\qquad\beta=\frac{0}{D}=0,\qquad\gamma=\frac{D}{D}=1 ,$$
and by continuity these hold on all of $[0,\pi]$.

**Step 6.** $p(x)=p(0)\exp\int_0^x0\,dt=p(0)$. Normalise $p(0)=1$: $\boxed{p\equiv1}$.

**Step 7.** $q=p\beta=0$ and $w=p\gamma=1$: $\boxed{q\equiv0,\ w\equiv1}$.

**Step 8.** For $n=3$: $X_3''+0\cdot X_3'+0\cdot X_3+16\cdot1\cdot X_3=-16\sin4x+16\sin4x=0$. ✓ So the unique solution up to the factor $p(0)$ is $(p,q,w)=c\,(1,0,1)$, the string equation $X''+\lambda X=0$, as expected.

### Example 2: non-constant coefficients, $p=x$, $q=0$, $w=1/x$

**Data.** On $[1,e^{\pi}]$ consider $(xX')'+\dfrac{\lambda}{x}X=0$ with $X(1)=X(e^\pi)=0$ (Euler-type problem). With $t=\ln x$ it becomes $X_{tt}+\lambda X=0$, $X(t{=}0)=X(t{=}\pi)=0$, so the eigenpairs are
$$\lambda_n=(n+1)^2,\qquad X_n(x)=\sin\big((n+1)\ln x\big).$$
Again we only use $\lambda=1,4,9$ and $X=\sin\ln x,\ \sin 2\ln x,\ \sin3\ln x$, and forget the equation.

**Step 1-2.** With $k=n+1$,
$$X_n'=\frac{k\cos(k\ln x)}{x},\qquad X_n''=-\frac{k^2\sin(k\ln x)}{x^2}-\frac{k\cos(k\ln x)}{x^2}=-\frac{\lambda_nX_n}{x^2}-\frac{X_n'}{x}.$$

**Step 3-4.** The right-hand side of (2) is
$$-X_n''=\frac1x\,X_n'+0\cdot X_n+\frac1{x^2}\,\lambda_nX_n\qquad\text{for all }n=0,1,2,$$
with the same coefficients for all three rows. By the shortcut (coordinates of $r$ in the columns of $M$),
$$\alpha=\frac1x,\qquad\beta=0,\qquad\gamma=\frac1{x^2}.$$
Concretely, $A=D/x$, $B=0$, $G=D/x^2$ with $D(x)=-16\sin^6(\ln x)/x$ (computed symbolically), which is nonzero on $(1,e^\pi)$ and zero only at the endpoints.

**Step 6.**
$$p(x)=p(1)\exp\int_1^x\frac{dt}{t}=p(1)\,x .$$
Normalise $p(1)=1$: $\boxed{p(x)=x}$.

**Step 7.**
$$q=p\beta=0,\qquad w=p\gamma=x\cdot\frac1{x^2}=\frac1x,$$
$\boxed{q\equiv0,\ w(x)=1/x}$, recovering exactly the original coefficients (up to the scale $p(1)$).

**Step 8.** For $n=3$ ($\lambda=16$, $X=\sin4\ln x$): $X''+\frac1xX'+\frac{16}{x^2}X=0$ by the formula for $X_n''$ above. ✓

A numerical run of steps 3-7 on a problem with genuinely variable $p,q,w$ ($p=1+x^2$, $q=-x$, $w=2+\sin3x$ on $[0,1]$, eigenpairs computed numerically, derivatives from the data only) recovered $\alpha,\beta,\gamma$ to about $10^{-9}$ and $p,q,w$ to about $10^{-6}$ to $10^{-8}$ away from the endpoints.

### Summary of the algorithm

1. Take $(\lambda_n,X_n)$ for $n=0,1,2$ and compute $X_n',X_n''$.
2. Form $M(x)$ and $r(x)$ as in (2).
3. Solve $M(\alpha,\beta,\gamma)^{T}=r$ (Cramer, or read off coordinates).
4. $p=p(a)\exp\int_a^x\alpha$, $q=p\beta$, $w=p\gamma$.
5. Check with $n\ge3$, with signs ($p,w>0$, $q\le0$), and note the free scale $p(a)$.
