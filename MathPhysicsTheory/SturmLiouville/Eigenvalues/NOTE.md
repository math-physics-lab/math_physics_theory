## Proof plan for `exists_eigenvalue_seq`

The classical theorem (Herman §4.2; Birkhoff–Rota, Ch. 10; Coddington–Levinson,
Ch. 8) says that a regular Sturm-Liouville problem has eigenvalues
$\lambda_0 < \lambda_1 < \cdots$ with $\lambda_n \to +\infty$, and no others. The
Lean proof splits it into three facts about $E$ = `eigenvalueSet P`, stated as
`have`s inside the proof:

1. $E \subseteq [0, \infty)$ (`hnonneg`);
2. $E \cap (-\infty, M]$ is finite for every $M$ (`hfin`);
3. $E$ is infinite (`hinf`).

Order theory then finishes the proof: a set with these properties is
order-isomorphic to $\mathbb{N}$. Its enumeration is strictly increasing,
starts at a value $\ge 0$ and tends to $+\infty$, since only finitely many terms
lie below each bound.

### Step 0: what the formal definitions say at the endpoints

`Operator.apply` and `Robin.Operator.apply` use `deriv`, the two-sided
derivative of a function on all of $\mathbb{R}$. It is $0$ where the function is
not differentiable. Only the values on $[a, b]$ are fixed by the problem, so an
eigenfunction $X$ can be changed outside $[a, b]$, and so can the coefficient
$p$. Let $Y = X|_{[a,b]}$ and let $Y'$ be its one-sided derivative at the
endpoints.

At an interior point, $X$ and $p$ are differentiable in the usual sense, so the
equation $(pY')' + qY = -\lambda w Y$ holds on $(a, b)$. Because $Y$ is $C^2$ on
$[a, b]$, it then holds on all of $[a, b]$. At an endpoint $c$ there are three
possibilities:

* if $X$ is differentiable at $c$, then `deriv X c` $= Y'(c)$ and the Robin
  condition $\alpha Y(c) + \beta Y'(c) = 0$ holds as written;
* if not, then `deriv X c` $= 0$ and the condition reduces to $\alpha Y(c) = 0$.
  - If $\alpha \ne 0$, this gives $Y(c) = 0$.
  - If $\alpha = 0$, look at $h = p \cdot$ `deriv X`, for which $h(c) = 0$:
    - if $h$ is differentiable at $c$, it is continuous there, so
      $p(c)Y'(c) = 0$ and the Neumann condition holds as written;
    - otherwise `deriv h c` $= 0$, and the equation at $c$ becomes
      $(q(c) + \lambda w(c)) Y(c) = 0$.

So for every eigenvalue $\lambda \in E$ there is a $C^2$ solution $Y \not\equiv 0$
of the equation on $[a, b]$ that, at each endpoint $c$, either

* (R) satisfies the given Robin condition, or
* (D) satisfies $Y(c) = 0$,

unless $\lambda = -q(c)/w(c)$, which is at most two numbers. Conversely, every
eigenvalue $\lambda$ of the Dirichlet problem, with eigenfunction $Y$, lies in
$E$. Set $X = Y$ on $[a, b]$ and $X = Y + 1$ outside. Then $X$ jumps at $a$ and
$b$, so `deriv X` vanishes there and both Robin conditions read $0 = 0$. Also
$Y'(c) \ne 0$ (otherwise $Y \equiv 0$ by uniqueness), so $h$ jumps at $c$ and the
equation at $c$ reads $0 = 0$.

Write $\sigma(T_a, T_b)$ for the spectrum of the honest problem with condition
$T_a \in \{R, D\}$ at $a$ and $T_b$ at $b$. Then

$$\sigma(D, D) \subseteq E \subseteq \bigcup_{T_a, T_b \in \{R, D\}} \sigma(T_a, T_b)
  \cup \{-q(a)/w(a), -q(b)/w(b)\}.$$

### Step 1: $E \subseteq [0, \infty)$ (Rayleigh quotient, Herman §4.2)

Multiply the equation by $Y$ and integrate by parts:

$$\lambda \int_a^b w Y^2 = \int_a^b \left(p Y'^2 - q Y^2\right)
  + p(a) Y(a) Y'(a) - p(b) Y(b) Y'(b).$$

The integral is $\ge 0$ because $p > 0$ and $q \le 0$. At $a$: under (D) the
boundary term is $0$; under (R) with $\beta_1 \ne 0$ it equals
$-p(a)(\alpha_1/\beta_1) Y(a)^2 \ge 0$, since $\alpha_1 \beta_1 \le 0$. The term
at $b$ works the same way, using $\alpha_2 \beta_2 \ge 0$. Since
$\int w Y^2 > 0$, we get $\lambda \ge 0$. The two exceptional values satisfy
$-q(c)/w(c) \ge 0$ directly.

### Steps 2 and 3: Prüfer's transformation (Birkhoff–Rota Ch. 10, Teschl §5.5)

Fix separated conditions $(T_a, T_b)$ and let $u(\cdot, \lambda)$ be the solution
of $(pu')' + (q + \lambda w) u = 0$ with initial data satisfying $T_a$. Write
$u = \rho \sin\theta$ and $pu' = \rho\cos\theta$. Then

$$\theta' = \frac{\cos^2\theta}{p} + (q + \lambda w)\sin^2\theta, \qquad
  \theta(a, \lambda) = A \in [0, \pi),$$

and $T_b$ holds exactly when $\theta(b, \lambda) \equiv B \pmod \pi$ for a fixed
$B \in (0, \pi]$. The standard facts are:

* $\lambda \mapsto \theta(b, \lambda)$ is continuous, by continuous dependence on
  parameters (Grönwall);
* it is strictly increasing, by the Sturm comparison theorem applied to the
  $\theta$ equation;
* it tends to $0$ as $\lambda \to -\infty$ and to $+\infty$ as $\lambda \to +\infty$;
* $\theta$ crosses multiples of $\pi$ only upwards, because $\theta' = 1/p > 0$
  there.

So $\sigma(T_a, T_b) = \{\lambda_n : \theta(b, \lambda_n) = B + n\pi\}$, with exactly
one $\lambda_n$ for each $n \ge 0$, and $\lambda_n \uparrow \infty$. Each of the
four spectra therefore meets $(-\infty, M]$ in a finite set, which gives fact 2.
$\sigma(D, D)$ is infinite, which gives fact 3.

### Lean prerequisites

Mathlib already has existence and uniqueness for ODEs (`IsPicardLindelof`,
`ODE_solution_unique`) and Grönwall's inequality, which give continuous
dependence on $\lambda$. Still to formalise: the Prüfer angle, the comparison
argument for monotonicity, and the limits as $\lambda \to \pm\infty$.
