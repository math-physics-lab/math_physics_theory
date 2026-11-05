## Proof of `exists_eigenvalue_seq`

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

unless $\lambda = -q(c)/w(c)$, which is at most two numbers (`eigenfunction_data`).

Conversely, let $Y$ be a Dirichlet eigenfunction for $\lambda$ with
$p(c)Y'(c) \ne 0$ at both ends. Then $\lambda \in E$. Set $X = Y$ on $[a, b]$ and
$X = Y + 1$ outside. Then $X$ jumps at $a$ and $b$, so `deriv X` vanishes there
and both Robin conditions read $0 = 0$. Also $h$ jumps at each end, so the
equation there reads $0 = 0$ too.

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

### Step 2: $E \cap (-\infty, M]$ is finite (orthogonality and compactness)

Suppose infinitely many eigenvalues lie in $(-\infty, M]$. Discard the two
exceptional values. Each remaining eigenvalue has an eigenfunction that satisfies
(R) or (D) at each end; normalise it so that $\int_a^b w Y^2 = 1$. There are only
four combinations of (R) and (D), so infinitely many of these eigenvalues share
one. For two of them, $\lambda \ne \mu$, Green's identity gives

$$(\mu - \lambda) \int_a^b w Y_\lambda Y_\mu
  = \left[p \left(Y_\lambda' Y_\mu - Y_\lambda Y_\mu'\right)\right]_a^b = 0,$$

because both satisfy the same condition at each end, so their Wronskian vanishes
there. Hence $\int_a^b w (Y_\lambda - Y_\mu)^2 = 2$.

On the other hand, the Rayleigh quotient gives
$\int_a^b p Y_\lambda'^2 \le \lambda \le M$, so $\int_a^b Y_\lambda'^2 \le C$ for a
constant $C$. Since $|Y'| \le t/2 + Y'^2/(2t)$, this gives the uniform estimate
$|Y_\lambda(x) - Y_\lambda(y)| \le t|x - y|/2 + C/(2t)$ for every $t > 0$, and
also a uniform bound on $|Y_\lambda|$. By Arzelà–Ascoli
(`BoundedContinuousFunction.arzela_ascoli`), two of the $Y_\lambda$ are uniformly
within $\delta$ of each other. For small $\delta$ this contradicts
$\int_a^b w (Y_\lambda - Y_\mu)^2 = 2$.

### Step 3: $E$ is infinite (a scaled Prüfer transformation)

For $k > 0$, let $\theta_k$ solve

$$\theta' = \frac{k \cos^2\theta}{p} + \left(\frac{q}{k} + k w\right)\sin^2\theta,
  \qquad \theta(a) = 0.$$

It exists by Picard–Lindelöf (`IsPicardLindelof`), because the right-hand side is
bounded and Lipschitz in $\theta$. Put
$\rho(x) = \exp \int_a^x \left(\frac{k}{p} - \frac{q}{k} - k w\right)
\sin\theta \cos\theta$ and $u = \rho \sin\theta$. Then $p u' = k \rho \cos\theta$
and $(p u')' + (q + k^2 w) u = 0$. So whenever $\theta_k(b) = m\pi$ with $m \ge 1$,
$u$ is a Dirichlet eigenfunction for $\lambda = k^2$. Extended by a jump outside
$[a, b]$, it is an eigenfunction of `P` (Step 0).

* $k \mapsto \theta_k(b)$ is continuous on $(0, \infty)$, by Grönwall's
  inequality (`dist_le_of_approx_trajectories_ODE`).
* For large $k$ the right-hand side is at least $c k$ for some $c > 0$, so
  $\theta_k(b) \ge c k (b - a) \to \infty$.

By the intermediate value theorem, $\theta_k(b)$ takes every value $m\pi$ with
$m$ large. Different values of $m$ give different $k$, and so different
eigenvalues $k^2$.

### Lean structure

The steps are `private` lemmas in `Eigenvalues.lean`:

* Step 0: `eigenfunction_data`;
* Step 1: `rayleigh` and `eigenvalue_nonneg`;
* Step 2: `orthogonal` and `eigenvalueSet_inter_Iic_finite`;
* Step 3: `isEigenvalue_of_prufer` and `eigenvalueSet_infinite`.
