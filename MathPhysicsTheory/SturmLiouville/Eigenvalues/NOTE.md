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

All derivatives in `Problem.IsSolution` are taken within $[a, b]$, so they are
one-sided at the endpoints. An eigenfunction $Y$ is therefore a $C^2$ solution of
$(pY')' + qY = -\lambda w Y$ on $[a, b]$ that satisfies both Robin conditions
(`eigenfunction_data`).

### Step 1: $E \subseteq [0, \infty)$ (Rayleigh quotient, Herman §4.2)

Multiply the equation by $Y$ and integrate by parts (Green's identity):

$$\lambda \int_a^b w Y^2 = \int_a^b \left(p Y'^2 - q Y^2\right)
  + p(a) Y(a) Y'(a) - p(b) Y(b) Y'(b).$$

The integral is $\ge 0$ because $p > 0$ and $q \le 0$. At $a$: if $\beta_1 = 0$,
then $Y(a) = 0$ and the boundary term is $0$; otherwise it equals
$-p(a)(\alpha_1/\beta_1) Y(a)^2 \ge 0$, since $\alpha_1 \beta_1 \le 0$. The term
at $b$ works the same way, using $\alpha_2 \beta_2 \ge 0$. So
$\lambda \int w Y^2 \ge \int p Y'^2 \ge 0$, and since $\int w Y^2 > 0$, we get
$\lambda \ge 0$.

### Step 2: $E \cap (-\infty, M]$ is finite (orthogonality and compactness)

Suppose infinitely many eigenvalues lie in $(-\infty, M]$. Normalise an
eigenfunction for each so that $\int_a^b w Y_\lambda^2 = 1$. For two of them,
$\lambda \ne \mu$, Green's identity gives

$$(\mu - \lambda) \int_a^b w Y_\lambda Y_\mu
  = \left[p \left(Y_\lambda' Y_\mu - Y_\lambda Y_\mu'\right)\right]_a^b = 0,$$

because both satisfy the same Robin condition at each end, so their Wronskian
vanishes there. Hence $\int_a^b w (Y_\lambda - Y_\mu)^2 = 2$.

On the other hand, the Rayleigh quotient gives
$\int_a^b p Y_\lambda'^2 \le \lambda \le M$, so $\int_a^b Y_\lambda'^2 \le C$ for a
constant $C$. Since $|Y'| \le t/2 + Y'^2/(2t)$, this gives the uniform estimate
$|Y_\lambda(x) - Y_\lambda(y)| \le t|x - y|/2 + C/(2t)$ for every $t > 0$, and
also a uniform bound on $|Y_\lambda|$. By Arzelà–Ascoli
(`BoundedContinuousFunction.arzela_ascoli`), two of the $Y_\lambda$ are uniformly
within $\delta$ of each other. For small $\delta$ this contradicts
$\int_a^b w (Y_\lambda - Y_\mu)^2 = 2$.

### Step 3: $E$ is infinite (a scaled Prüfer transformation)

For $k > 0$, write a solution as $u = \rho \sin\theta$, $p u' = k \rho \cos\theta$.
The Robin condition $\alpha u + \beta u' = 0$ at an endpoint $c$ then says
$\theta(c) \equiv A_c(k) \pmod \pi$, where $A_c(k) \in [0, \pi]$ solves
$\alpha p(c) \sin A + \beta k \cos A = 0$ (`bcAngle`). $A_c(k)$ depends
continuously on $k$.

Let $\theta_k$ solve

$$\theta' = \frac{k \cos^2\theta}{p} + \left(\frac{q}{k} + k w\right)\sin^2\theta,
  \qquad \theta(a) = A_a(k).$$

It exists by Picard–Lindelöf (`IsPicardLindelof`), because the right-hand side is
bounded and Lipschitz in $\theta$. Put
$\rho(x) = \exp \int_a^x \left(\frac{k}{p} - \frac{q}{k} - k w\right)
\sin\theta \cos\theta$ and $u = \rho \sin\theta$. Then $p u' = k \rho \cos\theta$
and $(p u')' + (q + k^2 w) u = 0$, and $u$ satisfies the Robin condition at $a$.
So whenever $\theta_k(b) = A_b(k) + m\pi$ with $m \ge 3$, $u$ is an eigenfunction
for $\lambda = k^2$. It is nonzero where $\theta = 5\pi/2$.

* $k \mapsto \theta_k(b) - A_b(k)$ is continuous on $(0, \infty)$, by Grönwall's
  inequality (`dist_le_of_approx_trajectories_ODE`).
* For large $k$ the right-hand side is at least $c k$ for some $c > 0$, so
  $\theta_k(b) - A_b(k) \ge c k (b - a) - \pi \to \infty$.

By the intermediate value theorem, $\theta_k(b) - A_b(k)$ takes every value
$m\pi$ with $m$ large. Different values of $m$ give different $k$, and so
different eigenvalues $k^2$.

### Lean structure

The steps are `private` lemmas in `Eigenvalues.lean`:

* eigenfunctions: `eigenfunction_data`;
* Step 1: `green`, `rayleigh` and `eigenvalue_nonneg`;
* Step 2: `orthogonal` and `eigenvalueSet_inter_Iic_finite`;
* Step 3: `isEigenvalue_of_prufer` and `eigenvalueSet_infinite`.
