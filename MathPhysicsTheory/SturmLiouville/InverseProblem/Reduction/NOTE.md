## How much data does the inverse problem need?

`InverseProblem` takes **all** eigenpairs $(\lambda_n,X_n)$, $n=0,1,2,\dots$, and assumes that the $\lambda_n$ are the whole ordered spectrum of some problem. Below we look at how much of this is needed. The answers to (1) and (2) are formalized in this module. The rest is a mathematical derivation and is not formalized yet.

| known in advance | eigenpairs needed | boundary conditions used? | status |
|---|---|---|---|
| nothing ($p,q,w$ all unknown) | **3**, and 2 are not enough | no | 3 suffice: formalized; 2 fail: derivation |
| $p$ | 2 | no | derivation |
| $w$ | 2 | yes (one endpoint) | derivation |
| $q\equiv0$ | 2, with $\lambda_0,\lambda_1\ne0$ | no | derivation |
| only numbers (eigenvalues, norming constants) | — | yes | gives the Liouville normal form only |

### 1. Three eigenpairs are enough, and nothing is lost

The uniqueness proof (`proportional_of_eigenpairs`) uses exactly three eigenpairs with $\lambda_0<\lambda_1<\lambda_2$. It does **not** use

* the other eigenpairs,
* where the three eigenvalues sit in the spectrum (they need not be the first three, and this does not have to be known),
* the boundary conditions,
* the sign condition $q\le0$.

`ReducedInverseProblem` therefore takes three eigenpairs as data. Existence and uniqueness up to a factor $c>0$ hold (`ReducedInverseProblem.exists_solution`, `ReducedInverseProblem.solution_unique`). These proofs need no `sorry`. The uniqueness proof for the full problem does need one: it gets $\lambda_0<\lambda_1<\lambda_2$ from `exists_eigenvalue_seq`, which is not proved yet.

The reduction loses nothing. `InverseProblem.isSolution_iff_reduce` says that for any $n_0<n_1<n_2$ the full problem and the problem with only the eigenpairs $n_0,n_1,n_2$ have the same solutions. Put another way, three eigenpairs fix the whole spectral data. Two problems that share three eigenpairs are proportional (`Problem.proportional_of_three`), so they have the same eigenfunctions (`Problem.isEigenfunction_iff_of_three`) and the same ordered spectrum (`Problem.eigenvalues_eq_of_three`).

### 2. Where Steklov's expansion comes in

Steklov's theorem (`steklov_expansion`) says that every $f\in C^2[a,b]$ satisfying the boundary conditions is the sum of its Fourier series,
$$f=\sum_n c_nX_n,\qquad c_n=\frac{\int_a^b fX_nw}{\int_a^b X_n^2w}.$$
The coefficients involve $w$, which the inverse problem determines only up to a factor $c$. But that factor cancels in $c_n$ (`Problem.Proportional.fourierCoeff_eq`). So:

> **Three eigenpairs determine the whole Steklov expansion.** Every problem with the given three eigenpairs has the same eigenfunctions $X_n$ and the same coefficients $c_n(f)$ for every $f$ (`Problem.fourierCoeff_eq_of_three`). The expansion $f=\sum c_nX_n$ can be computed from the three eigenpairs.

This is the precise sense in which the other eigenpairs carry no new information. Recover $(p,q,w)$ from three pairs. The rest of the spectrum and the eigenfunction basis of Steklov's theorem then follow from the recovered equation.

**What Steklov's theorem cannot do: bring three down to two.** The obstruction in §3 is *local*: the coefficients are changed on a small interval only. Completeness is a *global* property, and the modified problem is again a regular Sturm-Liouville problem. By Steklov's theorem it has its own complete eigenbasis, which contains the same two given eigenfunctions. So completeness or orthogonality of the given functions cannot tell the two problems apart. (Orthogonality $\int X_0X_1w=0$ holds for both.)

**Where completeness does reduce the data: from functions to numbers.** In classical inverse spectral theory (Borg, Gelfand–Levitan, Marchenko), sequences of *numbers* replace the eigenfunctions. Examples are the spectrum together with the norming constants $\int X_n^2w$ (with $X_n$ normalized at $a$), or two spectra for two boundary conditions. The proofs rest on expansion theorems of exactly Steklov's kind, such as Parseval's identity for the eigenfunction basis. However, the Liouville transformation
$$t=\int_a^x\sqrt{w/p},\qquad y=(pw)^{1/4}X$$
turns any problem into $-y''+Q(t)\,y=\lambda y$ on $[0,\ell]$. It keeps the spectrum and changes the boundary coefficients in a known way. Spectral numbers therefore determine at most $\ell$ and the single function $Q$, never the three functions $p,q,w$. Numbers alone are enough only when two of $(p,q,w)$ are known in advance. This is the trade-off: three eigen*functions* determine everything, while infinitely many *numbers* determine one function.

**Open direction.** Do two eigenfunctions together with the full spectrum (numbers only for $n\ge2$) determine $(p,q,w)$? The local perturbation of §3 does change the spectrum, so §3 does not rule this out. A proof would need global, Steklov-type arguments.

### 3. Two eigenpairs are not enough

Take the string: $p=1$, $q=0$, $w=1$ on $[0,\pi]$ with Dirichlet conditions, and its first two eigenpairs
$$\lambda_0=1,\ X_0=\sin x,\qquad \lambda_1=4,\ X_1=\sin2x .$$
Let $c\in C^1[0,\pi]$ with $c\ge1$, $c'\ge0$, $c'\not\equiv0$, and $c'$ supported in $[\pi/6,\pi/3]$. Define
$$\tilde p=c,\qquad \tilde q=-c'\Big(\cot x+\tfrac13\tan x\Big),\qquad \tilde w=c+\tfrac13\,c'\tan x .$$
All three are continuous, since $c'$ vanishes near the zeros $0,\pi/2,\pi$ of $X_0X_1$. Also $\tilde p\ge1>0$, $\tilde w\ge1>0$, and $\tilde q\le0$ because $\cot x,\tan x>0$ on $[\pi/6,\pi/3]$. A direct computation (checked symbolically) gives
$$(\tilde pX_n')'+\tilde qX_n+\lambda_n\tilde wX_n=0\qquad(n=0,1).$$
So $\sin x$ and $\sin2x$ are eigenfunctions of the new problem for $1$ and $4$. By the oscillation theorem ($0$ and $1$ interior zeros), they are even its **first two** eigenpairs. But $(\tilde p,\tilde q,\tilde w)$ is not a multiple of $(1,0,1)$. Hence two eigenpairs do not determine the coefficients, even with their indices and the boundary conditions known.

**Where the construction comes from.** For $c=\tilde p/p$, eliminating $X_n''$ gives, for each $n$ (see `MathPhysicsTheory.SturmLiouville.InverseProblem.Uniqueness`),
$$c'\,pX_n' + \big(Q+\lambda_nW\big)X_n=0,\qquad Q=\tilde q-cq,\quad W=\tilde w-cw .$$
With two eigenpairs these are two linear equations for the two unknowns $Q,W$, solvable for **any** $c$ wherever $X_0X_1\ne0$. This leaves one free function. A third eigenpair adds a third equation, and the Riccati argument of `proportional_of_eigenpairs` then forces $c'=0$.

### 4. Two eigenpairs plus one known coefficient

Count the unknowns: every eigenpair gives one equation at each point, and there are three unknown functions. If one coefficient is known, two eigenpairs should be enough, and in each case this holds. Below $(p,q,w)$ is the true solution, $(\tilde p,\tilde q,\tilde w)$ another one, and $c,Q,W$ are as in §3.

**$p$ known.** Then $c\equiv1$, so $(Q+\lambda_nW)X_n=0$ for $n=0,1$. Zeros of $X_n$ are isolated (Cauchy uniqueness), so $Q+\lambda_0W=Q+\lambda_1W=0$, hence $Q=W=0$ and $\tilde q=q$, $\tilde w=w$.

**$w$ known** (the density, say). Then $W=(1-c)w$. Multiply the relation for $n=0$ by $X_1$, the one for $n=1$ by $X_0$, and subtract. With the Wronskian $\mathcal W=X_0X_1'-X_0'X_1$ this gives
$$c'\,p\mathcal W=(\lambda_1-\lambda_0)(c-1)\,wX_0X_1 ,$$
and from the equations, $(p\mathcal W)'=-(\lambda_1-\lambda_0)\,wX_0X_1$. Hence $\big((c-1)\,p\mathcal W\big)'=0$, so $(c-1)\,p\mathcal W$ is constant on $[a,b]$. **Here the boundary conditions enter.** $X_0$ and $X_1$ satisfy the same Robin condition at $a$, so $(X_0,X_0')(a)$ and $(X_1,X_1')(a)$ are parallel and $\mathcal W(a)=0$. The constant is therefore $0$. Now $\mathcal W$ does not vanish on any interval, since $X_0,X_1$ would then be proportional there, which is impossible for different eigenvalues. So $c\equiv1$, and the case "$p$ known" applies. Without boundary conditions this fails: $c=1+K/(p\mathcal W)$ is a one-parameter family of solutions.

**$q\equiv0$ known** (as for a string with variable tension and density). Then $Q=0$. Combine $\lambda_1X_1\cdot(n{=}0)-\lambda_0X_0\cdot(n{=}1)$:
$$c'\,p\,\big(\lambda_1X_0'X_1-\lambda_0X_0X_1'\big)=0 .$$
The bracket cannot vanish on an interval if $\lambda_0\ne0$. Otherwise $m_0=(\lambda_0/\lambda_1)\,m_1$ for $m_n=pX_n'/X_n$, and the Riccati equations $m_n'=-\lambda_nw-m_n^2/p$ give $\lambda_0(\lambda_0-\lambda_1)\,m_1^2=0$, so $m_1=0$ and $X_1$ is constant, which forces $\lambda_1=0$. So $c'\equiv0$, $c$ is constant, then $W=0$, and $(\tilde p,\tilde w)=c\,(p,w)$. The condition $\lambda_0\ne0$ is needed. For the Neumann problem with $q=0$, $X_0=1$ and $\lambda_0=0$ satisfy the equation for every $p,w$, so they carry no information.
