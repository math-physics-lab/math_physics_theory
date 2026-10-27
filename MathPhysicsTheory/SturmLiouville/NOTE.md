# Expanding the operator

The Sturm-Liouville operator is written in divergence form,

$$
L y = \frac{d}{dx}\left(p(x) \frac{dy}{dx}\right) + q(x) y.
$$

When $p$ and $y'$ are differentiable, the product rule expands the first term:

$$
\frac{d}{dx}\bigl(p y'\bigr) = p' y' + p y'',
$$

so

$$
L y = p y'' + p' y' + q y.
$$

This is `Operator.apply_expanded`, stated as an equality of functions. Its hypotheses are
what the product rule needs at every point: `hp` makes $p$ differentiable and `hy` makes
$y'$ differentiable. In the proof, `funext` reduces to a point $x$, `HasDerivAt.mul` gives
the derivative of $t \mapsto p(t)\, y'(t)$ there, and `ring` reorders the terms.

Conversely, an operator $a_2 y'' + a_1 y' + a_0 y$ is in Sturm-Liouville form exactly when
$a_1 = a_2'$; otherwise multiplying by the integrating factor
$\mu = \exp\left(\int \frac{a_1 - a_2'}{a_2}\, dx\right)$ puts it in that form.
