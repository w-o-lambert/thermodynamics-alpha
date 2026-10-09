# Equation-by-equation comparison with Lekner (1982)

## Scope and sources

Lekner's paper introduces an entropy parameter `y = Δs/2` and expresses the
coexistence curve parametrically. The notation below is transcribed directly from the attached 1982 paper. The new
`PaperEquations.lean` module records and verifies equations (7), (10)-(16) against
the generic repository quantities. Equation (17) is retained as an asymptotic
follow-up because it requires the analytic limit modules rather than only algebra.

## Parameter

Lekner:

`y = Δs/2`.

Present package:

`d = log(z_liquid/z_gas)`.

Since the branch ratio is `exp(d)` and the Lekner ratio is `exp(2y)`, the exact
mapping is `d = 2y`.

## Auxiliary function f

Lekner:

`f(y) = [y cosh y - sinh y] / [sinh y cosh y - y]`.

Present package:

`H_vdW(d) = [d cosh(d/2) - 2 sinh(d/2)] / [sinh d - d]`.

Substitution `d = 2y`, together with `sinh(2y) = 2 sinh y cosh y`, gives
`H_vdW(2y) = f(y)` exactly.

## Branch coordinates

Present package:

`z_high = H_vdW(d) exp(d/2)` and `z_low = H_vdW(d) exp(-d/2)`.

At `d = 2y`:

`z_liquid = f(y) exp(y)` and `z_gas = f(y) exp(-y)`.

## Reduced densities

The free-volume coordinate satisfies `z = bρ/(1-bρ)`. With critical density
`ρ_c = 1/(3b)`, reduced density is

`ρ/ρ_c = 3z/(1+z)`.

Therefore:

`n_l = 3 f(y)/(exp(-y)+f(y))`,

`n_g = 3 f(y)/(exp(y)+f(y))`.

These are exactly the Lekner liquid and gas density branches.

## Auxiliary function g

Lekner:

`g(y) = 1 + 2 f(y) cosh y + f(y)^2`.

Present package generates the same combination from branch sum and product:

`z_l + z_g = 2 f(y) cosh y`,

`z_l z_g = f(y)^2`.

Hence `g(y) = 1 + z_l + z_g + z_l z_g = (1+z_l)(1+z_g)`.

## Reduced coexistence temperature and pressure

The paper-facing module records

`T/T_c = 27 f(y)[f(y)+cosh y] / [4 g(y)^2]`,

`p/p_c = 27 f(y)^2[1-f(y)^2] / g(y)^2`.

These are not new model assumptions. They are the reduced thermodynamic closure
obtained after inserting the same two branches into the van der Waals equation of
state and coexistence conditions.

## Parameter-free coexistence equation

Present package:

`log(z_l/z_g)/(z_l-z_g) = (2+z_l+z_g)/(z_l+z_g+2z_l z_g)`.

Using `log(z_l/z_g)=2y`, the Lekner branches solve precisely this equation. The
closed identity for `H_vdW` is therefore the same algebraic content as Lekner's
parametric solution, written in geometric-midpoint/log-ratio coordinates.

## Overall conclusion

The present package does not define a competing parametrisation. It uses the same
parametric solution in different variables:

* repository `d` equals `2y`;
* repository `H_vdW(d)` equals Lekner `f(y)`;
* repository high/low free-volume branches equal Lekner liquid/gas branches;
* the reduced-density transformation reproduces Lekner's density equations;
* the package's coefficient-free coexistence equation is the equation solved by
  Lekner's parametrisation.

The main difference is architectural: the package keeps the branch geometry in a
general method layer and confines author-specific entropy and reduced-variable
notation to this paper Application.

## Architectural promotion in v0.7

The entropy interpretation and coexistence observables now live in generic pure
van der Waals modules. This paper folder retains `y`, `f(y)`, `g(y)`, and theorem
wrappers proving that the paper notation is obtained from generic quantities by
`d = 2y`.
