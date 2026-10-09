import ClassicalThermodynamics.Applications.KirkwoodOppenheim1961.IdealSolutions
import ClassicalThermodynamics.Applications.KirkwoodOppenheim1961.RegularSolutions
import ClassicalThermodynamics.Applications.KirkwoodOppenheim1961.RealSolutions

/-!
# Kirkwood–Oppenheim, *Chemical Thermodynamics*

Selected Chapter 11 ideal-solution, regular-solution, and Margules results.
Model definitions and derivations live in `ClassicalThermodynamics.Models`; this
application layer only records the correspondence to the chapter equations.

The supplied extension package's cubic Margules parameter structure asserted
`B2 = B1 + C1` for expansions with cubic coefficient `C1`. That relation does
not in general satisfy Gibbs–Duhem for those stated polynomials. The model
layer instead derives the coefficient relation from the polynomial
Gibbs–Duhem identity, making its coefficient convention explicit.
-/

namespace ClassicalThermodynamics.Applications.KirkwoodOppenheim1961

end ClassicalThermodynamics.Applications.KirkwoodOppenheim1961
