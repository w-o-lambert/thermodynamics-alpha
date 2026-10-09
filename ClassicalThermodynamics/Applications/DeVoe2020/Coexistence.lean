import ClassicalThermodynamics.Thermodynamics.Coexistence

/-!
# DeVoe (2020): a coexistence condition

This wrapper records only the componentwise chemical-potential equality
condition for multicomponent phase equilibrium discussed in DeVoe's Chapter
12. It does not identify the repository's osmotic pressure with DeVoe's
ordinary pressure or formalize the source's common-temperature condition.
For the polymer-mixture setting, ACS Omega 2021a Equation (10) separately
relates osmotic pressure to the solvent mixing chemical potential when a
shared partial molar volume is assumed.
-/

namespace ClassicalThermodynamics.Applications.DeVoe2020

/-- DeVoe (2020), Chapter 12, multicomponent phase equilibrium: the
chemical-potential equality clause of the repository's pairwise coexistence
predicate.

The repository predicate additionally requires equal osmotic pressure. That
condition is not identified here with DeVoe's ordinary-pressure condition;
for the ACS Omega 2021a model, its connection to solvent chemical-potential
equality is recorded separately by
`verified_equation10_solventCoexistence_iff_osmoticPressure`, under its
shared-nonzero-partial-volume hypothesis.
-/
theorem chapter12_coexistence_chemicalPotential_eq
    {ι State Model : Type*}
    [ClassicalThermodynamics.Thermodynamics.HasChemicalPotential ι State Model]
    [ClassicalThermodynamics.Thermodynamics.HasOsmoticPressure Model State]
    {M : Model} {a b : State}
    (h : ClassicalThermodynamics.Thermodynamics.Coexist ι M a b) :
    ∀ i : ι,
      ClassicalThermodynamics.Thermodynamics.HasChemicalPotential.chemicalPotential
        M a i =
      ClassicalThermodynamics.Thermodynamics.HasChemicalPotential.chemicalPotential
        M b i :=
  ClassicalThermodynamics.Thermodynamics.coexist_chemicalPotential_eq h

end ClassicalThermodynamics.Applications.DeVoe2020
