import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereMultiplicity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCNormalModeSection4D

/-!
# Radial coefficients for complex first-sphere witness arguments

At the phase-zero witness the radial local coordinate contains the extra
factor `2` coming from the sum of the two Hopf frame representatives.  This
file packages the resulting positive and negative real coefficients and their
nonvanishing, so the complex multiplicity proofs can refer to the exact
observed scalar rather than unfold the witness construction repeatedly.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereComplexMultiplicity4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereDirac4D
open P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereMultiplicity4D
open P0EFTJanusProgramPD9PrimitiveSpinCNormalModeSection4D

/-- Exact positive-branch radial scalar observed at the phase-zero witness. -/
def primitiveSpinCHopfFirstSpherePositiveRadialCoefficient
    (period : Real) (sector : NormalRootChoice) (mode : Int) : Real :=
  2 *
    (primitiveSpinCHopfFirstSphereDiracFrequency period sector mode -
      normalRootLeviCivitaCorrectedFrequency period sector mode)

/-- The positive observed radial scalar never vanishes. -/
theorem primitiveSpinCHopfFirstSpherePositiveRadialCoefficient_ne_zero
    (period : Real) (sector : NormalRootChoice) (mode : Int) :
    primitiveSpinCHopfFirstSpherePositiveRadialCoefficient
        period sector mode ≠ 0 := by
  exact mul_ne_zero (by norm_num)
    (firstSpherePositiveCoefficient_ne_zero period sector mode)

/-- Exact negative-branch radial scalar observed at the phase-zero witness. -/
def primitiveSpinCHopfFirstSphereNegativeRadialCoefficient
    (period : Real) (sector : NormalRootChoice) (mode : Int) : Real :=
  2 *
    (-primitiveSpinCHopfFirstSphereDiracFrequency period sector mode -
      normalRootLeviCivitaCorrectedFrequency period sector mode)

/-- The negative observed radial scalar never vanishes. -/
theorem primitiveSpinCHopfFirstSphereNegativeRadialCoefficient_ne_zero
    (period : Real) (sector : NormalRootChoice) (mode : Int) :
    primitiveSpinCHopfFirstSphereNegativeRadialCoefficient
        period sector mode ≠ 0 := by
  exact mul_ne_zero (by norm_num)
    (firstSphereNegativeCoefficient_ne_zero period sector mode)

/-- Consolidated nonzero radial witness package. -/
theorem primitiveSpinCHopfFirstSphereComplexRadial_closed
    (period : Real) (sector : NormalRootChoice) (mode : Int) :
    primitiveSpinCHopfFirstSpherePositiveRadialCoefficient
        period sector mode ≠ 0 ∧
      primitiveSpinCHopfFirstSphereNegativeRadialCoefficient
        period sector mode ≠ 0 :=
  ⟨primitiveSpinCHopfFirstSpherePositiveRadialCoefficient_ne_zero
      period sector mode,
    primitiveSpinCHopfFirstSphereNegativeRadialCoefficient_ne_zero
      period sector mode⟩

end
end P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereComplexMultiplicity4D
end JanusFormal
