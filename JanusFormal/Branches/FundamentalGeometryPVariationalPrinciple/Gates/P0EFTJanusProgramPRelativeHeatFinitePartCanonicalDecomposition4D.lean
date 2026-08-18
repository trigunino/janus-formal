import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeHeatFinitePartDeterminant4D

/-!
# Canonical signed decomposition of a relative heat finite part

The heat counterterm and the two heat integrals are stored with their raw
signs.  The logarithmic determinant is the negative of their sum, so each
assembly contribution carries one explicit minus sign.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRelativeHeatFinitePartCanonicalDecomposition4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusProgramPRelativeHeatFinitePartDeterminant4D

/-- Signed determinant contribution of the raw counterterm finite part. -/
def canonicalCountertermContribution
    {heatTrace : HeatTime → Real}
    (data : RelativeHeatFinitePartData heatTrace) : Real :=
  -data.countertermFinitePart

/-- Signed determinant contribution of the raw short-time remainder. -/
def canonicalShortTimeContribution
    {heatTrace : HeatTime → Real}
    (data : RelativeHeatFinitePartData heatTrace) : Real :=
  -relativeHeatShortTimeFinitePart data

/-- Signed determinant contribution of the raw long-time heat integral. -/
def canonicalLongTimeContribution
    {heatTrace : HeatTime → Real}
    (data : RelativeHeatFinitePartData heatTrace) : Real :=
  -relativeHeatLongTimeIntegral data

/-- The canonical determinant decomposition, with the global heat/zeta minus
sign distributed over its three raw terms. -/
theorem relativeHeatFinitePartLogDeterminant_eq_canonical
    {heatTrace : HeatTime → Real}
    (data : RelativeHeatFinitePartData heatTrace) :
    relativeHeatFinitePartLogDeterminant data =
      canonicalCountertermContribution data +
        canonicalShortTimeContribution data +
          canonicalLongTimeContribution data := by
  unfold relativeHeatFinitePartLogDeterminant
    canonicalCountertermContribution canonicalShortTimeContribution
    canonicalLongTimeContribution
  ring

/-- Public canonical-sign checkpoint. -/
theorem relative_heat_finite_part_canonical_decomposition_gate
    {heatTrace : HeatTime → Real}
    (data : RelativeHeatFinitePartData heatTrace) :
    relativeHeatFinitePartLogDeterminant data =
      canonicalCountertermContribution data +
        canonicalShortTimeContribution data +
          canonicalLongTimeContribution data :=
  relativeHeatFinitePartLogDeterminant_eq_canonical data

end
end P0EFTJanusProgramPRelativeHeatFinitePartCanonicalDecomposition4D
end JanusFormal
