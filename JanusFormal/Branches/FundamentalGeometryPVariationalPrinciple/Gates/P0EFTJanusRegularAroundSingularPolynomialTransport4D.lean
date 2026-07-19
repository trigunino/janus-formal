import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFinitePolynomialMatrixValuationCriterion4D

/-! # Regular changes around a singular diagonal polynomial transport -/

namespace JanusFormal
namespace P0EFTJanusRegularAroundSingularPolynomialTransport4D

set_option autoImplicit false
noncomputable section

open Filter
open scoped Topology
open P0EFTJanusSignedNormalizedInversePowerDivergence4D

abbrev Matrix4 := P0EFTJanusMatrixSquareRootFrechetSylvester.Matrix4

def regularAroundTransport (left core right : Real → Matrix4) (t : Real) : Matrix4 :=
  left t * core t * right t

/-- Any finite limit produced by the diagonal valuation criterion survives
arbitrary convergent regular changes on both sides. -/
theorem regularAroundTransport_tendsto
    (left core right : Real → Matrix4) (leftLimit coreLimit rightLimit : Matrix4)
    (hLeft : Tendsto left (nhdsWithin 0 (Set.Ioi 0)) (nhds leftLimit))
    (hCore : Tendsto core (nhdsWithin 0 (Set.Ioi 0)) (nhds coreLimit))
    (hRight : Tendsto right (nhdsWithin 0 (Set.Ioi 0)) (nhds rightLimit)) :
    Tendsto (regularAroundTransport left core right)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (leftLimit * coreLimit * rightLimit)) := by
  exact (hLeft.mul hCore).mul hRight

/-- A continuous scalar extractor records whether the regular limiting frames
annihilate a divergent component.  If its extracted component still equals a
nonzero normalized leading factor times an inverse power, no finite matrix
limit can exist. -/
theorem regularAroundTransport_no_finite_limit_of_survivingExtractor
    (left core right : Real → Matrix4)
    (extract : Matrix4 → Real) (hExtractContinuous : Continuous extract)
    (normalized : Real → Real) {coefficient : Real}
    (hNormalized : Tendsto normalized (nhdsWithin 0 (Set.Ioi 0))
      (nhds coefficient)) (hCoefficient : coefficient ≠ 0)
    {power : Nat} (hPower : 0 < power)
    (hSurvives :
      (fun t => extract (regularAroundTransport left core right t)) =ᶠ[
        nhdsWithin 0 (Set.Ioi 0)]
      (fun t => normalized t * (t ^ power)⁻¹))
    (candidate : Matrix4) :
    ¬ Tendsto (regularAroundTransport left core right)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds candidate) := by
  intro hMatrix
  have hFinite : Tendsto
      (fun t => extract (regularAroundTransport left core right t))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (extract candidate)) :=
    hExtractContinuous.continuousAt.tendsto.comp hMatrix
  have hForbidden := normalized_mul_inversePower_no_finite_limit normalized
    hNormalized hCoefficient hPower (extract candidate)
  exact hForbidden (hFinite.congr' hSurvives)

/-- Entry extraction is continuous, so the obstruction specializes directly
to any transported matrix coefficient that survives the limiting frames. -/
theorem regularAroundTransport_no_finite_limit_of_survivingEntry
    (left core right : Real → Matrix4) (row column : Fin 4)
    (normalized : Real → Real) {coefficient : Real}
    (hNormalized : Tendsto normalized (nhdsWithin 0 (Set.Ioi 0))
      (nhds coefficient)) (hCoefficient : coefficient ≠ 0)
    {power : Nat} (hPower : 0 < power)
    (hSurvives :
      (fun t => regularAroundTransport left core right t row column) =ᶠ[
        nhdsWithin 0 (Set.Ioi 0)]
      (fun t => normalized t * (t ^ power)⁻¹))
    (candidate : Matrix4) :
    ¬ Tendsto (regularAroundTransport left core right)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds candidate) := by
  exact regularAroundTransport_no_finite_limit_of_survivingExtractor
    left core right (fun matrix => matrix row column)
    (continuous_id.matrix_elem row column) normalized hNormalized hCoefficient
    hPower hSurvives candidate

end
end P0EFTJanusRegularAroundSingularPolynomialTransport4D
end JanusFormal
