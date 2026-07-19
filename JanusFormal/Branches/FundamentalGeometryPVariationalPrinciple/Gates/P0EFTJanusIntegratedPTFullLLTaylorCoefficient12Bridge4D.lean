import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGlobalPTDifferentialLLFullCurveTaylorReconstruction4D

/-! Integrated C1/C2 coefficients of the genuine full PT LL curve. -/

namespace JanusFormal
namespace P0EFTJanusIntegratedPTFullLLTaylorCoefficient12Bridge4D

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff Topology
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLWeakEquation4D
open P0EFTJanusFullMatterRobinLLDirections4D
open P0EFTJanusDifferentialLLFullCurveActionDecomposition4D
open P0EFTJanusIntegratedPTFullLLHessianAssembly4D
open P0EFTJanusTruePTFullLLFirstVariationBridge4D
open P0EFTJanusFullLLVariationalAPI4D
open P0EFTJanusGlobalPTDifferentialLLFullCurveTaylorReconstruction4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)
local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance : BorelSpace (EffectiveThroat period hPeriod) where measurable_eq := rfl

theorem coefficient_one_integrable
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (direction : FullMatterRobinLLDirections period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    Integrable (ptTaylorCoeff period hPeriod 1 frame fields direction.llAuxMetric
      (fullDirectionLLVariation period hPeriod direction)) mu :=
  ptTaylorCoeff_integrable period hPeriod 1 frame fields direction.llAuxMetric
    (fullDirectionLLVariation period hPeriod direction) mu

theorem coefficient_two_integrable
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (direction : FullMatterRobinLLDirections period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    Integrable (ptTaylorCoeff period hPeriod 2 frame fields direction.llAuxMetric
      (fullDirectionLLVariation period hPeriod direction)) mu :=
  ptTaylorCoeff_integrable period hPeriod 2 frame fields direction.llAuxMetric
    (fullDirectionLLVariation period hPeriod direction) mu

theorem integral_coefficient_one_eq_fullLLEuler
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (direction : FullMatterRobinLLDirections period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    (∫ p, ptTaylorCoeff period hPeriod 1 frame fields direction.llAuxMetric
      (fullDirectionLLVariation period hPeriod direction) p ∂mu) =
      fullLLEuler period hPeriod frame fields direction mu := by
  change globalPTFullLLTaylorEuler period hPeriod frame fields direction.llAuxMetric
      (fullDirectionLLVariation period hPeriod direction) mu =
    fullLLEuler period hPeriod frame fields direction mu
  exact globalPTFullLLTaylorEuler_eq_actual period hPeriod frame fields direction mu

theorem integral_coefficient_two_eq_half_fullLLHessian
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (direction : FullMatterRobinLLDirections period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    (∫ p, ptTaylorCoeff period hPeriod 2 frame fields direction.llAuxMetric
      (fullDirectionLLVariation period hPeriod direction) p ∂mu) =
      (1 / 2 : Real) * fullLLHessian period hPeriod frame fields direction direction mu := by
  have h := globalPTFullLLTaylorHessianDiagonal_eq_actual period hPeriod frame fields
    direction.llAuxMetric (fullDirectionLLVariation period hPeriod direction) mu
  unfold globalPTFullLLTaylorHessianDiagonal at h
  change 2 * (∫ p, ptTaylorCoeff period hPeriod 2 frame fields direction.llAuxMetric
      (fullDirectionLLVariation period hPeriod direction) p ∂mu) =
    fullLLHessian period hPeriod frame fields direction direction mu at h
  linarith

end
end P0EFTJanusIntegratedPTFullLLTaylorCoefficient12Bridge4D
end JanusFormal
