import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusPTSymmetricDifferentialLLHessian4D

namespace JanusFormal
namespace P0EFTJanusDifferentialLLActionReconstruction4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusGlobalLLWorldvolume4D
open P0EFTJanusMappingTorusGlobalLLCovariance4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLHessian4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance effectiveThroatMeasurableSpace :
    MeasurableSpace (EffectiveThroat period hPeriod) := borel _

local instance effectiveThroatBorelSpace :
    BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

/-- The raw differential LL density is half the diagonal of its flux Hessian
at the actual LL field, with all auxiliary backgrounds unchanged. -/
theorem differentialLLDensity_eq_half_fluxHessianDensity
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    differentialLLDensity period hPeriod frame fields point =
      (1 / 2 : Real) *
        differentialLLFluxHessianDensity period hPeriod frame fields
          fields.llField fields.llField point := by
  unfold differentialLLDensity differentialLLFluxHessianDensity
    llWorldvolumeDensity llFlux
  rw [throatDerivativePairing_self_eq_energy period hPeriod frame fields.llField point,
    real_inner_self_eq_norm_sq]
  ring

/-- Integrated reconstruction of the raw differential LL action. -/
theorem globalDifferentialLLAction_eq_half_fluxHessian
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) :
    globalDifferentialLLAction period hPeriod frame fields mu =
      (1 / 2 : Real) * globalDifferentialLLFluxHessian period hPeriod frame
        fields fields.llField fields.llField mu := by
  unfold globalDifferentialLLAction globalDifferentialLLFluxHessian
  rw [show differentialLLDensity period hPeriod frame fields =
      fun point => (1 / 2 : Real) *
        differentialLLFluxHessianDensity period hPeriod frame fields
          fields.llField fields.llField point from by
    funext point
    exact differentialLLDensity_eq_half_fluxHessianDensity period hPeriod
      frame fields point]
  rw [integral_const_mul]

/-- Exact reconstruction of the unchanged PT-averaged LL action from the
diagonal of its genuine mixed Hessian. -/
theorem globalPTSymmetricDifferentialLLAction_eq_half_fluxHessian
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) :
    globalPTSymmetricDifferentialLLAction period hPeriod frame fields mu =
      (1 / 2 : Real) *
        globalPTSymmetricDifferentialLLFluxHessian period hPeriod frame fields
          fields.llField fields.llField mu := by
  unfold globalPTSymmetricDifferentialLLAction
    globalPTSymmetricDifferentialLLFluxHessian
  rw [globalDifferentialLLAction_eq_half_fluxHessian period hPeriod frame
    fields mu]
  rw [globalDifferentialLLAction_eq_half_fluxHessian period hPeriod frame
    (llPTPullback period hPeriod fields) mu]
  change (1 / 2 : Real) *
      ((1 / 2 : Real) * globalDifferentialLLFluxHessian period hPeriod frame
          fields fields.llField fields.llField mu +
        (1 / 2 : Real) * globalDifferentialLLFluxHessian period hPeriod frame
          (llPTPullback period hPeriod fields)
          (differentialLLFluxDirectionPT period hPeriod fields.llField)
          (differentialLLFluxDirectionPT period hPeriod fields.llField) mu) = _
  ring

end

end P0EFTJanusDifferentialLLActionReconstruction4D
end JanusFormal
