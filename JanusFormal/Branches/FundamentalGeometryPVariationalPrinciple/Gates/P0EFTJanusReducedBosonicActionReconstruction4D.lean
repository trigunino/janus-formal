import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGlobalHolonomicScalarActionReconstruction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusRobinJunctionActionReconstruction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusDifferentialLLActionReconstruction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusReducedBosonicActualActionHessian4D

namespace JanusFormal
namespace P0EFTJanusReducedBosonicActionReconstruction4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarWeakJacobiRiesz4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarActualHessian4D
open P0EFTJanusMappingTorusScalarRobinJunctionBalance4D
open P0EFTJanusMappingTorusScalarRobinJunctionHessian4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLHessian4D
open P0EFTJanusMappingTorusReducedBosonicNaturalFredholmHessian4D
open P0EFTJanusMappingTorusReducedBosonicActualActionHessian4D
open P0EFTJanusGlobalHolonomicScalarActionReconstruction4D
open P0EFTJanusRobinJunctionActionReconstruction4D
open P0EFTJanusDifferentialLLActionReconstruction4D

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

/-- Reconstruction of the single reduced bosonic action.  Only the Robin
block contributes an affine constant and linear term; the remaining sum is
half the simultaneous diagonal of the genuine assembled Hessian. -/
theorem reducedBosonicSmoothAction_reconstructed_from_euler_and_actualHessian
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure llMeasure]
    (scalar : GlobalScalarTestSpace period hPeriod)
    (junction : SmoothThroatField period hPeriod Real)
    (llFields : IndependentFields period hPeriod) :
    reducedBosonicSmoothAction period hPeriod scalarData kPlus kMinus bulkPlus
        bulkMinus robinMeasure frame llMeasure scalar junction llFields =
      robinJunctionAction period hPeriod kPlus kMinus bulkPlus bulkMinus
          (0 : SmoothThroatField period hPeriod Real) robinMeasure +
        robinFirstVariation period hPeriod kPlus kMinus bulkPlus bulkMinus
          (0 : SmoothThroatField period hPeriod Real) junction robinMeasure +
        (1 / 2 : Real) *
          reducedBosonicSmoothActionMixedHessian period hPeriod scalarData
            kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure
            scalar scalar scalar junction junction junction llFields
            llFields.llField llFields.llField := by
  unfold reducedBosonicSmoothAction
  rw [globalHolonomicScalarAction_eq_half_actualMixedHessian period hPeriod
    scalarData.formData scalar scalar]
  rw [globalHolonomicScalarActionMixedHessian_eq_jacobi period hPeriod
    scalarData.formData scalar scalar scalar]
  rw [robinJunctionAction_reconstructed_from_euler_and_actualHessian period
    hPeriod kPlus kMinus bulkPlus bulkMinus junction junction robinMeasure]
  rw [robinJunctionActionMixedHessian_eq_robinHessian period hPeriod kPlus
    kMinus bulkPlus bulkMinus junction junction junction robinMeasure]
  rw [globalPTSymmetricDifferentialLLAction_eq_half_fluxHessian period hPeriod
    frame llFields llMeasure]
  rw [reducedBosonicSmoothActionMixedHessian_eq period hPeriod scalarData
    kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure scalar scalar
    scalar junction junction junction llFields llFields.llField llFields.llField]
  ring

end

end P0EFTJanusReducedBosonicActionReconstruction4D
end JanusFormal
