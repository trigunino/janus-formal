import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusReducedBosonicActualActionHessian4D

namespace JanusFormal
namespace P0EFTJanusReducedBosonicActualHelmholtz4D

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
open P0EFTJanusMappingTorusScalarRobinJunctionHessian4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLHessian4D
open P0EFTJanusMappingTorusReducedBosonicNaturalFredholmHessian4D
open P0EFTJanusMappingTorusReducedBosonicActualActionHessian4D

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

/-- Helmholtz symmetry for the genuine mixed Hessian of the single assembled
reduced bosonic action, under simultaneous exchange of all three directions. -/
theorem reducedBosonicSmoothActionMixedHessian_symmetric
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure llMeasure]
    (scalar scalarFirst scalarSecond : GlobalScalarTestSpace period hPeriod)
    (junction robinFirst robinSecond : SmoothThroatField period hPeriod Real)
    (llFields : IndependentFields period hPeriod)
    (llFirst llSecond : SmoothThroatField period hPeriod LLFieldFiber) :
    reducedBosonicSmoothActionMixedHessian period hPeriod scalarData kPlus
        kMinus bulkPlus bulkMinus robinMeasure frame llMeasure scalar scalarFirst
        scalarSecond junction robinFirst robinSecond llFields llFirst llSecond =
      reducedBosonicSmoothActionMixedHessian period hPeriod scalarData kPlus
        kMinus bulkPlus bulkMinus robinMeasure frame llMeasure scalar scalarSecond
        scalarFirst junction robinSecond robinFirst llFields llSecond llFirst := by
  rw [reducedBosonicSmoothActionMixedHessian_eq period hPeriod scalarData kPlus
      kMinus bulkPlus bulkMinus robinMeasure frame llMeasure scalar scalarFirst
      scalarSecond junction robinFirst robinSecond llFields llFirst llSecond,
    reducedBosonicSmoothActionMixedHessian_eq period hPeriod scalarData kPlus
      kMinus bulkPlus bulkMinus robinMeasure frame llMeasure scalar scalarSecond
      scalarFirst junction robinSecond robinFirst llFields llSecond llFirst]
  rw [weakGlobalHolonomicScalarJacobiOperator_symmetric period hPeriod
      scalarData.formData scalarFirst scalarSecond,
    robinHessian_symmetric period hPeriod kPlus kMinus robinFirst robinSecond
      robinMeasure,
    globalPTSymmetricDifferentialLLFluxHessian_comm period hPeriod frame
      llFields llFirst llSecond llMeasure]

end

end P0EFTJanusReducedBosonicActualHelmholtz4D
end JanusFormal
