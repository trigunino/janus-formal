import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusReducedBosonicActualActionHessian4D

namespace JanusFormal
namespace P0EFTJanusReducedBosonicActualEulerLinearization4D

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
open P0EFTJanusMappingTorusGlobalHolonomicScalarVariation4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarWeakJacobiRiesz4D
open P0EFTJanusMappingTorusScalarRobinJunctionBalance4D
open P0EFTJanusMappingTorusScalarRobinJunctionHessian4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLWeakEquation4D
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

/-- The Euler functional of the single reduced bosonic action is genuinely
differentiable along simultaneous scalar, Robin, and LL background curves;
its derivative is the actual mixed Hessian of that same action. -/
theorem reducedBosonicSmoothEuler_hasDerivAt
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
    HasDerivAt
      (fun epsilon : Real =>
        reducedBosonicSmoothActionDirectionalDerivative period hPeriod scalarData
          kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure
          (scalarAffineCurve period hPeriod scalar scalarFirst epsilon) scalarSecond
          (junctionAffineCurve period hPeriod junction robinFirst epsilon) robinSecond
          (differentialLLFluxCurve period hPeriod llFields llFirst epsilon) llSecond)
      (reducedBosonicSmoothActionMixedHessian period hPeriod scalarData kPlus
        kMinus bulkPlus bulkMinus robinMeasure frame llMeasure scalar scalarFirst
        scalarSecond junction robinFirst robinSecond llFields llFirst llSecond) 0 := by
  rw [show (fun epsilon : Real =>
      reducedBosonicSmoothActionDirectionalDerivative period hPeriod scalarData
        kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure
        (scalarAffineCurve period hPeriod scalar scalarFirst epsilon) scalarSecond
        (junctionAffineCurve period hPeriod junction robinFirst epsilon) robinSecond
        (differentialLLFluxCurve period hPeriod llFields llFirst epsilon) llSecond) =
      (fun epsilon : Real =>
        weakGlobalHolonomicScalarEulerOperator period hPeriod scalarData.formData
            (scalarAffineCurve period hPeriod scalar scalarFirst epsilon) scalarSecond +
          robinFirstVariation period hPeriod kPlus kMinus bulkPlus bulkMinus
            (junctionAffineCurve period hPeriod junction robinFirst epsilon)
            robinSecond robinMeasure +
          globalPTSymmetricDifferentialLLFluxFirstVariation period hPeriod frame
            (differentialLLFluxCurve period hPeriod llFields llFirst epsilon)
            llSecond llMeasure) from by
    funext epsilon
    exact reducedBosonicSmoothActionDirectionalDerivative_eq period hPeriod
      scalarData kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure
      (scalarAffineCurve period hPeriod scalar scalarFirst epsilon) scalarSecond
      (junctionAffineCurve period hPeriod junction robinFirst epsilon) robinSecond
      (differentialLLFluxCurve period hPeriod llFields llFirst epsilon) llSecond]
  rw [reducedBosonicSmoothActionMixedHessian_eq period hPeriod scalarData kPlus
    kMinus bulkPlus bulkMinus robinMeasure frame llMeasure scalar scalarFirst
    scalarSecond junction robinFirst robinSecond llFields llFirst llSecond]
  exact ((weakGlobalHolonomicScalarEulerOperator_hasDerivAt period hPeriod
      scalarData.formData scalar scalarFirst scalarSecond).add
    (robinWeakBalance_linearized_hasDerivAt period hPeriod kPlus kMinus
      bulkPlus bulkMinus junction robinFirst robinSecond robinMeasure)).add
    (globalPTSymmetricDifferentialLLFluxFirstVariation_fluxCurve_hasDerivAt
      period hPeriod frame llFields llFirst llSecond llMeasure)

end

end P0EFTJanusReducedBosonicActualEulerLinearization4D
end JanusFormal
