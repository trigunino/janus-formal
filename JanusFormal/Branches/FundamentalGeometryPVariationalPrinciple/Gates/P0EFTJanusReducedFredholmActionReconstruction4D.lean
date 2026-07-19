import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusReducedBosonicActionReconstruction4D

namespace JanusFormal
namespace P0EFTJanusReducedFredholmActionReconstruction4D

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
open P0EFTJanusMappingTorusScalarRobinJunctionBalance4D
open P0EFTJanusMappingTorusScalarRobinJunctionL2Fredholm4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricLLH1RieszOperator4D
open P0EFTJanusMappingTorusReducedBosonicNaturalFredholmHessian4D
open P0EFTJanusMappingTorusReducedBosonicActualActionHessian4D
open P0EFTJanusReducedBosonicActionReconstruction4D

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

/-- The LL field stored by the positive LL data, viewed in its genuine smooth
LLH¹ form domain. -/
def storedLLH1Smooth (data : PositiveLLH1Data period hPeriod) :
    LLH1Smooth period hPeriod data :=
  LLH1Smooth.ofTest period hPeriod data data.fields.llField

@[simp] theorem storedLLH1Smooth_toTest
    (data : PositiveLLH1Data period hPeriod) :
    (storedLLH1Smooth period hPeriod data).toTest = data.fields.llField :=
  rfl

/-- On the smooth diagonal of the completed reduced Fredholm domain, the
pairing reconstructs the same assembled reduced action after retaining the
necessary affine Robin terms. -/
theorem reducedBosonicSmoothAction_reconstructed_from_naturalFredholmDiagonal
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure robinMeasure]
    (llData : PositiveLLH1Data period hPeriod)
    (scalar : StaticGlobalScalarTest period hPeriod scalarData)
    (junction : SmoothThroatField period hPeriod Real) :
    reducedBosonicSmoothAction period hPeriod scalarData kPlus kMinus bulkPlus
        bulkMinus robinMeasure (finiteSmoothThroatGeneratingFrame period hPeriod)
        llData.mu scalar.toField junction llData.fields =
      robinJunctionAction period hPeriod kPlus kMinus bulkPlus bulkMinus
          (0 : SmoothThroatField period hPeriod Real) robinMeasure +
        robinFirstVariation period hPeriod kPlus kMinus bulkPlus bulkMinus
          (0 : SmoothThroatField period hPeriod Real) junction robinMeasure +
        (1 / 2 : Real) *
          reducedBosonicNaturalHessian period hPeriod scalarData kPlus kMinus
            robinMeasure llData
            (staticScalarEnergyEmbedding period hPeriod scalarData scalar,
              smoothThroatFieldToL2 period hPeriod robinMeasure junction,
              llH1SmoothEmbedding period hPeriod llData
                (storedLLH1Smooth period hPeriod llData))
            (staticScalarEnergyEmbedding period hPeriod scalarData scalar,
              smoothThroatFieldToL2 period hPeriod robinMeasure junction,
              llH1SmoothEmbedding period hPeriod llData
                (storedLLH1Smooth period hPeriod llData)) := by
  letI : IsFiniteMeasure llData.mu := llData.finiteMeasure
  rw [reducedBosonicSmoothAction_reconstructed_from_euler_and_actualHessian
    period hPeriod scalarData kPlus kMinus bulkPlus bulkMinus robinMeasure
    (finiteSmoothThroatGeneratingFrame period hPeriod) llData.mu scalar.toField
    junction llData.fields]
  rw [reducedBosonicNaturalHessian_smooth_eq_assembledActionMixedHessian
    period hPeriod scalarData kPlus kMinus robinMeasure llData scalar.toField
    bulkPlus bulkMinus junction scalar scalar junction junction
    (storedLLH1Smooth period hPeriod llData)
    (storedLLH1Smooth period hPeriod llData)]
  simp only [storedLLH1Smooth_toTest]

end

end P0EFTJanusReducedFredholmActionReconstruction4D
end JanusFormal
