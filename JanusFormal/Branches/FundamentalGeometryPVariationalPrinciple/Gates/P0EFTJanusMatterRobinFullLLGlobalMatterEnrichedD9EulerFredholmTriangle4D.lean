import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMatterRobinFullLLGlobalMatterEnrichedD9EulerHessianTriangle4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMatterRobinFullLLGlobalMatterEnrichedD9ReducedFredholmPairing4D

/-!
# Actual Euler--D9--reduced Fredholm triangle on the smooth Robin--LL slice

Along the smooth Robin--LL directions, the derivative of the representative
Euler curve of the actual matter+Robin+LL action is exactly the reduced Jacobi
pairing.  The reduced scalar slot is zero here; no metric, gauge or ghost block
and no global Program-P Fredholm family is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusMatterRobinFullLLGlobalMatterEnrichedD9EulerFredholmTriangle4D
set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff Topology
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusScalarDiffeomorphismNoetherOperator4D
open P0EFTJanusGlobalMatterMultipletActualEulerHessian4D
open P0EFTJanusCommonMatterActionVariation4D
open P0EFTJanusFullMatterRobinLLDirections4D
open P0EFTJanusMatterRobinFullLLReducedFredholmBlock4D
open P0EFTJanusMatterRobinFullLLActiveQuotientEulerVariation4D
open P0EFTJanusMatterRobinFullLLGlobalMatterEnrichedD9EulerHessianTriangle4D
open P0EFTJanusMatterRobinFullLLGlobalMatterEnrichedD9ReducedFredholmPairing4D
open P0EFTJanusMappingTorusReducedBosonicNaturalFredholmHessian4D
open P0EFTJanusMappingTorusPTSymmetricLLH1RieszOperator4D
open P0EFTJanusMappingTorusScalarRobinJunctionL2Fredholm4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarWeakJacobiRiesz4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusCompleteGaugeFixedEllipticSymbol

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

theorem representativeEulerCurve_hasDerivAt_reducedJacobi_pairing_on_robinLL
    (matterData : MatterMultipletActionData period hPeriod)
    (scalarData : PositiveStaticGlobalScalarData period hPeriod) (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure robinMeasure]
    (llData : PositiveLLH1Data period hPeriod) [IsFiniteMeasure llData.mu]
    (matter : MatterComponentFamily period hPeriod)
    (junction : SmoothThroatField period hPeriod Real)
    (sector : Sector) (column : Fin 2) (point : EffectiveThroat period hPeriod)
    (robinFirst robinSecond : SmoothThroatField period hPeriod Real)
    (llFirst llSecond : LLH1Smooth period hPeriod llData) :
    HasDerivAt
      (representativeEulerCurve period hPeriod matterData kPlus kMinus bulkPlus bulkMinus
        robinMeasure (finiteSmoothThroatGeneratingFrame period hPeriod) llData.mu matter junction
        llData.fields (fullRobinLLDirection period hPeriod robinFirst llFirst.toTest)
        (fullRobinLLDirection period hPeriod robinSecond llSecond.toTest))
      (reducedBosonicNaturalHessian period hPeriod scalarData kPlus kMinus robinMeasure llData
        (staticScalarEnergyEmbedding period hPeriod scalarData 0,
          smoothThroatFieldToL2 period hPeriod robinMeasure robinFirst,
          llH1SmoothEmbedding period hPeriod llData llFirst)
        (staticScalarEnergyEmbedding period hPeriod scalarData 0,
          smoothThroatFieldToL2 period hPeriod robinMeasure robinSecond,
          llH1SmoothEmbedding period hPeriod llData llSecond)) 0 := by
  have h := representativeEulerCurve_hasDerivAt_enrichedD9ActiveHessian
    period hPeriod matterData kPlus kMinus bulkPlus bulkMinus robinMeasure
    (finiteSmoothThroatGeneratingFrame period hPeriod) llData.mu matter junction llData.fields
    sector column point (fullRobinLLDirection period hPeriod robinFirst llFirst.toTest)
    (fullRobinLLDirection period hPeriod robinSecond llSecond.toTest)
  rw [enrichedD9_robinLL_Hessian_eq_reducedJacobi_pairing period hPeriod matterData scalarData
    kPlus kMinus robinMeasure llData sector column point robinFirst robinSecond llFirst llSecond] at h
  exact h

end
end P0EFTJanusMatterRobinFullLLGlobalMatterEnrichedD9EulerFredholmTriangle4D
end JanusFormal
