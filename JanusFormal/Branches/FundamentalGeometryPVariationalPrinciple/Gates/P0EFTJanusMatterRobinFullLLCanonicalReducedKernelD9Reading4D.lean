import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCommonMatterRobinLLReducedKernelCanonicalSharedInclusion4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusLLH1SmoothEmbeddingKernel4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMatterRobinFullLLGlobalMatterEnrichedD9ReducedKernel4D

/-! Canonical reduced-kernel consequences on the smooth Robin--LL D9 reading. -/

namespace JanusFormal
namespace P0EFTJanusMatterRobinFullLLCanonicalReducedKernelD9Reading4D
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
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusScalarRobinJunctionL2Fredholm4D
open P0EFTJanusMappingTorusReducedBosonicNaturalFredholmHessian4D
open P0EFTJanusMappingTorusPTSymmetricLLH1RieszOperator4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarWeakJacobiRiesz4D
open P0EFTJanusMappingTorusLLH1SmoothEmbeddingKernel4D
open P0EFTJanusCommonMatterRobinLLReducedFredholmOperatorPairing4D
open P0EFTJanusCommonMatterRobinLLReducedKernelCanonicalSharedInclusion4D
open P0EFTJanusMatterRobinFullLLReducedFredholmBlock4D
open P0EFTJanusMatterRobinFullLLActiveQuotientHessian4D
open P0EFTJanusFullMatterRobinLLGlobalMatterEnrichedD9Projection4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusCompleteGaugeFixedEllipticSymbol

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)
local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) := fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) := fixedThroatQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveThroat period hPeriod) := fixedThroatQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance : BorelSpace (EffectiveThroat period hPeriod) where measurable_eq := rfl
local instance : IsFiniteMeasure (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod
local instance : Measure.IsOpenPosMeasure (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  intrinsicCanonicalThroatVolumeMeasure_isOpenPosMeasure period hPeriod

def zeroRobinLLActiveDirection : ActiveDirection period hPeriod where
  matter := 0
  robin := 0
  llField := 0
  llAuxMetric := 0
  llMeasure := 0

theorem reducedJacobi_canonical_kernel_robin_ll_and_D9_reading_zero
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (kPlus kMinus : Real) (hCoupling : kPlus + kMinus ≠ 0)
    (llData : PositiveLLH1Data period hPeriod)
    (sector : Sector) (column : Fin 2) (point : EffectiveThroat period hPeriod)
    (robin : SmoothThroatField period hPeriod Real) (ll : LLH1Smooth period hPeriod llData)
    (hZero : reducedBosonicJacobiOperator period hPeriod scalarData kPlus kMinus
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) llData
      (reducedRobinLLInclusion period hPeriod scalarData
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) llData robin ll) = 0) :
    robin = 0 ∧ ll = 0 ∧
      toActiveDirection period hPeriod
        (globalMatterEnrichedD9Projection period hPeriod llData.fields
          (fullRobinLLDirection period hPeriod robin ll.toTest) sector column point) =
        zeroRobinLLActiveDirection period hPeriod := by
  have hComponents := reducedJacobi_canonical_shared_inclusion_kernel_components period hPeriod
    scalarData kPlus kMinus hCoupling llData robin ll hZero
  have hLL : ll = 0 :=
    (llH1SmoothEmbedding_eq_zero_iff period hPeriod llData ll).mp hComponents.2
  refine ⟨hComponents.1, hLL, ?_⟩
  rw [hComponents.1, hLL]
  rfl

end
end P0EFTJanusMatterRobinFullLLCanonicalReducedKernelD9Reading4D
end JanusFormal
