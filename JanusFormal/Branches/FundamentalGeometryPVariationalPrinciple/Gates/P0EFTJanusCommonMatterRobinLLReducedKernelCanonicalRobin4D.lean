import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCommonMatterRobinLLReducedKernelFullSupportRobin4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalRobinL2Injection4D

/-! Pointwise Robin consequence of the reduced Jacobi kernel for the actual canonical throat measure. -/

namespace JanusFormal
namespace P0EFTJanusCommonMatterRobinLLReducedKernelCanonicalRobin4D
set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff Topology
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusScalarRobinJunctionL2Fredholm4D
open P0EFTJanusMappingTorusReducedBosonicNaturalFredholmHessian4D
open P0EFTJanusMappingTorusPTSymmetricLLH1RieszOperator4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarWeakJacobiRiesz4D
open P0EFTJanusCommonMatterRobinLLReducedFredholmOperatorPairing4D
open P0EFTJanusCommonMatterRobinLLReducedKernelFullSupportRobin4D

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

theorem reducedJacobi_canonical_shared_kernel_robin_eq_zero
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (kPlus kMinus : Real) (hCoupling : kPlus + kMinus ≠ 0)
    (llData : PositiveLLH1Data period hPeriod)
    (robin : SmoothThroatField period hPeriod Real) (ll : LLH1Smooth period hPeriod llData)
    (hZero : reducedBosonicJacobiOperator period hPeriod scalarData kPlus kMinus
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) llData
      (reducedRobinLLInclusion period hPeriod scalarData
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) llData robin ll) = 0) :
    robin = 0 := by
  exact reducedJacobi_shared_kernel_robin_eq_zero_of_fullSupport period hPeriod scalarData
    kPlus kMinus hCoupling (intrinsicCanonicalThroatVolumeMeasure period hPeriod)
      llData robin ll hZero

end
end P0EFTJanusCommonMatterRobinLLReducedKernelCanonicalRobin4D
end JanusFormal
