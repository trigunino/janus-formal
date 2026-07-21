import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCommonMatterRobinLLReducedKernelCanonicalRobin4D

/-! Complete kernel statement on the smooth Robin--LL inclusion for the canonical measure. -/

namespace JanusFormal
namespace P0EFTJanusCommonMatterRobinLLReducedKernelCanonicalSharedInclusion4D
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
open P0EFTJanusCommonMatterRobinLLReducedKernelCanonicalRobin4D

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

theorem reducedJacobi_canonical_shared_inclusion_kernel_components
    (scalarData : PositiveStaticGlobalScalarData period hPeriod)
    (kPlus kMinus : Real) (hCoupling : kPlus + kMinus ≠ 0)
    (llData : PositiveLLH1Data period hPeriod)
    (robin : SmoothThroatField period hPeriod Real) (ll : LLH1Smooth period hPeriod llData)
    (hZero : reducedBosonicJacobiOperator period hPeriod scalarData kPlus kMinus
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) llData
      (reducedRobinLLInclusion period hPeriod scalarData
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) llData robin ll) = 0) :
    robin = 0 ∧ llH1SmoothEmbedding period hPeriod llData ll = 0 := by
  constructor
  · exact reducedJacobi_canonical_shared_kernel_robin_eq_zero period hPeriod scalarData
      kPlus kMinus hCoupling llData robin ll hZero
  · have hIncluded := reducedBosonicJacobiOperator_shared_inclusion_kernel period hPeriod scalarData
      kPlus kMinus hCoupling (intrinsicCanonicalThroatVolumeMeasure period hPeriod)
        llData robin ll hZero
    have hLL := congrArg (fun value => value.2.2) hIncluded
    simpa [reducedRobinLLInclusion] using hLL

end
end P0EFTJanusCommonMatterRobinLLReducedKernelCanonicalSharedInclusion4D
end JanusFormal
