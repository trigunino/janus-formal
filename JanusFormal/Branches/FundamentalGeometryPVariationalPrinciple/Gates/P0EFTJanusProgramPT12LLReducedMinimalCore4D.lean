import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12LLQuotientFriedrichsRealization4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12ClosedNullPMapCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12LLFullReducedQuotientCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12LLFullJacobiZeroFluxClosedDecomposition4D

/-! Concrete quotient-to-Friedrichs graph transport for the LL sector at
zero flux. The reduced closed Jacobi operator has trivial kernel. -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12LLReducedMinimalCore4D

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 600000
noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff ENNReal LinearPMap InnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusPTSymmetricLLWeakEulerJacobiOperator4D
open P0EFTJanusMappingTorusPTSymmetricLLH1RieszOperator4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalFullLLGraphRiesz4D
open P0EFTJanusProgramPT12LLSmoothL2Density4D
open P0EFTJanusProgramPT12LLFullSmoothL2Density4D
open P0EFTJanusProgramPT12LLFullJacobiClosure4D
open P0EFTJanusProgramPT12LLFullJacobiClosedSymmetry4D
open P0EFTJanusProgramPT12LLFullJacobiPureAuxMeasureL2Kernel4D
open P0EFTJanusProgramPT12ClosedNullPMapQuotient4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)

local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance : BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl
local instance : IsFiniteMeasure (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod

open P0EFTJanusProgramPT12LLFullJacobiHilbertQuotient4D
open P0EFTJanusProgramPT12LLFullSmoothReducedQuotient4D
open P0EFTJanusProgramPT12LLCanonicalH1ClosedDomain4D

open P0EFTJanusProgramPT12LLFullReducedQuotientCore4D
open P0EFTJanusProgramPT12LLFullJacobiZeroFluxClosedDecomposition4D
open P0EFTJanusProgramPT12LLCanonicalFriedrichsRealization4D

variable {configuration : GlobalFieldConfiguration period hPeriod}
variable {couplings : GlobalCandidateAActionCouplings}
variable {NonNullFace NullFace : Type*} [Fintype NonNullFace] [Fintype NullFace]
variable (data : GlobalCandidateAActionData period hPeriod configuration couplings NonNullFace NullFace)
variable (analysis : GlobalAnalysisData period hPeriod configuration)
variable (hZero : (data.boundary.llFields period hPeriod).llField = 0)

open P0EFTJanusProgramPT12ClosedNullPMapCore4D
open P0EFTJanusProgramPT12LLQuotientFriedrichsRealization4D

theorem fullLLJacobiClosedPMap_hasCore :
    (fullLLJacobiClosedPMap period hPeriod data analysis).HasCore
      (fullLLSmoothToHilbertLinearMap period hPeriod analysis).range :=
  (fullLLJacobiSmoothPMap period hPeriod data analysis).closureHasCore

include hZero in
/-- Genuine LL smooth fields form an operator core after removing auxiliary/measure null slots. -/
theorem fullLLReducedJacobi_hasCore :
    (fullLLReducedJacobi period hPeriod data analysis).HasCore
      (fullLLReducedHilbertCore period hPeriod analysis).range := by
  change (quotientPMap _ _).HasCore
    ((fullLLAuxMeasureNullSpace period hPeriod).mkQ.comp
      (fullLLSmoothToHilbertLinearMap period hPeriod analysis)).range
  rw [LinearMap.range_comp]
  exact quotientPMap_hasCore _ _
    (fullLLJacobiClosedPMap_isClosed period hPeriod data analysis)
    (fullLLJacobiClosedPMap_symmetric period hPeriod data analysis)
    (fullLLAuxMeasureNullSpace_graph_zero period hPeriod data analysis hZero) _
    (fullLLJacobiClosedPMap_hasCore period hPeriod data analysis)

include hZero in
/-- The Friedrichs smooth restriction closes to the actual minimal quotient Jacobi. -/
theorem quotientLLFriedrichs_smoothClosure_eq_minimal :
    ((quotientLLFriedrichs period hPeriod analysis).domRestrict
      (fullLLReducedHilbertCore period hPeriod analysis).range).closure =
    fullLLReducedJacobi period hPeriod data analysis :=
  extension_restriction_closure _ _
    (fullLLReducedJacobi_le_quotientFriedrichs period hPeriod analysis data hZero) _
    (fullLLReducedJacobi_hasCore period hPeriod data analysis hZero)

end
end P0EFTJanusProgramPT12LLReducedMinimalCore4D
end JanusFormal
