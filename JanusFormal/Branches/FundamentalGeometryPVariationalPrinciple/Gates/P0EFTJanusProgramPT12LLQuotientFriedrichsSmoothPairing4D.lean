import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12LLQuotientFriedrichsRealization4D

/-! Smooth full-LL same-action pairing on the canonical quotient realization. -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12LLQuotientFriedrichsSmoothPairing4D

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000
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

open P0EFTJanusProgramPT12LLFullReducedFriedrichsBridge4D
open P0EFTJanusProgramPT12IsometricPMapTransport4D

open P0EFTJanusProgramPT12LLQuotientFriedrichsRealization4D
open P0EFTJanusProgramPGlobalFullLLOnShellFredholmReduction4D
open P0EFTJanusMappingTorusPTSymmetricLLWeakEulerJacobiOperator4D
open P0EFTJanusMappingTorusLLH1SmoothEmbeddingKernel4D
open P0EFTJanusProgramPLL2EllipticNuclearHeatRegulator4D

variable {configuration : GlobalFieldConfiguration period hPeriod}
variable (analysis : GlobalAnalysisData period hPeriod configuration)

/-- Actual smooth quotient directions as Friedrichs domain elements. -/
def quotientLLFriedrichsSmoothDomainElement
    (direction : GlobalFullLLSmooth period hPeriod analysis) :
    (quotientLLFriedrichs period hPeriod analysis).domain :=
  (transportedDomainEquiv (fullLLReducedHilbertToCanonical period hPeriod analysis)
    (canonicalLLFriedrichsJacobi period hPeriod analysis)).symm
      (canonicalLLFriedrichsSmoothDomainElement period hPeriod analysis direction.2)

theorem quotientLLFriedrichsSmoothDomainElement_value
    (direction : GlobalFullLLSmooth period hPeriod analysis) :
    (quotientLLFriedrichsSmoothDomainElement period hPeriod analysis direction :
      FullLLReducedHilbert period hPeriod) = fullLLReducedHilbertCore period hPeriod analysis direction := by
  apply (fullLLReducedHilbertToCanonical period hPeriod analysis).injective
  change fullLLReducedHilbertToCanonical period hPeriod analysis
      ((fullLLReducedHilbertToCanonical period hPeriod analysis).symm
        (canonicalLLFriedrichsSmoothDomainElement period hPeriod analysis direction.2)) = _
  rw [LinearIsometryEquiv.apply_symm_apply, canonicalLLFriedrichsSmoothDomainElement_value]
  rfl

theorem quotientLLFriedrichs_on_smooth
    (direction : GlobalFullLLSmooth period hPeriod analysis) :
    fullLLReducedHilbertToCanonical period hPeriod analysis
      (quotientLLFriedrichs period hPeriod analysis
        (quotientLLFriedrichsSmoothDomainElement period hPeriod analysis direction)) =
      canonicalLLFriedrichsJacobi period hPeriod analysis
        (canonicalLLFriedrichsSmoothDomainElement period hPeriod analysis direction.2) := by
  exact (transportedPMap_action _ _ _).trans
    (congrArg (canonicalLLFriedrichsJacobi period hPeriod analysis)
      ((transportedDomainEquiv (fullLLReducedHilbertToCanonical period hPeriod analysis)
        (canonicalLLFriedrichsJacobi period hPeriod analysis)).apply_symm_apply _))

/-- The transported operator has the same smooth energy pairing. -/
theorem quotientLLFriedrichs_smooth_energy_pairing
    (first second : GlobalFullLLSmooth period hPeriod analysis) :
    inner Real (quotientLLFriedrichs period hPeriod analysis
        (quotientLLFriedrichsSmoothDomainElement period hPeriod analysis first))
      (fullLLReducedHilbertCore period hPeriod analysis second) =
      inner Real (llH1SmoothEmbedding period hPeriod (analysis.llH1Data period hPeriod) first.2)
        (llH1SmoothEmbedding period hPeriod (analysis.llH1Data period hPeriod) second.2) := by
  rw [← (fullLLReducedHilbertToCanonical period hPeriod analysis).inner_map_map,
    quotientLLFriedrichs_on_smooth]
  have hSecond : fullLLReducedHilbertToCanonical period hPeriod analysis
      (fullLLReducedHilbertCore period hPeriod analysis second) =
        (canonicalLLFriedrichsSmoothDomainElement period hPeriod analysis second.2 :
          CanonicalLLL2 period hPeriod analysis) := by
    rw [canonicalLLFriedrichsSmoothDomainElement_value]
    rfl
  rw [hSecond, canonicalLLFriedrichsJacobi_smooth_pairing]
  exact (weakLLJacobiH1Extension_apply_smooth period hPeriod
    (analysis.llH1Data period hPeriod) first.2 second.2).symm

variable {couplings : GlobalCandidateAActionCouplings}
variable {NonNullFace NullFace : Type*} [Fintype NonNullFace] [Fintype NullFace]
variable (data : GlobalCandidateAActionData period hPeriod configuration couplings NonNullFace NullFace)
variable (hZero : (data.boundary.llFields period hPeriod).llField = 0)

include hZero in
/-- Exact same-action pairing, including arbitrary auxiliary and measure
components of both smooth representatives, at zero background flux. -/
theorem quotientLLFriedrichs_smooth_sameAction_pairing
    (first second : GlobalFullLLSmooth period hPeriod analysis) :
    inner Real (quotientLLFriedrichs period hPeriod analysis
        (quotientLLFriedrichsSmoothDomainElement period hPeriod analysis first))
      (fullLLReducedHilbertCore period hPeriod analysis second) =
      globalCandidateAFullLLSameActionHessian period hPeriod data first second := by
  rw [quotientLLFriedrichs_smooth_energy_pairing,
    ← globalCandidateAFullLLContinuousHessian_smooth period hPeriod data analysis,
    globalCandidateAFullLLContinuousHessian_zeroFlux period hPeriod data analysis hZero,
    globalCandidateAFullLLFieldProjection_smooth, globalCandidateAFullLLFieldProjection_smooth]

end
end P0EFTJanusProgramPT12LLQuotientFriedrichsSmoothPairing4D
end JanusFormal
