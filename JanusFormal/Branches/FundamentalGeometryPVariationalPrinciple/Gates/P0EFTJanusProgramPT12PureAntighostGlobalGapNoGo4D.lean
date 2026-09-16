import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12PureAntighostNonzeroWitness4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12PureAntighostAugmentedRieszIsotropic4D

/-! # A pure antighost obstructs a positive global Riesz floor -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12PureAntighostGlobalGapNoGo4D

set_option autoImplicit false
set_option maxHeartbeats 4200000
set_option synthInstance.maxHeartbeats 2100000
set_option maxRecDepth 4096

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff InnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateAFaithfulFredholmSum4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedFredholmSum4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalHilbertAugmentationObstruction4D
open P0EFTJanusProgramPT12PureAntighostNonzeroWitness4D
open P0EFTJanusProgramPT12PureAntighostBRSTIsotropic4D
open P0EFTJanusProgramPT12PureAntighostFullCoreIsotropic4D
open P0EFTJanusProgramPT12PureAntighostAugmentedRieszIsotropic4D

attribute [local instance]
  P0EFTJanusProgramPT12PureAntighostAugmentedRieszIsotropic4D.augmentedNormedAddCommGroup
  P0EFTJanusProgramPT12PureAntighostAugmentedRieszIsotropic4D.augmentedInnerProductSpace
  P0EFTJanusProgramPT12PureAntighostAugmentedRieszIsotropic4D.augmentedNormedSpace
  P0EFTJanusProgramPT12PureAntighostAugmentedRieszIsotropic4D.augmentedModule
  P0EFTJanusProgramPT12PureAntighostAugmentedRieszIsotropic4D.augmentedCompleteSpace

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

/-- The faithful augmented Riesz operator has no strictly positive global
quadratic lower bound. -/
theorem no_positive_global_riesz_floor
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (sameAction : ProgramPGlobalMinimalPhysicalLocalMatterLLSameActionBridge4D
      period hPeriod configuration data analysis chart)
    (physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D period
      hPeriod configuration data analysis chart sameAction) :
    ¬ ∃ c : Real, 0 < c ∧
      ∀ y : GlobalCandidateAFaithfulSameActionHilbert period hPeriod
          configuration data analysis,
        c * ‖y‖ ^ 2 ≤
          inner Real
            (globalCandidateAFaithfulAugmentedRieszOperator period hPeriod
              configuration data analysis chart sameAction physical y) y := by
  rintro ⟨c, hc, hFloor⟩
  obtain ⟨antighost, hAntighost⟩ :=
    exists_nonzero_globalDiffeomorphismAntighostField period hPeriod
  let core := pureAntighostCore period hPeriod configuration analysis antighost
  let metric := globalCandidateAMetricBySector period hPeriod data
  let x := diagonalExtendedBulkL2SmoothEmbedding period hPeriod metric
    couplings.matterMassSquared data analysis core
  have hNonminimal : pureAntighostNonminimal period hPeriod antighost ≠ 0 := by
    intro hZero
    apply hAntighost
    have hComponent := congrArg
      (fun state : GlobalDiffeomorphismNonminimalFields period hPeriod =>
        state.antighost) hZero
    change antighost = 0 at hComponent
    exact hComponent
  have hCore : core ≠ 0 := by
    intro hZero
    apply hNonminimal
    exact (globalCandidateAPureDiffeomorphismNonminimalCore_eq_zero_iff
      period hPeriod configuration analysis
      (pureAntighostNonminimal period hPeriod antighost)).mp hZero
  have hx : x ≠ 0 := by
    intro hZero
    apply hCore
    apply diagonalExtendedBulkL2SmoothEmbedding_injective period hPeriod metric
      couplings.matterMassSquared data analysis
    simpa only [map_zero] using hZero
  have hPairing :
      inner Real
          (globalCandidateAFaithfulAugmentedRieszOperator period hPeriod
            configuration data analysis chart sameAction physical x) x = 0 :=
    pureAntighost_faithfulAugmentedRiesz_pairing_self period hPeriod
      configuration data analysis chart sameAction physical antighost
  have hBound := hFloor x
  rw [hPairing] at hBound
  have hPositive : 0 < c * ‖x‖ ^ 2 :=
    mul_pos hc (sq_pos_of_pos ((norm_pos_iff).2 hx))
  exact (not_le_of_gt hPositive) hBound

end
end P0EFTJanusProgramPT12PureAntighostGlobalGapNoGo4D
end JanusFormal
