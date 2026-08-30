import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSeparatingPDEResidual4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAAugmentedFredholmSum4D

/-!
# Strong residual of the full augmented Candidate-A Hessian

This adds the seven retained physical action blocks to the faithful
BRST--SpinC--LL graph residual.  The result is conditional only on the
existing same-action bridge and bounded common-domain physical extension.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeFaithfulAugmentedRieszResidual4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1200000

noncomputable section

open Set Topology MeasureTheory
open scoped Manifold ContDiff InnerProductSpace
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalLocalHessianBridge4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedFredholmSum4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSeparatingPDEResidual4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

/-- Strong residual of the complete augmented Candidate-A Hessian. -/
def globalCandidateAFaithfulAugmentedRieszResidual
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
      hPeriod configuration data analysis chart sameAction)
    (state : CommonAugmentedHilbert period hPeriod configuration data analysis) :
    CommonAugmentedHilbert period hPeriod configuration data analysis :=
  globalCandidateACommonAugmentedRieszOperator period hPeriod configuration
    data analysis chart sameAction physical state

/-- Hilbert pairing of the complete augmented residual. -/
def globalCandidateAFaithfulAugmentedRieszResidualPairing
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (residual test : CommonAugmentedHilbert period hPeriod configuration data
      analysis) : Real :=
  inner Real residual test

/-- The full augmented Hessian is represented by its strong residual. -/
theorem globalCandidateAFaithfulAugmentedHessian_eq_rieszResidualPairing
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
      hPeriod configuration data analysis chart sameAction)
    (state test : CommonAugmentedHilbert period hPeriod configuration data
      analysis) :
    globalCandidateACommonAugmentedHessian period hPeriod configuration data
        analysis chart sameAction physical state test =
      globalCandidateAFaithfulAugmentedRieszResidualPairing period hPeriod
        configuration data analysis
          (globalCandidateAFaithfulAugmentedRieszResidual period hPeriod
            configuration data analysis chart sameAction physical state) test := by
  simpa only [globalCandidateAFaithfulAugmentedRieszResidualPairing,
    globalCandidateAFaithfulAugmentedRieszResidual] using
      (globalCandidateACommonAugmentedRieszOperator_pairing period hPeriod
        configuration data analysis chart sameAction physical state test).symm

/-- Hilbert tests separate the complete augmented residual. -/
theorem globalCandidateAFaithfulAugmentedRieszResidualPairing_separates
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (residual : CommonAugmentedHilbert period hPeriod configuration data
      analysis) :
    (∀ test, globalCandidateAFaithfulAugmentedRieszResidualPairing period
      hPeriod configuration data analysis residual test = 0) ↔ residual = 0 := by
  constructor
  · intro hPairing
    exact inner_self_eq_zero.mp (hPairing residual)
  · intro hResidual test
    rw [hResidual]
    exact inner_zero_left test

/-- Separating representation of the full augmented Euler covector. -/
def globalCandidateAFaithfulAugmentedRieszResidualRepresentation
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
      hPeriod configuration data analysis chart sameAction)
    (state : CommonAugmentedHilbert period hPeriod configuration data analysis) :
    SeparatingPDEResidualRepresentation
      (fderiv Real
        (globalCandidateACommonAugmentedAction period hPeriod configuration data
          analysis chart sameAction physical) state).toLinearMap where
  Residual := CommonAugmentedHilbert period hPeriod configuration data analysis
  zeroResidual := 0
  residual := globalCandidateAFaithfulAugmentedRieszResidual period hPeriod
    configuration data analysis chart sameAction physical state
  pairing := globalCandidateAFaithfulAugmentedRieszResidualPairing period
    hPeriod configuration data analysis
  represents := by
    intro test
    rw [globalCandidateACommonAugmentedAction_fderiv period hPeriod
      configuration data analysis chart sameAction physical state]
    exact globalCandidateAFaithfulAugmentedHessian_eq_rieszResidualPairing
      period hPeriod configuration data analysis chart sameAction physical state
        test
  separates :=
    globalCandidateAFaithfulAugmentedRieszResidualPairing_separates period
      hPeriod configuration data analysis
        (globalCandidateAFaithfulAugmentedRieszResidual period hPeriod
          configuration data analysis chart sameAction physical state)

/-- The full augmented Euler covector vanishes exactly when its strong Riesz
residual vanishes. -/
theorem globalCandidateAFaithfulAugmentedEulerCovector_eq_zero_iff_rieszResidual
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
      hPeriod configuration data analysis chart sameAction)
    (state : CommonAugmentedHilbert period hPeriod configuration data analysis) :
    fderiv Real
        (globalCandidateACommonAugmentedAction period hPeriod configuration data
          analysis chart sameAction physical) state = 0 ↔
      globalCandidateAFaithfulAugmentedRieszResidual period hPeriod
        configuration data analysis chart sameAction physical state = 0 := by
  let representation :=
    globalCandidateAFaithfulAugmentedRieszResidualRepresentation period hPeriod
      configuration data analysis chart sameAction physical state
  constructor
  · intro hEuler
    apply (separatingPDEResidualRepresentation_covector_eq_zero_iff
      representation).mp
    exact congrArg ContinuousLinearMap.toLinearMap hEuler
  · intro hResidual
    apply ContinuousLinearMap.ext
    intro test
    have hCovector :=
      (separatingPDEResidualRepresentation_covector_eq_zero_iff
        representation).mpr hResidual
    exact LinearMap.congr_fun hCovector test

/-- On the dense smooth core, the residual pairing is the genuine local
gauge-fixed Candidate-A Hessian, including all seven physical blocks. -/
theorem globalCandidateAFaithfulAugmentedRieszResidual_smooth_pairing
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
      hPeriod configuration data analysis chart sameAction)
    (first second : GlobalCandidateADiagonalExtendedBulkSmoothCore period
      hPeriod analysis) :
    globalCandidateAFaithfulAugmentedRieszResidualPairing period hPeriod
        configuration data analysis
        (globalCandidateAFaithfulAugmentedRieszResidual period hPeriod
          configuration data analysis chart sameAction physical
          (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
            (globalCandidateAMetricBySector period hPeriod data)
            couplings.matterMassSquared data analysis first))
        (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
          (globalCandidateAMetricBySector period hPeriod data)
          couplings.matterMassSquared data analysis second) =
      diagonalExtendedBulkMinimalPhysicalLocalGaugeFixedHessianOnCore period
        hPeriod configuration data analysis chart sameAction.chartBridge first
          second := by
  unfold globalCandidateAFaithfulAugmentedRieszResidualPairing
  unfold globalCandidateAFaithfulAugmentedRieszResidual
  calc
    _ = globalCandidateACommonAugmentedHessian period hPeriod configuration data
          analysis chart sameAction physical
          (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
            (globalCandidateAMetricBySector period hPeriod data)
            couplings.matterMassSquared data analysis first)
          (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
            (globalCandidateAMetricBySector period hPeriod data)
            couplings.matterMassSquared data analysis second) :=
      globalCandidateACommonAugmentedRieszOperator_pairing period hPeriod
        configuration data analysis chart sameAction physical _ _
    _ = _ :=
      globalCandidateACommonAugmentedHessian_smooth_eq_gaugeFixed period hPeriod
        configuration data analysis chart sameAction physical first second

end
end P0EFTJanusProgramPGlobalEulerLagrangeFaithfulAugmentedRieszResidual4D
end JanusFormal
