import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalRieszTransport4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12SpectralBRSTNonnegative4D

/-! The complete Friedrichs target remains nonnegative on the pure BRST sector. -/
namespace JanusFormal
namespace P0EFTJanusProgramPT12FullFriedrichsBRSTNonnegative4D

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 600000
noncomputable section

open Set MeasureTheory
open scoped ENNReal lp Manifold ContDiff InnerProductSpace LinearPMap
open P0EFTJanusCircleQuillenMetricFlatConnection
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusImmersionFiberAlgebra
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalFullLLGraphRiesz4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalPairedAbelianBRSTGaugeFermion4D
open P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateAAbelianExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalCandidateAFaithfulFredholmSum4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalLocalHessianBridge4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalCandidateACanonicalStablePerturbation4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorBismutFreedFamily4D
open P0EFTJanusProgramPGlobalGaugeFixedSpectralHessianFredholm4D
open P0EFTJanusProgramPGlobalGaugeFixedLLFriedrichsHessianFredholm4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsCommonDomainFamily4D
open P0EFTJanusProgramPT12LLCanonicalH1ClosedDomain4D
open P0EFTJanusProgramPT12LLCanonicalH1L2Bridge4D

attribute [local instance]
  programPGlobalGaugeFixedSpectralHessianHilbertRealInnerProductSpace
  programPPrimitiveSpinCMatterHilbertRealInnerProductSpace
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2DiffeomorphismNormedAddCommGroup
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2DiffeomorphismInnerProductSpace
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2AbelianInnerProductSpace
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2MatterInnerProductSpace
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2LLInnerProductSpace
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkNormedAddCommGroup
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkInnerProductSpace
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkCompleteSpace

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

local instance spectralMatterRestrictionModeDecidableEq
    (iota : Type*) [DecidableEq iota] :
    DecidableEq (ProgramPGlobalGaugeFixedSpectralHessianMode iota) :=
  Classical.decEq _

open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalRieszTransport4D
open P0EFTJanusProgramPT12SpectralBRSTNonnegative4D
open P0EFTJanusLinearPMapProdIdentityFredholm4D
set_option backward.isDefEq.respectTransparency false

/-- Vanishing of the installed readout means vanishing of both actual target tail components. -/
theorem friedrichsMatterLLReadout_eq_zero_iff
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    {iota : Type*} [DecidableEq iota]
    (state : ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert period hPeriod iota analysis) :
    programPT12GaugeFixedLLFriedrichsMatterLLReadout period hPeriod configuration analysis state = 0 ↔
      programPT12GaugeFixedSpectralMatterRestriction state.fst = 0 ∧ state.snd = 0 := by
  constructor
  · intro hZero
    exact ⟨congrArg WithLp.fst hZero, congrArg WithLp.snd hZero⟩
  · rintro ⟨hMatter, hLL⟩
    apply WithLp.ofLp_injective 2
    exact Prod.ext hMatter hLL
variable {couplings : GlobalCandidateAActionCouplings}
variable {NonNullFace NullFace : Type*}
variable [Fintype NonNullFace] [Fintype NullFace]
variable {measure : Measure (EffectiveQuotient period hPeriod)}
variable (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
variable (data : GlobalCandidateAActionData period hPeriod
  configuration.physical couplings NonNullFace NullFace)
variable (analysis : GlobalAnalysisData period hPeriod configuration.physical)
variable (chart : GlobalCandidateALocalVariationalChart period hPeriod
  couplings NonNullFace NullFace measure)
variable (sameAction : ProgramPGlobalMinimalPhysicalLocalMatterLLSameActionBridge4D
  period hPeriod configuration data analysis chart)
variable (physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D
  period hPeriod configuration data analysis chart sameAction)

/-- Every pure BRST target state has nonnegative pairing, including the full H11 perturbation. -/
theorem fullFriedrichs_pairing_nonneg_of_matterLLReadout_zero
    {iota : Type*} [DecidableEq iota] (covector : iota → TangentVector3) (parameter : Real)
    (state : ProgramPT12GaugeFixedLLFriedrichsD11CommonDomain period hPeriod covector couplings.matterMassSquared analysis)
    (hZero : programPT12GaugeFixedLLFriedrichsMatterLLReadout period hPeriod configuration analysis state.1 = 0) :
    0 ≤ inner Real
      (programPT12GaugeFixedLLFriedrichsFullPhysicalOperator
        (configuration := configuration) (data := data) (analysis := analysis) (chart := chart)
        (sameAction := sameAction) (physical := physical) period hPeriod covector parameter state) state.1 := by
  have hParts := (friedrichsMatterLLReadout_eq_zero_iff period hPeriod configuration analysis state.1).mp hZero
  have hTransport : programPT12GaugeFixedLLFriedrichsToActualTransport
      (configuration := configuration) (data := data) (analysis := analysis) period hPeriod state.1 = 0 := by
    change programPT12FriedrichsMatterLLToActualTransport
      (configuration := configuration) (data := data) (analysis := analysis) period hPeriod
      (programPT12GaugeFixedLLFriedrichsMatterLLReadout period hPeriod configuration analysis state.1) = 0
    rw [hZero, map_zero]
  have hResidual : programPT12GaugeFixedLLFriedrichsPhysicalResidualForm
      (configuration := configuration) (data := data) (analysis := analysis) (chart := chart)
      (sameAction := sameAction) (physical := physical) period hPeriod state.1 state.1 = 0 := by
    change physical.form
      (programPT12GaugeFixedLLFriedrichsToActualTransport
        (configuration := configuration) (data := data) (analysis := analysis) period hPeriod state.1)
      (programPT12GaugeFixedLLFriedrichsToActualTransport
        (configuration := configuration) (data := data) (analysis := analysis) period hPeriod state.1) = 0
    rw [hTransport]
    simp
  rw [programPT12GaugeFixedLLFriedrichsFullPhysicalOperator_pairing, hResidual, add_zero]
  change 0 ≤ inner Real (linearPMapProd
    (programPGlobalGaugeFixedSpectralHessianRealMaximalOperator period hPeriod covector couplings.matterMassSquared)
    (programPT12GaugeFixedLLFriedrichsD11LLOperator period hPeriod analysis parameter) state) state.1
  rw [linearPMapProd_apply, WithLp.prod_inner_apply]
  change 0 ≤ inner Real
    (programPGlobalGaugeFixedSpectralHessianRealMaximalOperator period hPeriod covector couplings.matterMassSquared
      ⟨state.1.fst, state.2.1⟩) state.1.fst +
    inner Real (programPT12GaugeFixedLLFriedrichsD11LLOperator period hPeriod analysis parameter
      ⟨state.1.snd, state.2.2⟩) state.1.snd
  have hLLPair : inner Real
      (programPT12GaugeFixedLLFriedrichsD11LLOperator period hPeriod analysis parameter
        ⟨state.1.snd, state.2.2⟩) state.1.snd = 0 :=
    (congrArg (inner Real (programPT12GaugeFixedLLFriedrichsD11LLOperator period hPeriod analysis parameter
      ⟨state.1.snd, state.2.2⟩)) hParts.2).trans (inner_zero_right _)
  rw [hLLPair, add_zero]
  apply spectralBRST_pairing_nonneg
  intro mode
  exact congrArg (fun field : ProgramPPrimitiveSpinCMatterHilbert => field mode) hParts.1

end
end P0EFTJanusProgramPT12FullFriedrichsBRSTNonnegative4D
end JanusFormal
