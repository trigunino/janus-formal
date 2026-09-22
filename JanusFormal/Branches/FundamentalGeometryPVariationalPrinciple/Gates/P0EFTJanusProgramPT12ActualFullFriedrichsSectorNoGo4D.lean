import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FullFriedrichsBRSTNonnegative4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12AbelianBRSTNegativePhysicalColumn4D

/-! Global obstruction to the installed sector-preserving Friedrichs zero-fibre realization. -/
namespace JanusFormal
namespace P0EFTJanusProgramPT12ActualFullFriedrichsSectorNoGo4D

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

open P0EFTJanusProgramPT12FullFriedrichsBRSTNonnegative4D
open P0EFTJanusProgramPT12AbelianBRSTNegativePhysicalColumn4D
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusPhysicalGaugeSobolevComplex4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D

/-- A concrete nonzero smooth paired field for the global negative witness. -/
theorem exists_nonzero_pairedGaugeField :
    ∃ field : GlobalPairedGaugeLieSmooth period hPeriod, field ≠ 0 := by
  let field : GlobalPairedGaugeLieSmooth period hPeriod := fun _ =>
    ⟨fun _ => (EuclideanSpace.equiv (Fin 2) Real).symm (fun _ => 1), contMDiff_const⟩
  refine ⟨field, ?_⟩
  intro hZero
  let sphere : UnitThreeSphere :=
    ⟨![0, 1, 0, 0], by
      norm_num [P0EFTJanusReflectionFixedThroat.OnUnitThreeSphere,
        P0EFTJanusReflectionFixedThroat.radiusSquared, Fin.sum_univ_succ]⟩
  let point := mappingTorusMk (reflectedSphereData period hPeriod) ⟨sphere, 0⟩
  have hValue := congrArg (fun f : GlobalPairedGaugeLieSmooth period hPeriod =>
    (EuclideanSpace.equiv (Fin 2) Real) (f .plus point) 0) hZero
  change (1 : Real) = 0 at hValue
  exact one_ne_zero hValue
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

private abbrev actualEmbedding :=
  diagonalExtendedBulkL2SmoothEmbedding period hPeriod
    (globalCandidateAMetricBySector period hPeriod data) couplings.matterMassSquared data analysis

private abbrev actualOperator :=
  globalCandidateACommonAugmentedRieszOperator period hPeriod configuration data analysis chart sameAction physical

private def actualCorePairing
    (core : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod analysis) : Real :=
  @inner Real (CommonAugmentedHilbert period hPeriod configuration data analysis)
    (commonAugmentedInnerProductSpace period hPeriod configuration data analysis).toInner
    (actualOperator period hPeriod configuration data analysis chart sameAction physical
    (actualEmbedding period hPeriod configuration data analysis core))
    (actualEmbedding period hPeriod configuration data analysis core)

private abbrev targetOperator {iota : Type*} [DecidableEq iota] (covector : iota → TangentVector3) :=
  programPT12GaugeFixedLLFriedrichsFullPhysicalOperator
    (configuration := configuration) (data := data) (analysis := analysis) (chart := chart)
    (sameAction := sameAction) (physical := physical) period hPeriod covector 0

/-- The negative direction survives in the complete actual operator with all physical columns. -/
theorem actual_augmented_pureB_pairing_neg
    (field : GlobalPairedGaugeLieSmooth period hPeriod) (hField : field ≠ 0) :
    actualCorePairing period hPeriod configuration data analysis chart sameAction physical
      (pureAbelianNakanishiLautrupCore period hPeriod configuration analysis field) < 0 := by
  unfold actualCorePairing
  rw [pureAbelianNakanishiLautrupCore_augmented_pairing_self]
  have hValue : globalPairedGaugeLieL2LinearMap period hPeriod field ≠ 0 := by
    intro hZero
    apply hField
    apply globalPairedGaugeLieL2LinearMap_injective period hPeriod
    simpa only [map_zero] using hZero
  exact neg_neg_of_pos (sq_pos_of_pos ((norm_pos_iff).2 hValue))

/-- No global pairing realization can keep pure nonminimal fields out of the matter--LL tail.
No linearity, injectivity, isometry or ghost domain assumption is needed. -/
theorem no_actual_to_fullFriedrichs_sector_pairing
    {iota : Type*} [DecidableEq iota] (covector : iota → TangentVector3) :
    ¬ ∃ realize : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod analysis →
        (targetOperator period hPeriod configuration data analysis chart sameAction physical covector).domain,
      (∀ field : GlobalPairedGaugeLieSmooth period hPeriod,
        programPT12GaugeFixedLLFriedrichsMatterLLReadout period hPeriod configuration analysis
          (realize (pureAbelianNakanishiLautrupCore period hPeriod configuration analysis field)).val = 0) ∧
      (∀ core : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod analysis,
        inner Real (targetOperator period hPeriod configuration data analysis chart sameAction physical covector (realize core))
          (realize core).val =
        actualCorePairing period hPeriod configuration data analysis chart sameAction physical core) := by
  rintro ⟨realize, hReadout, hPairing⟩
  obtain ⟨field, hField⟩ := exists_nonzero_pairedGaugeField period hPeriod
  let core := pureAbelianNakanishiLautrupCore period hPeriod configuration analysis field
  have hNonnegative := fullFriedrichs_pairing_nonneg_of_matterLLReadout_zero period hPeriod
    configuration data analysis chart sameAction physical covector 0 (realize core) (hReadout field)
  rw [hPairing core] at hNonnegative
  have hNegative := actual_augmented_pureB_pairing_neg period hPeriod configuration data analysis
    chart sameAction physical field hField
  exact (not_le_of_gt hNegative) hNonnegative

end
end P0EFTJanusProgramPT12ActualFullFriedrichsSectorNoGo4D
end JanusFormal
