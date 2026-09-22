import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12JointQuotientPhysicalRiesz4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12JointQuotientAbelianSmoothPairing4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12AbelianLorenzShearPairing4D

/-! The geometric Abelian Lorenz shear preserves the full H11 column,
including its couplings to every other physical sector. -/
namespace JanusFormal
namespace P0EFTJanusProgramPT12AbelianLorenzShearPhysical4D
set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 1200000
noncomputable section

open Set MeasureTheory
open scoped ENNReal lp Manifold ContDiff InnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalCandidateABulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalCandidateAAbelianExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateAAbelianExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalCovariantHessianResidualBridge4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalMetricTangentIntrinsicEmbedding4D
open P0EFTJanusProgramPGlobalCandidateACanonicalStablePerturbation4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphProjections4D
open P0EFTJanusProgramPGlobalFullLLGraphRiesz4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartCenter4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLocalActionFamilyCenter4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC0FirstJetProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongComponentPDEBlockPairing4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLLWeakFirstVariation4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLocalEuler4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongSpinCTotalEuler4D
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalRieszTransport4D
open P0EFTJanusProgramPT12LLCanonicalH1ClosedDomain4D
open P0EFTJanusProgramPT12LLCanonicalH1L2Bridge4D
open P0EFTJanusProgramPT12StrongLLPhysicalMixedHessianZero4D
open P0EFTJanusProgramPT12StrongMatterLLSameActionBridge4D
open P0EFTJanusProgramPT12StrongPhysicalSecondJet4D
open P0EFTJanusProgramPT12StrongToH11PhysicalSecondJet4D
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2DiffeomorphismNormedAddCommGroup
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2DiffeomorphismInnerProductSpace
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2AbelianInnerProductSpace
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2MatterInnerProductSpace
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2MatterCompleteSpace
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2LLInnerProductSpace
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2LLCompleteSpace
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkNormedAddCommGroup
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkInnerProductSpace
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkCompleteSpace
  P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D.programPPrimitiveSpinCMatterHilbertRealInnerProductSpace

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance : IsManifold coverModelWithCorners ω
    (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance : BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

section

variable {couplings : GlobalCandidateAActionCouplings}
variable {NonNullFace NullFace : Type*}
variable [Fintype NonNullFace] [Fintype NullFace]
variable {measure : Measure (EffectiveQuotient period hPeriod)}
variable (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
variable (data : GlobalCandidateAActionData period hPeriod
  configuration.physical couplings NonNullFace NullFace)
variable (analysis : GlobalAnalysisData period hPeriod configuration.physical)

set_option backward.isDefEq.respectTransparency false
open P0EFTJanusProgramPT12StrongCompletedMatterLLPhysicalRieszZero4D
open P0EFTJanusProgramPT12LLQuotientFriedrichsRealization4D
open P0EFTJanusProgramPT12LLQuotientFriedrichsSmoothPairing4D
open P0EFTJanusProgramPT12LLFullJacobiHilbertQuotient4D

open P0EFTJanusProgramPT12StrongFullLLQuotientColumn4D
open P0EFTJanusProgramPGlobalLLAuxMeasureGraphRiesz4D
open P0EFTJanusProgramPT12LLFullJacobiZeroFluxKernel4D
open P0EFTJanusProgramPT12DiagonalGhostHilbertQuotient4D
open P0EFTJanusProgramPCandidateADiagonalDiffeomorphismKineticAdjointBridge4D

open P0EFTJanusProgramPT12StrongGhostLLNullSpace4D
open P0EFTJanusProgramPT12ClosedNullQuotient4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalLocalHessianBridge4D

open P0EFTJanusProgramPT12StrongGhostLLHilbertQuotient4D
open P0EFTJanusProgramPT12JointQuotientAbelianFactor4D
open P0EFTJanusProgramPT12SignedBRSTAugmentedPairing4D
open P0EFTJanusProgramPT12AbelianSignedBRSTRealization4D
open P0EFTJanusProgramPT12DiffeomorphismSignedBRSTRealization4D
variable [IsFiniteMeasure measure]
variable (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
  period hPeriod couplings.matterMassSquared)
variable (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
variable (hBase : RegularGeneralMetricC2PairedLorentzChartBaseCompatible
  period hPeriod plusBase minusBase)
variable (hCenter : RegularGeneralMetricC2PairedMinimalPhysicalCenterCompatible
  period hPeriod configuration.physical plusBase minusBase hBase)

variable (physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D
  period hPeriod configuration data analysis
  (strongChart (measure := measure) period hPeriod configuration data analysis realization plusBase minusBase hBase)
  (strongBridge (measure := measure) period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter))

open P0EFTJanusProgramPT12JointQuotientAbelianColumn4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalHilbertAugmentationObstruction4D

open P0EFTJanusProgramPT12JointQuotientAbelianSmoothPairing4D
open P0EFTJanusProgramPT12AbelianLorenzGraphShear4D
open P0EFTJanusProgramPT12AbelianBRSTNegativePhysicalColumn4D
open P0EFTJanusProgramPT12JointQuotientPhysicalRiesz4D

/-- The increment changes only the independent auxiliary field. -/
theorem abelianLorenzIncrement_physicalRiesz_zero
    (vector : ActualAbelianHilbert period hPeriod configuration data) :
    strongPhysicalRiesz (measure := measure) period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical
      (actualAbelianInclusion period hPeriod configuration data analysis
        (abelianLorenzGraphIncrement period hPeriod
          (globalCandidateAMetricBySector period hPeriod data) vector)) = 0 := by
  let riesz := strongPhysicalRiesz (measure := measure) period hPeriod configuration data analysis
    realization plusBase minusBase hBase hCenter physical
  let inclusion := actualAbelianInclusion period hPeriod configuration data analysis
  let increment := abelianLorenzGraphIncrement period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)
  have hAll : (fun value => riesz (inclusion (increment value))) =
      (fun _ : ActualAbelianHilbert period hPeriod configuration data =>
        (0 : CommonAugmentedHilbert period hPeriod configuration data analysis)) := by
    apply (globalPairedAbelianOffShellSmoothEmbedding_denseRange period hPeriod
      (globalCandidateAMetricBySector period hPeriod data)).equalizer
    · exact riesz.continuous.comp (inclusion.continuous.comp increment.continuous)
    · exact continuous_const
    · funext state
      change riesz (inclusion (abelianLorenzGraphIncrement period hPeriod
        (globalCandidateAMetricBySector period hPeriod data)
        (globalPairedAbelianOffShellSmoothEmbedding period hPeriod
          (globalCandidateAMetricBySector period hPeriod data) state))) = 0
      rw [abelianLorenzGraphIncrement_smooth]
      change riesz (actualAbelianInclusion period hPeriod configuration data analysis _) = 0
      rw [actualAbelianInclusion_smooth]
      apply physicalRiesz_core_zero_of_hessian_column_zero period hPeriod configuration data analysis
        (strongChart (measure := measure) period hPeriod configuration data analysis realization
          plusBase minusBase hBase)
        (strongBridge (measure := measure) period hPeriod configuration data analysis realization
          plusBase minusBase hBase hCenter) physical
      intro test
      unfold diagonalExtendedBulkMinimalPhysicalLocalActionHessianOnCore
      have hTangent := pureAbelianNakanishiLautrupCore_physicalTangent_zero period hPeriod
        configuration data analysis (fun sector =>
          (abelianLorenzSmoothIncrement period hPeriod
            (globalCandidateAMetricBySector period hPeriod data) state).nonminimal sector
            |>.nakanishiLautrup.field)
      change diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
        configuration data analysis
        (abelianCore period hPeriod configuration analysis
          (abelianLorenzSmoothIncrement period hPeriod
            (globalCandidateAMetricBySector period hPeriod data) state)) = 0 at hTangent
      rw [hTangent]
      simp
  exact congrFun hAll vector

/-- Full physical column equality, with arbitrary completed tests implicit. -/
theorem abelianLorenzShear_physicalRiesz
    (vector : ActualAbelianHilbert period hPeriod configuration data) :
    strongPhysicalRiesz (measure := measure) period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical
      (actualAbelianInclusion period hPeriod configuration data analysis
        (abelianLorenzGraphShear period hPeriod
          (globalCandidateAMetricBySector period hPeriod data) vector)) =
    strongPhysicalRiesz (measure := measure) period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical
      (actualAbelianInclusion period hPeriod configuration data analysis vector) := by
  rw [abelianLorenzGraphShear,
    P0EFTJanusProgramPT12NilpotentGraphShear4D.nilpotentShear_apply,
    map_add, map_add, abelianLorenzIncrement_physicalRiesz_zero, add_zero]

/-- The same H11 column is retained after the joint ghosts--LL quotient. -/
theorem quotientAbelianPhysicalColumn_lorenzShear
    (vector : ActualAbelianHilbert period hPeriod configuration data) :
    quotientAbelianPhysicalColumn period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical
      (abelianLorenzGraphShear period hPeriod
        (globalCandidateAMetricBySector period hPeriod data) vector) =
    quotientAbelianPhysicalColumn period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical vector :=
  congrArg (jointGhostLLNullSpace period hPeriod configuration data analysis).mkQ
    (abelianLorenzShear_physicalRiesz period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical vector)

end
end
end P0EFTJanusProgramPT12AbelianLorenzShearPhysical4D
end JanusFormal

