import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12AbelianGhostRotationPhysical4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12AbelianGhostIntrinsicDefect4D

/-! A concrete dense signed smooth Abelian core, with the exact full H11 column.
The FP skew defect remains; no maximal L2-domain identification is assumed. -/
namespace JanusFormal
namespace P0EFTJanusProgramPT12AbelianSignedSmoothCore4D
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

open P0EFTJanusProgramPT12AbelianGhostSmoothRotation4D
open P0EFTJanusProgramPGlobalPairedAbelianBRSTGaugeFermion4D
open P0EFTJanusProgramPGlobalGaugeTangentIntrinsicEmbedding4D

open P0EFTJanusProgramPT12AbelianGhostRotationPhysical4D
open P0EFTJanusProgramPT12AbelianLorenzShearPhysical4D
open P0EFTJanusProgramPT12AbelianLorenzShearPairing4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusProgramPT12GhostRotationDefect4D
open P0EFTJanusProgramPGlobalAbelianLorenzGraphRiesz4D

/-- Inverse ghost rotation followed by the genuine geometric Lorenz shear. -/
def abelianSignedSmoothCore
    (metric : P0EFTJanusD9D10ExactFieldContentBridge4D.Sector → SmoothGeneralLorentzMetric period hPeriod) :
    GlobalPairedAbelianBRSTState period hPeriod →ₗ[Real]
      GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric :=
  (abelianLorenzGraphShear period hPeriod metric).toLinearEquiv.toLinearMap.comp
    ((globalPairedAbelianOffShellSmoothEmbedding period hPeriod metric).comp
      (abelianGhostSignedEquiv period hPeriod).symm.toLinearMap)

theorem abelianSignedSmoothCore_denseRange
    (metric : P0EFTJanusD9D10ExactFieldContentBridge4D.Sector → SmoothGeneralLorentzMetric period hPeriod) :
    DenseRange (abelianSignedSmoothCore period hPeriod metric) := by
  let embedding := globalPairedAbelianOffShellSmoothEmbedding period hPeriod metric
  let rotation := (abelianGhostSignedEquiv period hPeriod).symm
  have hRange : Set.range (fun state => embedding (rotation state)) = Set.range embedding := by
    ext vector
    constructor
    · rintro ⟨state, rfl⟩
      exact ⟨rotation state, rfl⟩
    · rintro ⟨state, rfl⟩
      obtain ⟨input, rfl⟩ := rotation.surjective state
      exact ⟨input, rfl⟩
  have hRotated : DenseRange (fun state => embedding (rotation state)) := by
    change Dense (Set.range (fun state => embedding (rotation state)))
    rw [hRange]
    exact globalPairedAbelianOffShellSmoothEmbedding_denseRange period hPeriod metric
  exact (abelianLorenzGraphShear period hPeriod metric).surjective.denseRange.comp
    hRotated (abelianLorenzGraphShear period hPeriod metric).continuous

/-- Every transformed core vector still comes from an authentic smooth state. -/
theorem abelianSignedSmoothCore_smooth
    (metric : P0EFTJanusD9D10ExactFieldContentBridge4D.Sector → SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalPairedAbelianBRSTState period hPeriod) :
    abelianSignedSmoothCore period hPeriod metric state =
      globalPairedAbelianOffShellSmoothEmbedding period hPeriod metric
        (abelianGhostSignedReconstruct period hPeriod state +
          abelianLorenzSmoothIncrement period hPeriod metric
            (abelianGhostSignedReconstruct period hPeriod state)) :=
  abelianLorenzGraphShear_smooth period hPeriod metric _

/-- The separated auxiliary term and the actual ghost pairing on the new core.
The latter expands into signed diagonal terms plus the explicit FP defect. -/
theorem abelianSignedSmoothCore_hessian_pairing
    (metric : P0EFTJanusD9D10ExactFieldContentBridge4D.Sector → SmoothGeneralLorentzMetric period hPeriod)
    (first second : GlobalPairedAbelianBRSTState period hPeriod) :
    globalPairedAbelianOffShellHessian period hPeriod metric
      (abelianSignedSmoothCore period hPeriod metric first)
      (abelianSignedSmoothCore period hPeriod metric second) =
    inner Real (globalPairedAbelianLorenzL2LinearMap period hPeriod metric first.potential)
      (globalPairedAbelianLorenzL2LinearMap period hPeriod metric second.potential) -
    inner Real (globalPairedGaugeLieL2LinearMap period hPeriod
      (fun sector => (first.nonminimal sector).nakanishiLautrup.field))
      (globalPairedGaugeLieL2LinearMap period hPeriod
        (fun sector => (second.nonminimal sector).nakanishiLautrup.field)) +
    abelianGhostPairing period hPeriod metric
      (abelianGhostSignedReconstruct period hPeriod first)
      (abelianGhostSignedReconstruct period hPeriod second) := by
  change globalPairedAbelianOffShellHessian period hPeriod metric
    (abelianLorenzGraphShear period hPeriod metric
      (globalPairedAbelianOffShellSmoothEmbedding period hPeriod metric
        (abelianGhostSignedReconstruct period hPeriod first)))
    (abelianLorenzGraphShear period hPeriod metric
      (globalPairedAbelianOffShellSmoothEmbedding period hPeriod metric
        (abelianGhostSignedReconstruct period hPeriod second))) = _
  rw [abelianLorenzShear_hessian_pairing]
  simp only [globalPairedAbelianOffShellLorenzProjection_smooth,
    globalPairedAbelianOffShellBProjection_smooth,
    globalPairedAbelianOffShellAntighostProjection_smooth,
    globalPairedAbelianOffShellFPProjection_smooth]
  dsimp only [abelianGhostSignedReconstruct, abelianGhostPairing, ghostCrossPairing,
    abelianGhost, abelianAntighost]
  ring

theorem abelianSignedSmoothCore_physicalRiesz
    (state : GlobalPairedAbelianBRSTState period hPeriod) :
    strongPhysicalRiesz (measure := measure) period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical
      (actualAbelianInclusion period hPeriod configuration data analysis
        (abelianSignedSmoothCore period hPeriod
          (globalCandidateAMetricBySector period hPeriod data) state)) =
    strongPhysicalRiesz (measure := measure) period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical
      (actualAbelianInclusion period hPeriod configuration data analysis
        (globalPairedAbelianOffShellSmoothEmbedding period hPeriod
          (globalCandidateAMetricBySector period hPeriod data) state)) :=
  (abelianLorenzShear_physicalRiesz period hPeriod configuration data analysis realization
    plusBase minusBase hBase hCenter physical
    (globalPairedAbelianOffShellSmoothEmbedding period hPeriod
      (globalCandidateAMetricBySector period hPeriod data)
      (abelianGhostSignedReconstruct period hPeriod state))).trans
    (abelianGhostRotation_physicalRiesz period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical state)

theorem quotientAbelianPhysicalColumn_signedSmoothCore
    (state : GlobalPairedAbelianBRSTState period hPeriod) :
    quotientAbelianPhysicalColumn period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical
      (abelianSignedSmoothCore period hPeriod
        (globalCandidateAMetricBySector period hPeriod data) state) =
    quotientAbelianPhysicalColumn period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical
      (globalPairedAbelianOffShellSmoothEmbedding period hPeriod
        (globalCandidateAMetricBySector period hPeriod data) state) :=
  congrArg (jointGhostLLNullSpace period hPeriod configuration data analysis).mkQ
    (abelianSignedSmoothCore_physicalRiesz period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical state)

/-- Exact global reduced column, retaining the untransformed physical H11 column. -/
theorem quotientAbelian_signedSmoothCore_augmented_column
    (hZero : (data.boundary.llFields period hPeriod).llField = 0)
    (hMetric : globalCandidateAMetricBySector period hPeriod data .plus =
      globalCandidateAMetricBySector period hPeriod data .minus)
    (hWeights : candidateAPlusEinsteinKineticWeight couplings +
      candidateAMinusEinsteinKineticWeight couplings = 0)
    (state : GlobalPairedAbelianBRSTState period hPeriod) :
    jointGhostLLRiesz period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical hZero hMetric hWeights
      (quotientAbelianInclusion period hPeriod configuration data analysis
        (abelianSignedSmoothCore period hPeriod
          (globalCandidateAMetricBySector period hPeriod data) state)) =
    quotientAbelianInclusion period hPeriod configuration data analysis
      (pairedAbelianSignedRiesz period hPeriod (globalCandidateAMetricBySector period hPeriod data)
        (abelianSignedSmoothCore period hPeriod
          (globalCandidateAMetricBySector period hPeriod data) state)) +
    quotientAbelianPhysicalColumn period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical
      (globalPairedAbelianOffShellSmoothEmbedding period hPeriod
        (globalCandidateAMetricBySector period hPeriod data) state) := by
  rw [quotientAbelian_augmented_column, quotientAbelianPhysicalColumn_signedSmoothCore]

end
end
end P0EFTJanusProgramPT12AbelianSignedSmoothCore4D
end JanusFormal
