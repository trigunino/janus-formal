import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12AbelianLorenzShearPhysical4D

/-! The actual Abelian Lorenz shear on the whole joint quotient, preserving H11. -/
namespace JanusFormal
namespace P0EFTJanusProgramPT12JointQuotientLorenzShear4D
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

open P0EFTJanusProgramPT12AbelianLorenzShearPhysical4D
open P0EFTJanusProgramPT12NilpotentGraphShear4D

/-- Only the Abelian component receives the geometric auxiliary increment. -/
def jointLorenzIncrement :
    JointGhostLLQuotient period hPeriod configuration data analysis →L[Real]
      JointGhostLLQuotient period hPeriod configuration data analysis :=
  (quotientAbelianInclusion period hPeriod configuration data analysis).toContinuousLinearMap.comp
    ((abelianLorenzGraphIncrement period hPeriod
      (globalCandidateAMetricBySector period hPeriod data)).comp
      (quotientAbelianReadout period hPeriod configuration data analysis))

theorem jointLorenzIncrement_square_zero
    (vector : JointGhostLLQuotient period hPeriod configuration data analysis) :
    jointLorenzIncrement period hPeriod configuration data analysis
      (jointLorenzIncrement period hPeriod configuration data analysis vector) = 0 := by
  change quotientAbelianInclusion period hPeriod configuration data analysis
    (abelianLorenzGraphIncrement period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      (quotientAbelianReadout period hPeriod configuration data analysis
        (quotientAbelianInclusion period hPeriod configuration data analysis
          (abelianLorenzGraphIncrement period hPeriod
            (globalCandidateAMetricBySector period hPeriod data)
            (quotientAbelianReadout period hPeriod configuration data analysis vector))))) = 0
  rw [quotientAbelianReadout_inclusion, abelianLorenzGraphIncrement_square_zero, map_zero]

def jointLorenzShear : JointGhostLLQuotient period hPeriod configuration data analysis ≃L[Real]
    JointGhostLLQuotient period hPeriod configuration data analysis :=
  nilpotentShear (jointLorenzIncrement period hPeriod configuration data analysis)
    (jointLorenzIncrement_square_zero period hPeriod configuration data analysis)

theorem jointLorenzShear_abelianInclusion
    (vector : ActualAbelianHilbert period hPeriod configuration data) :
    jointLorenzShear period hPeriod configuration data analysis
      (quotientAbelianInclusion period hPeriod configuration data analysis vector) =
    quotientAbelianInclusion period hPeriod configuration data analysis
      (abelianLorenzGraphShear period hPeriod
        (globalCandidateAMetricBySector period hPeriod data) vector) := by
  rw [jointLorenzShear, nilpotentShear_apply, abelianLorenzGraphShear,
    nilpotentShear_apply, map_add]
  rfl

theorem jointLorenzIncrement_physicalRiesz_zero
    (vector : JointGhostLLQuotient period hPeriod configuration data analysis) :
    quotientPhysicalRiesz period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical
      (jointLorenzIncrement period hPeriod configuration data analysis vector) = 0 := by
  have h := congrArg (jointGhostLLNullSpace period hPeriod configuration data analysis).mkQ
    (abelianLorenzIncrement_physicalRiesz_zero period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical
      (quotientAbelianReadout period hPeriod configuration data analysis vector))
  exact h.trans ((jointGhostLLNullSpace period hPeriod configuration data analysis).mkQ.map_zero)

theorem jointLorenzShear_physicalRiesz
    (vector : JointGhostLLQuotient period hPeriod configuration data analysis) :
    quotientPhysicalRiesz period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical
      (jointLorenzShear period hPeriod configuration data analysis vector) =
    quotientPhysicalRiesz period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical vector := by
  rw [jointLorenzShear, nilpotentShear_apply, map_add,
    jointLorenzIncrement_physicalRiesz_zero, add_zero]

private theorem selfAdjoint_pairing_preserved
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]
    (operator : E →L[Real] E) (hSelf : IsSelfAdjoint operator)
    (shear : E → E) (hPreserved : ∀ x, operator (shear x) = operator x) (x y : E) :
    inner Real (operator (shear x)) (shear y) = inner Real (operator x) y :=
  (congrArg (fun z => inner Real z (shear y)) (hPreserved x)).trans
    ((hSelf.isSymmetric x (shear y)).trans
      ((congrArg (inner Real x) (hPreserved y)).trans (hSelf.isSymmetric x y).symm))

/-- All physical pairings, including cross-sector H11 terms, are unchanged. -/
theorem jointLorenzShear_physical_pairing
    (first second : JointGhostLLQuotient period hPeriod configuration data analysis) :
    inner Real
      (quotientPhysicalRiesz period hPeriod configuration data analysis realization
        plusBase minusBase hBase hCenter physical
        (jointLorenzShear period hPeriod configuration data analysis first))
      (jointLorenzShear period hPeriod configuration data analysis second) =
    inner Real
      (quotientPhysicalRiesz period hPeriod configuration data analysis realization
        plusBase minusBase hBase hCenter physical first) second :=
  selfAdjoint_pairing_preserved _
    (quotientPhysicalRiesz_isSelfAdjoint period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical) _
    (jointLorenzShear_physicalRiesz period hPeriod configuration data analysis realization
      plusBase minusBase hBase hCenter physical) first second

open P0EFTJanusProgramPT12AbelianLorenzShearPairing4D

/-- Actual reduced augmented pairing after the shear. The negative auxiliary
L2 block is separated and the original full H11 contribution is retained. -/
theorem jointLorenzShear_abelian_augmented_pairing
    (hZero : (data.boundary.llFields period hPeriod).llField = 0)
    (hMetric : globalCandidateAMetricBySector period hPeriod data .plus =
      globalCandidateAMetricBySector period hPeriod data .minus)
    (hWeights : candidateAPlusEinsteinKineticWeight couplings +
      candidateAMinusEinsteinKineticWeight couplings = 0)
    (first second : ActualAbelianHilbert period hPeriod configuration data) :
    inner Real
      (jointGhostLLRiesz period hPeriod configuration data analysis realization
        plusBase minusBase hBase hCenter physical hZero hMetric hWeights
        (jointLorenzShear period hPeriod configuration data analysis
          (quotientAbelianInclusion period hPeriod configuration data analysis first)))
      (jointLorenzShear period hPeriod configuration data analysis
        (quotientAbelianInclusion period hPeriod configuration data analysis second)) =
      inner Real (globalPairedAbelianOffShellLorenzProjection period hPeriod
        (globalCandidateAMetricBySector period hPeriod data) first)
        (globalPairedAbelianOffShellLorenzProjection period hPeriod
          (globalCandidateAMetricBySector period hPeriod data) second) -
      inner Real (globalPairedAbelianOffShellBProjection period hPeriod
        (globalCandidateAMetricBySector period hPeriod data) first)
        (globalPairedAbelianOffShellBProjection period hPeriod
          (globalCandidateAMetricBySector period hPeriod data) second) +
      inner Real (globalPairedAbelianOffShellAntighostProjection period hPeriod
        (globalCandidateAMetricBySector period hPeriod data) first)
        (globalPairedAbelianOffShellFPProjection period hPeriod
          (globalCandidateAMetricBySector period hPeriod data) second) +
      inner Real (globalPairedAbelianOffShellFPProjection period hPeriod
        (globalCandidateAMetricBySector period hPeriod data) first)
        (globalPairedAbelianOffShellAntighostProjection period hPeriod
          (globalCandidateAMetricBySector period hPeriod data) second) +
      inner Real (quotientPhysicalRiesz period hPeriod configuration data analysis realization
        plusBase minusBase hBase hCenter physical
        (quotientAbelianInclusion period hPeriod configuration data analysis first))
        (quotientAbelianInclusion period hPeriod configuration data analysis second) := by
  have hPhysical := jointLorenzShear_physical_pairing period hPeriod configuration data analysis
    realization plusBase minusBase hBase hCenter physical
    (quotientAbelianInclusion period hPeriod configuration data analysis first)
    (quotientAbelianInclusion period hPeriod configuration data analysis second)
  rw [jointLorenzShear_abelianInclusion, jointLorenzShear_abelianInclusion] at hPhysical ⊢
  rw [quotientAbelian_augmented_pairing, quotientAbelianReadout_inclusion,
    pairedAbelianSignedRiesz_pairing, abelianLorenzShear_hessian_pairing]
  exact congrArg (fun value => _ + value) hPhysical
end
end
end P0EFTJanusProgramPT12JointQuotientLorenzShear4D
end JanusFormal
