import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiffeomorphismH11QuotientAdjoint4D

/-! Dense physical H11 core in the joint quotient, with its full output norm preserved. -/
namespace JanusFormal
namespace P0EFTJanusProgramPT12DiffeomorphismH11QuotientCore4D
set_option autoImplicit false

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 600000
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

open P0EFTJanusProgramPT12CandidateAAbelianMixedOperator4D
open P0EFTJanusProgramPT12CandidateAAbelianMixedPotential4D
open P0EFTJanusProgramPT12AbelianPotentialGraphInclusion4D
open P0EFTJanusProgramPT12AbelianGhostRotationPhysical4D

open P0EFTJanusProgramPT12JointQuotientDiffeomorphismFactor4D
open P0EFTJanusProgramPT12JointQuotientDiffeomorphismSmoothPairing4D
open P0EFTJanusProgramPT12DiffeomorphismMetricSmooth4D

open P0EFTJanusProgramPT12DiffeomorphismH11MetricDependence4D

open P0EFTJanusProgramPT12DiffeomorphismH11Smooth4D
open P0EFTJanusProgramPT12DiffeomorphismL2Core4D
open P0EFTJanusProgramPT12InjectiveSmoothColumn4D

local instance physicalSourceInnerProductSpace : InnerProductSpace Real (DiffeomorphismL2 period hPeriod (globalCandidateAMetricBySector period hPeriod data .plus)) :=
  Submodule.innerProductSpace (𝕜 := Real) (E := DiffeomorphismL2Ambient period hPeriod)
    (diffeomorphismL2Space period hPeriod (globalCandidateAMetricBySector period hPeriod data .plus))

open P0EFTJanusProgramPT12DiffeomorphismH11Core4D

attribute [local irreducible] diffeomorphismH11Smooth diffeomorphismH11Core

open P0EFTJanusProgramPT12DiffeomorphismH11Adjoint4D
open P0EFTJanusProgramPT12DiffeomorphismMetricProjection4D

open P0EFTJanusProgramPT12DiffeomorphismH11AdjointMetric4D

local instance physicalMetricInnerProductSpace : InnerProductSpace Real (DiffeomorphismMetricL2 period hPeriod (globalCandidateAMetricBySector period hPeriod data .plus)) :=
  Submodule.innerProductSpace (𝕜 := Real)
    (E := DiffeomorphismL2 period hPeriod (globalCandidateAMetricBySector period hPeriod data .plus)) (diffeomorphismMetricProjection period hPeriod (globalCandidateAMetricBySector period hPeriod data .plus)).range

open P0EFTJanusProgramPT12DiffeomorphismGraphToL24D
open P0EFTJanusProgramPT12DiffeomorphismH11MetricBound4D
open P0EFTJanusProgramPGlobalDiffeomorphismBRSTOffShellGraphC2Chart4D
attribute [local instance]
  globalDiffeomorphismOffShellGraphNormedSpace globalDiffeomorphismOffShellGraphModule
  globalDiffeomorphismOffShellGraphInnerProductSpace globalDiffeomorphismOffShellGraphCompleteSpace
  diagonalGraphNormedSpace diagonalGraphModule diagonalGraphInnerProductSpace diagonalGraphCompleteSpace
attribute [local irreducible] diffeomorphismGraphToL2

open P0EFTJanusProgramPT12DiffeomorphismH11GraphBridge4D
open P0EFTJanusProgramPT12StrongGhostLLNullSpace4D
open P0EFTJanusProgramPT12StrongGhostLLHilbertQuotient4D
open P0EFTJanusProgramPT12ClosedRangeEquation4D

open P0EFTJanusProgramPT12DiffeomorphismH11QuotientAdjoint4D
open P0EFTJanusProgramPT12ClosedNullQuotient4D

/-- All physical outputs, reduced only by the common null space. -/
def diffeomorphismH11QuotientSmooth : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod →ₗ[Real] JointGhostLLQuotient period hPeriod configuration data analysis :=
  (jointGhostLLNullSpace period hPeriod configuration data analysis).mkQ.comp (diffeomorphismH11Smooth period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical)

theorem diffeomorphismH11QuotientSmooth_physical (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    diffeomorphismH11QuotientSmooth period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical field = quotientPhysicalRiesz period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical
      ((jointGhostLLNullSpace period hPeriod configuration data analysis).mkQ (diffeomorphismPhysicalSmoothLift period hPeriod configuration data analysis field)) := by
  unfold diffeomorphismH11QuotientSmooth diffeomorphismH11Smooth
  rfl

theorem diffeomorphismH11QuotientSmooth_pairing (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) (test : CommonAugmentedHilbert period hPeriod configuration data analysis) :
    inner Real (diffeomorphismH11QuotientSmooth period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical field) ((jointGhostLLNullSpace period hPeriod configuration data analysis).mkQ test) =
      inner Real (diffeomorphismH11Smooth period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical field) test := by
  rw [diffeomorphismH11QuotientSmooth_physical, quotientPhysicalRiesz_pairing,
    diffeomorphismH11Smooth_pairing]

theorem diffeomorphismH11Smooth_jointNull_orthogonal (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    diffeomorphismH11Smooth period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical field ∈ (jointGhostLLNullSpace period hPeriod configuration data analysis)ᗮ := by
  unfold diffeomorphismH11Smooth
  exact operator_mem_null_orthogonal (strongPhysicalRiesz (measure := measure) period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical)
    (strongPhysicalRiesz_isSelfAdjoint period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical) (jointGhostLLNullSpace period hPeriod configuration data analysis)
    (jointNull_le_physicalRiesz_kernel period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical) _

theorem diffeomorphismH11QuotientSmooth_norm (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    ‖diffeomorphismH11QuotientSmooth period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical field‖ = ‖diffeomorphismH11Smooth period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical field‖ := by
  have h := inner_mk_of_left_orthogonal (jointGhostLLNullSpace period hPeriod configuration data analysis)
    (diffeomorphismH11Smooth period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical field) (diffeomorphismH11Smooth period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical field)
    (diffeomorphismH11Smooth_jointNull_orthogonal period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical field)
  change inner Real (diffeomorphismH11QuotientSmooth period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical field) (diffeomorphismH11QuotientSmooth period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical field) = _ at h
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

def diffeomorphismH11QuotientCore : DiffeomorphismL2 period hPeriod (globalCandidateAMetricBySector period hPeriod data .plus) →ₗ.[Real] JointGhostLLQuotient period hPeriod configuration data analysis :=
  injectiveSmoothColumn (D := GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) (E := DiffeomorphismL2 period hPeriod (globalCandidateAMetricBySector period hPeriod data .plus)) (F := JointGhostLLQuotient period hPeriod configuration data analysis)
    (diffeomorphismL2Smooth period hPeriod (globalCandidateAMetricBySector period hPeriod data .plus)) (diffeomorphismH11QuotientSmooth period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical) (diffeomorphismL2Smooth_injective period hPeriod (globalCandidateAMetricBySector period hPeriod data .plus))

def diffeomorphismH11QuotientSmoothDomain (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    (diffeomorphismH11QuotientCore period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical).domain := ⟨diffeomorphismL2Smooth period hPeriod (globalCandidateAMetricBySector period hPeriod data .plus) field, ⟨field, rfl⟩⟩

theorem diffeomorphismH11QuotientCore_smooth (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    diffeomorphismH11QuotientCore period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical (diffeomorphismH11QuotientSmoothDomain period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical field) =
      diffeomorphismH11QuotientSmooth period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical field :=
  injectiveSmoothColumn_smooth (D := GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) (E := DiffeomorphismL2 period hPeriod (globalCandidateAMetricBySector period hPeriod data .plus)) (F := JointGhostLLQuotient period hPeriod configuration data analysis)
    (diffeomorphismL2Smooth period hPeriod (globalCandidateAMetricBySector period hPeriod data .plus)) (diffeomorphismH11QuotientSmooth period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical) (diffeomorphismL2Smooth_injective period hPeriod (globalCandidateAMetricBySector period hPeriod data .plus)) field

theorem diffeomorphismH11QuotientCore_denseDomain :
    Dense ((diffeomorphismH11QuotientCore period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical).domain : Set (DiffeomorphismL2 period hPeriod (globalCandidateAMetricBySector period hPeriod data .plus))) :=
  injectiveSmoothColumn_denseDomain (D := GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) (E := DiffeomorphismL2 period hPeriod (globalCandidateAMetricBySector period hPeriod data .plus)) (F := JointGhostLLQuotient period hPeriod configuration data analysis)
    (diffeomorphismL2Smooth period hPeriod (globalCandidateAMetricBySector period hPeriod data .plus)) (diffeomorphismH11QuotientSmooth period hPeriod configuration data analysis realization plusBase minusBase hBase hCenter physical) (diffeomorphismL2Smooth_injective period hPeriod (globalCandidateAMetricBySector period hPeriod data .plus))
    (diffeomorphismL2Smooth_denseRange period hPeriod (globalCandidateAMetricBySector period hPeriod data .plus))

end
end
end P0EFTJanusProgramPT12DiffeomorphismH11QuotientCore4D
end JanusFormal
