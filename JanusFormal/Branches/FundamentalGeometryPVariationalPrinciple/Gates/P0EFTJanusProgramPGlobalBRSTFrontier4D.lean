import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalNoether4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalDiffeomorphismFlowNoether4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCompleteVariationGeneralMetricBVBRSTBoundary4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusD8NonabelianGhostThroatBRST4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusExteriorDiffeomorphismGhostBRST4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusExteriorScalarBRSTDerivation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusLinearizedDiffeomorphismBRST4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusOrdinaryGhostNonlinearBRSTNoGo4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPNonlinearGlobalBRST4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGlobalMatterArbitraryDiffeomorphismNoether4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalTimeTranslationMetricMatterGaugeNoether4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusMeasuredDensityBRST4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusThroatScalarCoadjointBRST4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPCandidateABRSTInvarianceReduction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPThroatMetricGeometricAntifieldDual4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPTensorialCoadjointAntifieldBRST4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGeneralMetricGeometricAntifieldDual4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGeneralMetricPositiveDualizer4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGeneralMetricTimeTranslationSkew4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGeneralMetricTimeTranslationPairingNaturality4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPThroatMetricDiagonalDefinitenessNoGo4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPThroatMetricPositiveDualizer4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPThroatMetricGeneratingFrameSeparation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteFrameMetricDualizerAlgebra4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPThroatMetricFrameEnergySmooth4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPThroatMetricFrameCovectorSmooth4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPThroatMetricRestrictedGhostSkew4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD8RotationGhostThroatRestriction4D

/-!
# Exact frontier of the global BRST/BV problem

The physical abelian gauge differential is nilpotent.  The genuinely odd
exterior-valued diffeomorphism ghost satisfies its cubic Jacobi closure and
acts by a square-zero graded derivation on the genuine smooth scalar algebra;
its two-ghost scalar square cancels exactly.  The linearized diffeomorphism
differential is square-zero.  The corrected linear full-field differential
(including all three LL throat blocks) is square-zero, and the existing
general-metric BV doublet is nilpotent and preserves the current Program-P
boundary domain.  The exact `U(1)²` action orbit is stationary.

The exterior complex, fields, metric antifields and boundary variables now
form one square-zero packet whose differential commutes with the throat
trace.  Canonical time/rotation integration by parts now gives exact skew on
LL coefficient fields, and the global `finiteBV` action has its native finite
null-generator reparametrization invariance.  The bulk time-translation ghost
and all three bulk rotation ghosts have exact derivative-of-inclusion
restrictions to their throat ghosts.  These results do not claim all-ghost
tensor skew.  Candidate A now also has
a nonlinear complete-flow Noether interface; its concrete fixed-measure
nine-block invariance remains an explicit contract.
The existing finite tangent generators now also make the bulk geometric
metric antifield realization faithful. For a supplied global metric
representation, bulk coadjoint closure still requires integrated
skew-adjointness.
This is not yet full `BRST-GLOBAL-01`: invariance of all nine
Candidate-A blocks under this same nonlinear diffeomorphism differential
remains an explicit contract.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalBRSTFrontier4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open MeasureTheory
open P0EFTJanusCompleteVariationGeneralMetricBVBRSTBoundary4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusD8NonabelianGhostBracketNaturality4D
open P0EFTJanusMappingTorusD8NonabelianGhostLinearFullFieldBRST4D
open P0EFTJanusMappingTorusD8NonabelianGhostTriple4D
open P0EFTJanusMappingTorusD8NonabelianGhostThroatBRST4D
open P0EFTJanusMappingTorusExteriorDiffeomorphismGhostBRST4D
open P0EFTJanusMappingTorusExteriorScalarBRSTDerivation4D
open P0EFTJanusMappingTorusGradedScalarGhostAction4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVFirstLevel4D
open P0EFTJanusMappingTorusInducedFieldVariation4D
open P0EFTJanusMappingTorusLinearizedDiffeomorphismBRST4D
open P0EFTJanusMappingTorusMeasuredDensityBRST4D
open P0EFTJanusMappingTorusThroatScalarCoadjointBRST4D
open P0EFTJanusMappingTorusOrdinaryGhostNonlinearBRSTNoGo4D
open P0EFTJanusMappingTorusPhysicalGaugeSobolevComplex4D
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothDiffeomorphismGhostLieBracket4D
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPCommonGeometricDomain4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalEulerLagrange4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalNoether4D
open P0EFTJanusProgramPGlobalDiffeomorphismFlowNoether4D
open P0EFTJanusProgramPNonlinearGlobalBRST4D
open P0EFTJanusProgramPCandidateABRSTInvarianceReduction4D
open P0EFTJanusProgramPThroatMetricGeometricAntifieldDual4D
open P0EFTJanusProgramPTensorialCoadjointAntifieldBRST4D
open P0EFTJanusProgramPGeneralMetricGeometricAntifieldDual4D
open P0EFTJanusProgramPGeneralMetricPositiveDualizer4D
open P0EFTJanusProgramPGeneralMetricTimeTranslationSkew4D
open P0EFTJanusProgramPGeneralMetricTimeTranslationPairingNaturality4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVUltralocalMaster4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVIntegratedMaster4D
open P0EFTJanusMappingTorusTensorialDiffeomorphismRepresentation4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVThroatBoundary4D
open P0EFTJanusMappingTorusIntrinsicMetricBVThroatIntegrated4D
open P0EFTJanusMappingTorusIntrinsicMetricBVThroatBracket4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusProgramPThroatMetricDiagonalDefinitenessNoGo4D
open P0EFTJanusProgramPThroatMetricPositiveDualizer4D
open P0EFTJanusProgramPThroatMetricGeneratingFrameSeparation4D
open P0EFTJanusProgramPThroatMetricFrameEnergySmooth4D
open P0EFTJanusProgramPThroatMetricFrameCovectorSmooth4D
open P0EFTJanusProgramPThroatMetricRestrictedGhostSkew4D
open P0EFTJanusProgramPD8RotationGhostThroatRestriction4D
open P0EFTJanusMappingTorusGlobalMatterArbitraryDiffeomorphismNoether4D
open P0EFTJanusMappingTorusGlobalMatterMultipletDiagonalDiffeomorphismNoether4D
open P0EFTJanusMappingTorusDiagonalDiffeomorphismAction4D
open P0EFTJanusMappingTorusCanonicalTimeTranslationMetricMatterGaugeNoether4D
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusCompleteTimeFlow4D
open P0EFTJanusMappingTorusTimeTranslationMetricMatterGaugeNoether4D
open P0EFTJanusMappingTorusCovariantTensorDiffeomorphismGenerator4D
open P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusNonlinearGaugeFlowNoether

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

attribute [local instance]
  GlobalCandidateAVariationalChart.normedAddCommGroup
  GlobalCandidateAVariationalChart.normedSpace

/-- Every currently constructed BRST layer, with its scope exposed. -/
structure ProgramPGlobalBRSTFrontierCertificate4D where
  abelianSquareZero : ∀ state : AbelianBRSTState period hPeriod,
    brstDifferential period hPeriod
        (brstDifferential period hPeriod state) =
      zeroBRSTState period hPeriod
  exteriorGhostJacobi : ∀ i j k first second third,
    cubicGhostBRSTJacobiObstruction period hPeriod i j k
        first second third = 0
  scalarGradedDerivationSquareZero :
    ∀ (ghost : CInfinityDiffeomorphismGhost period hPeriod)
      (element : OneGhostScalarSuperalgebra period hPeriod),
      (oneGhostScalarBRSTDifferential period hPeriod ghost).toLinearMap
          ((oneGhostScalarBRSTDifferential
            period hPeriod ghost).toLinearMap element) =
        0
  exteriorScalarSquareZero :
    ∀ (first second : CInfinityDiffeomorphismGhost period hPeriod)
      (scalar : CInfinityScalarField period hPeriod),
      twoGhostScalarBRSTSquare period hPeriod first second scalar = 0
  linearizedDiffeomorphismSquareZero :
    ∀ (background : SmoothQuotientField period hPeriod Real)
      (state : LinearizedDiffeomorphismBRSTState period hPeriod),
      linearizedBRSTDifferential period hPeriod background
          (linearizedBRSTDifferential period hPeriod background state) =
        zeroLinearizedBRSTState period hPeriod
  linearFullFieldSquareZero :
    ∀ fields : LinearFullFieldBRST period hPeriod,
      correctedLinearFullFieldBRST period hPeriod
          (unconditionalLLThroatRotationBRSTCompletion period hPeriod)
          (correctedLinearFullFieldBRST period hPeriod
            (unconditionalLLThroatRotationBRSTCompletion period hPeriod)
            fields) =
        0
  metricBVSquareZero : ∀ phase : SmoothGeneralMetricBVField period hPeriod,
    smoothGeneralMetricBVBRST period hPeriod
        (smoothGeneralMetricBVBRST period hPeriod phase) =
      smoothGeneralMetricBVZero period hPeriod
  metricBVBoundaryStable :
    ∀ (domain : ProgramPCommonGeometricDomain4D period hPeriod)
      (variation : IndependentFieldVariation period hPeriod)
      (phase : SmoothGeneralMetricBVField period hPeriod),
      completeVariationWithGeneralMetricBV period hPeriod variation
          (smoothGeneralMetricBVBRST period hPeriod phase) ∈
          programPBoundaryTangentDomain4D period hPeriod domain ↔
        completeVariationWithGeneralMetricBV period hPeriod variation phase ∈
          programPBoundaryTangentDomain4D period hPeriod domain
  ordinaryGhostNoGo :
    (∀ ghost : SmoothDiffeomorphismGhost period hPeriod,
      ordinaryQuadraticGhostBRST period hPeriod ghost = 0) ∧
      ¬ ∃ ghost,
        ordinaryQuadraticGhostBRST period hPeriod ghost ≠ 0
  nonlinearUnifiedSquareZero :
    ∀ packet : ProgramPNonlinearBRSTPacket period hPeriod,
      programPNonlinearBRST period hPeriod
          (programPNonlinearBRST period hPeriod packet) =
        programPNonlinearBRSTZero period hPeriod
  nonlinearBoundaryStable :
    ∀ packet : ProgramPNonlinearBRSTPacket period hPeriod,
      BoundaryCompatible period hPeriod packet →
        BoundaryCompatible period hPeriod
          (programPNonlinearBRST period hPeriod packet)
  nonlinearClosure :
    ProgramPNonlinearBRSTCertificate4D period hPeriod
  measuredDensityClosure :
    MeasuredDensityBRSTCertificate4D period hPeriod
  throatScalarCoadjointClosure :
    ThroatScalarCoadjointBRSTCertificate4D period hPeriod
  throatMetricGeometricAntifieldDual :
    ThroatMetricGeometricAntifieldDualCertificate4D period hPeriod
  metricGeometricAntifieldDual :
    GeneralMetricGeometricAntifieldDualCertificate4D period hPeriod
  metricGeometricAntifieldDualInjective :
    ∀ metrics : SmoothGeneralLorentzMetric period hPeriod ×
        SmoothGeneralLorentzMetric period hPeriod,
      Function.Injective
        (generalMetricGeometricAntifieldToAlgebraicDual
          period hPeriod metrics)
  tensorialCoadjointClosure :
    ∀ actions : TensorialInfinitesimalLieActionData period hPeriod,
      TensorialCoadjointAntifieldBRSTCertificate4D
        period hPeriod actions
  throatLorentzPairingAlgebraicAudit :
    ThroatMetricDiagonalDefinitenessNoGoCertificate4D
  intrinsicMetricTimeTranslationGeneratorZero :
    ∀ point : EffectiveQuotient period hPeriod,
      covariantTensorDiffeomorphismGeneratorAt period hPeriod
          (effectiveTimeFlowDiffeomorph period hPeriod)
          (intrinsicSmoothGeneralLorentzMetric
            period hPeriod).tensor.tensor.toTensorField point =
        0
  canonicalThroatCoefficientSkew :
    ∀ (index : Fin 4)
      (first second : SmoothThroatField period hPeriod LLFieldFiber),
      (∫ point, inner Real
          (throatFrameDerivative period hPeriod LLFieldFiber
            (canonicalDivergenceFreeLLFrame period hPeriod) first point index)
          (second point)
        ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)) +
        ∫ point, inner Real (first point)
          (throatFrameDerivative period hPeriod LLFieldFiber
            (canonicalDivergenceFreeLLFrame period hPeriod) second point index)
          ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod) = 0
  timeTranslationBulkGhostThroatRestriction :
    BulkGhostThroatRestrictionData period hPeriod
      (smoothGhostToCInfinity period hPeriod
        (effectiveTimeTranslationGhost period hPeriod))
  spatialRotationBulkGhostThroatRestriction :
    ∀ axis : Fin 3,
      BulkGhostThroatRestrictionData period hPeriod
        ((unconditionalD8SpatialRotationGhostRealization
          period hPeriod).ghosts axis)
  scalarMatterArbitraryDiffeomorphismInvariant :
    ∀ (configuration :
        GlobalGeneralLorentzMatterConfiguration period hPeriod)
      (curve : Real → SpacetimeDiffeomorphism period hPeriod)
      (parameter : Real),
      HasDerivAt
        (arbitraryDiffeomorphismMatterActionOrbit period hPeriod
          configuration curve) 0 parameter

def programPGlobalBRSTFrontierCertificate4D :
    ProgramPGlobalBRSTFrontierCertificate4D period hPeriod where
  abelianSquareZero := brstDifferential_square_zero period hPeriod
  exteriorGhostJacobi := by
    intro i j k first second third
    exact
      (exterior_diffeomorphism_ghost_brst4D_closure
        period hPeriod).2.2.2 i j k first second third
  scalarGradedDerivationSquareZero := fun ghost =>
    (oneGhostScalarBRSTDifferential period hPeriod ghost).square_zero
  exteriorScalarSquareZero :=
    twoGhostScalarBRSTSquare_zero period hPeriod
  linearizedDiffeomorphismSquareZero :=
    linearizedBRSTDifferential_square_zero period hPeriod
  linearFullFieldSquareZero :=
    correctedLinearFullFieldBRST_square_zero period hPeriod
      (unconditionalLLThroatRotationBRSTCompletion period hPeriod)
  metricBVSquareZero :=
    smoothGeneralMetricBVBRST_square_zero period hPeriod
  metricBVBoundaryStable :=
    completeVariationWithGeneralMetricBV_BRST_mem_boundaryDomain_iff
      period hPeriod
  ordinaryGhostNoGo :=
    ordinary_ghost_nonlinear_brst_noGo period hPeriod
  nonlinearUnifiedSquareZero :=
    programPNonlinearBRST_square_zero period hPeriod
  nonlinearBoundaryStable :=
    programPNonlinearBRST_boundary_stable period hPeriod
  nonlinearClosure :=
    programPNonlinearBRSTCertificate4D period hPeriod
  measuredDensityClosure :=
    measuredDensityBRSTCertificate4D period hPeriod
  throatScalarCoadjointClosure :=
    throatScalarCoadjointBRSTCertificate4D period hPeriod
  throatMetricGeometricAntifieldDual :=
    throatMetricGeometricAntifieldDualCertificate4D period hPeriod
  metricGeometricAntifieldDual :=
    generalMetricGeometricAntifieldDualCertificate4D period hPeriod
  metricGeometricAntifieldDualInjective :=
    generalMetricGeometricAntifieldToAlgebraicDual_injective
      period hPeriod
  tensorialCoadjointClosure :=
    programP_tensorial_coadjoint_antifield_gate period hPeriod
  throatLorentzPairingAlgebraicAudit :=
    throatMetricDiagonalDefinitenessNoGoCertificate4D
  intrinsicMetricTimeTranslationGeneratorZero :=
    intrinsicSmoothTensor_timeTranslation_generator_zero period hPeriod
  canonicalThroatCoefficientSkew :=
    canonicalGenerator_integral_inner_derivative_add_eq_zero
      period hPeriod
  timeTranslationBulkGhostThroatRestriction :=
    effectiveTimeTranslationBulkGhostThroatRestriction period hPeriod
  spatialRotationBulkGhostThroatRestriction :=
    unconditionalD8SpatialRotationBulkGhostThroatRestriction period hPeriod
  scalarMatterArbitraryDiffeomorphismInvariant :=
    arbitraryDiffeomorphismMatterActionOrbit_hasDerivAt_zero period hPeriod

/-- Scoped concrete metric BRST gate: the canonical intrinsic metric is
fixed infinitesimally by the genuine complete time-translation subgroup.
This does not claim a representation for arbitrary smooth ghosts. -/
theorem global_intrinsic_metric_timeTranslation_brst_gate
    (point : EffectiveQuotient period hPeriod) :
    covariantTensorDiffeomorphismGeneratorAt period hPeriod
        (effectiveTimeFlowDiffeomorph period hPeriod)
        (intrinsicSmoothGeneralLorentzMetric
          period hPeriod).tensor.tensor.toTensorField point =
      0 :=
  intrinsicSmoothTensor_timeTranslation_generator_zero
    period hPeriod point

/-- Cartan evaluation in the Maxwell and metric sectors discharges both
tensorial bracket obligations before passing to algebraic coadjoints. -/
theorem global_tensorial_cartan_coadjoint_gate
    (data : TensorialCartanActionData period hPeriod) :
    TensorialCoadjointAntifieldBRSTCertificate4D period hPeriod
      (data.toTensorialInfinitesimalLieActionData period hPeriod) :=
  programP_tensorial_coadjoint_antifield_gate period hPeriod
    (data.toTensorialInfinitesimalLieActionData period hPeriod)

/-- The exact assembled action is stationary along every paired smooth
abelian BRST ghost orbit. -/
theorem global_physical_u1_brst_action_gate
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (measure : Measure (EffectiveQuotient period hPeriod))
    (ghosts : PhysicalPairedGaugeGhost period hPeriod) :
    HasDerivAt
      (globalCandidateAPhysicalGaugeOrbit
        period hPeriod data measure ghosts) 0 0 :=
  globalCandidateAPhysicalGaugeOrbit_hasDerivAt_zero
    period hPeriod data measure ghosts

/-- Scoped ninth-block gate: the exact finite null-face/counterterm/joint
functional is invariant under null-generator reparametrization.  This is not
yet invariance under the ambient affine diffeomorphism-ghost chart action. -/
theorem global_candidateA_finiteBV_null_reparametrization_gate
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (configuration : chart.Configuration)
    (contract :
      GlobalCandidateANullBoundaryReparametrizationIntegrability
        period hPeriod (chart.family.dataAt configuration)) :
    globalCandidateAReparametrizedNullBoundaryAction period hPeriod
        (chart.family.dataAt configuration) =
      (globalCandidateAActionBlocks
        period hPeriod chart.family measure).finiteBV configuration := by
  change globalCandidateAReparametrizedNullBoundaryAction period hPeriod
      (chart.family.dataAt configuration) =
    globalCandidateANullBoundaryAction period hPeriod
      (chart.family.dataAt configuration)
  exact globalCandidateAReparametrizedNullBoundaryAction_eq
    period hPeriod (chart.family.dataAt configuration) contract

theorem global_brst_frontier_gate :
    Nonempty (ProgramPGlobalBRSTFrontierCertificate4D period hPeriod) :=
  ⟨programPGlobalBRSTFrontierCertificate4D period hPeriod⟩

/-- Exact final reduction: a termwise nine-block diffeomorphism symmetry
simultaneously yields action invariance, Noether, nilpotence and boundary
stability. -/
theorem global_candidateA_nonlinear_brst_reduction_gate
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (symmetry :
      GlobalCandidateADiffeomorphismGaugeSymmetry
        period hPeriod chart) :
    CandidateANonlinearBRSTInvarianceReduction4D
      period hPeriod chart symmetry :=
  candidateANonlinearBRSTInvarianceReduction4D
    period hPeriod chart symmetry

/-- Correct nonlinear-flow replacement for the affine diffeomorphism chart
line: termwise invariance gives exact action invariance and the Noether
identity for the field-dependent generator of each complete ghost flow. -/
theorem global_candidateA_diffeomorphism_flow_noether_gate
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (symmetry :
      GlobalCandidateADiffeomorphismFlowSymmetry period hPeriod chart)
    (ghost : CInfinityDiffeomorphismGhost period hPeriod) :
    FlowGaugeInvariant (symmetry.flow ghost)
        (globalCandidateAActionPullback period hPeriod chart) ∧
      EulerAnnihilatesGenerator (symmetry.flow ghost)
        (globalEulerLagrangeOperator period hPeriod chart) :=
  ⟨globalCandidateAAction_diffeomorphismFlow_invariant
      period hPeriod chart symmetry ghost,
    globalEuler_annihilates_diffeomorphismFlowGenerator
      period hPeriod chart symmetry ghost⟩

/-- The finite smooth tangent frame and canonical full-support bulk volume
make the geometric two-metric antifield realization faithful. -/
theorem global_metric_geometric_antifield_injective_gate
    (metrics : SmoothGeneralLorentzMetric period hPeriod ×
      SmoothGeneralLorentzMetric period hPeriod) :
    Function.Injective
      (generalMetricGeometricAntifieldToAlgebraicDual
        period hPeriod metrics) :=
  generalMetricGeometricAntifieldToAlgebraicDual_injective
    period hPeriod metrics

/-- Exact remaining infinitesimal obligation for the genuine complete time
subgroup: the supplied action must equal the pointwise derivative of the
actual tensor pullback orbit. This contract does not assert differentiation
under the integrated pairing or skew-adjointness. -/
abbrev GlobalMetricTimeTranslationGeneratorBridgeObligation
    (representation :
      SmoothGhostLieRepresentation period hPeriod
        (SmoothGeneralMetricTensorPair period hPeriod)) : Prop :=
  GeneralMetricTimeTranslationOrbitGeneratorBridge period hPeriod
    representation

/-- Proven scalar statement at the current frontier: finite naturality makes
the integrated intrinsic pairing orbit constant, hence its derivative is
zero. No identification with the infinitesimal representation is claimed. -/
theorem global_metric_timeTranslation_pairingOrbit_hasDerivAt_zero_gate
    (first second : SmoothGeneralMetricTensorPair period hPeriod) :
    HasDerivAt
      (fun parameter =>
        canonicalGeneralMetricTensorPairPairing period hPeriod
          (intrinsicGeneralLorentzMetricPair period hPeriod)
          (generalMetricTimeTranslationTensorOrbit
            period hPeriod parameter first)
          (generalMetricTimeTranslationTensorOrbit
            period hPeriod parameter second))
      0 0 :=
  canonicalGeneralMetricTensorPairPairing_intrinsic_timeTranslation_hasDerivAt_zero
    period hPeriod first second

/-- Bulk metric coadjoint closure for one supplied representation now
requires only its integrated skew-adjointness identity. -/
theorem global_metric_geometric_coadjoint_gate
    (metrics : SmoothGeneralLorentzMetric period hPeriod ×
      SmoothGeneralLorentzMetric period hPeriod)
    (representation :
      SmoothGhostLieRepresentation period hPeriod
        (SmoothGeneralMetricTensorPair period hPeriod))
    (hSkew :
      ∀ (ghost : CInfinityDiffeomorphismGhost period hPeriod)
        (antifield field :
          SmoothGeneralMetricTensorPair period hPeriod),
        canonicalGeneralMetricTensorPairPairing period hPeriod metrics
            (representation.action ghost antifield) field +
          canonicalGeneralMetricTensorPairPairing period hPeriod metrics
            antifield
            (representation.action ghost field) = 0) :
    GeneralMetricGeometricCoadjointBridgeData
      period hPeriod metrics representation where
  pairingNondegenerate :=
    generalMetricGeometricAntifieldToAlgebraicDual_injective
      period hPeriod metrics
  coadjointIntertwining := by
    intro ghost antifield
    exact
      (generalMetricGeometricAntifield_coadjointIntertwining_iff
        period hPeriod metrics representation ghost antifield).2
        (hSkew ghost antifield)

/-- Exact analytic completion gate for the faithful geometric throat-metric
coadjoint sector. -/
theorem global_throat_metric_geometric_coadjoint_gate
    (representation :
      SmoothGhostLieRepresentation period hPeriod
        (SmoothThroatGeneralMetricTensorPair period hPeriod))
    (hDiagonal :
      ∀ antifield : SmoothThroatGeneralMetricTensorPair period hPeriod,
        canonicalIntrinsicThroatTensorPairPairing
            period hPeriod antifield antifield = 0 →
          antifield = 0)
    (hSkew :
      ∀ ghost antifield field,
        canonicalIntrinsicThroatTensorPairPairing period hPeriod
            (representation.action ghost antifield) field +
          canonicalIntrinsicThroatTensorPairPairing period hPeriod
            antifield (representation.action ghost field) = 0) :
    ThroatMetricGeometricCoadjointBridgeData
      period hPeriod representation :=
  throatMetricGeometricCoadjointBridgeData_of_diagonal_skew
    period hPeriod representation hDiagonal hSkew

/-- Exact Lorentz-compatible completion gate using bilinear separation,
rather than the generally false diagonal-definiteness route. -/
theorem global_throat_metric_geometric_coadjoint_separation_gate
    (representation :
      SmoothGhostLieRepresentation period hPeriod
        (SmoothThroatGeneralMetricTensorPair period hPeriod))
    (hSeparates :
      ∀ antifield : SmoothThroatGeneralMetricTensorPair period hPeriod,
        (∀ field,
          canonicalIntrinsicThroatTensorPairPairing
            period hPeriod antifield field = 0) →
        antifield = 0)
    (hSkew :
      ∀ ghost antifield field,
        canonicalIntrinsicThroatTensorPairPairing period hPeriod
            (representation.action ghost antifield) field +
          canonicalIntrinsicThroatTensorPairPairing period hPeriod
            antifield (representation.action ghost field) = 0) :
    ThroatMetricGeometricCoadjointBridgeData
      period hPeriod representation :=
  throatMetricGeometricCoadjointBridgeData_of_separation_skew
    period hPeriod representation hSeparates hSkew

/-- Canonical full-support globalization gate: a positive smooth dualizer
discharges integrated separation, leaving only skew-adjointness. -/
theorem global_throat_metric_geometric_coadjoint_positiveDualizer_gate
    (representation :
      SmoothGhostLieRepresentation period hPeriod
        (SmoothThroatGeneralMetricTensorPair period hPeriod))
    (data : ThroatMetricSmoothPositiveDualizerData period hPeriod)
    (hSkew :
      ∀ ghost antifield field,
        canonicalIntrinsicThroatTensorPairPairing period hPeriod
            (representation.action ghost antifield) field +
          canonicalIntrinsicThroatTensorPairPairing period hPeriod
            antifield (representation.action ghost field) = 0) :
    ThroatMetricGeometricCoadjointBridgeData
      period hPeriod representation :=
  throatMetricGeometricCoadjointBridgeData_of_positiveDualizer_skew
    period hPeriod representation data hSkew

/-- Concrete finite-frame reduction: once the smooth tensor test realizes the
existing generating-frame sum of squares, pointwise separation and
full-support globalization are automatic. -/
theorem global_throat_metric_geometric_coadjoint_frameEnergy_gate
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (dualize :
      SmoothThroatGeneralMetricTensorPair period hPeriod →
        SmoothThroatGeneralMetricTensorPair period hPeriod)
    (hContinuous :
      ∀ antifield,
        Continuous
          (fun point =>
            intrinsicThroatTensorPairPairingAt period hPeriod
              antifield (dualize antifield) point))
    (hPairing :
      ∀ antifield point,
        intrinsicThroatTensorPairPairingAt period hPeriod
            antifield (dualize antifield) point =
          throatMetricPairFrameEnergy
            period hPeriod frame antifield point)
    (representation :
      SmoothGhostLieRepresentation period hPeriod
        (SmoothThroatGeneralMetricTensorPair period hPeriod))
    (hSkew :
      ∀ ghost antifield field,
        canonicalIntrinsicThroatTensorPairPairing period hPeriod
            (representation.action ghost antifield) field +
          canonicalIntrinsicThroatTensorPairPairing period hPeriod
            antifield (representation.action ghost field) = 0) :
    ThroatMetricGeometricCoadjointBridgeData
      period hPeriod representation :=
  global_throat_metric_geometric_coadjoint_positiveDualizer_gate
    period hPeriod representation
    (throatMetricSmoothPositiveDualizerData_of_frameEnergy
      period hPeriod frame dualize hContinuous hPairing)
    hSkew

/-- Smooth finite-frame reduction with continuity discharged
unconditionally by the existing bundlewise contraction calculus. -/
theorem global_throat_metric_geometric_coadjoint_smoothFrameEnergy_gate
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (dualize :
      SmoothThroatGeneralMetricTensorPair period hPeriod →
        SmoothThroatGeneralMetricTensorPair period hPeriod)
    (hPairing :
      ∀ antifield point,
        intrinsicThroatTensorPairPairingAt period hPeriod
            antifield (dualize antifield) point =
          throatMetricPairFrameEnergy
            period hPeriod frame antifield point)
    (representation :
      SmoothGhostLieRepresentation period hPeriod
        (SmoothThroatGeneralMetricTensorPair period hPeriod))
    (hSkew :
      ∀ ghost antifield field,
        canonicalIntrinsicThroatTensorPairPairing period hPeriod
            (representation.action ghost antifield) field +
          canonicalIntrinsicThroatTensorPairPairing period hPeriod
            antifield (representation.action ghost field) = 0) :
    ThroatMetricGeometricCoadjointBridgeData
      period hPeriod representation :=
  global_throat_metric_geometric_coadjoint_positiveDualizer_gate
    period hPeriod representation
    (throatMetricSmoothPositiveDualizerData_of_frameEnergyPairing
      period hPeriod frame dualize hPairing)
    hSkew

/-- For a supplied frame and representation, the canonical smooth
tensor-valued dualizer discharges positivity. Integrated skew-adjointness
remains an additional input. -/
theorem global_throat_metric_geometric_coadjoint_assembledFrameDualizer_gate
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (representation :
      SmoothGhostLieRepresentation period hPeriod
        (SmoothThroatGeneralMetricTensorPair period hPeriod))
    (hSkew :
      ∀ ghost antifield field,
        canonicalIntrinsicThroatTensorPairPairing period hPeriod
            (representation.action ghost antifield) field +
          canonicalIntrinsicThroatTensorPairPairing period hPeriod
            antifield (representation.action ghost field) = 0) :
    ThroatMetricGeometricCoadjointBridgeData
      period hPeriod representation :=
  global_throat_metric_geometric_coadjoint_smoothFrameEnergy_gate
    period hPeriod frame
    (intrinsicThroatMetricPairSmoothFrameDualizer
      period hPeriod frame)
    (intrinsicThroatMetricPairSmoothFrameDualizer_pairing_eq_energy
      period hPeriod frame)
    representation hSkew

end
end P0EFTJanusProgramPGlobalBRSTFrontier4D
end JanusFormal
