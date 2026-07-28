import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalNoether4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCompleteVariationGeneralMetricBVBRSTBoundary4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusD8NonabelianGhostThroatBRST4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusExteriorDiffeomorphismGhostBRST4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusExteriorScalarBRSTDerivation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusLinearizedDiffeomorphismBRST4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusOrdinaryGhostNonlinearBRSTNoGo4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPNonlinearGlobalBRST4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGlobalMatterArbitraryDiffeomorphismNoether4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusMeasuredDensityBRST4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusThroatScalarCoadjointBRST4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPCandidateABRSTInvarianceReduction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPThroatMetricGeometricAntifieldDual4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPTensorialCoadjointAntifieldBRST4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGeneralMetricGeometricAntifieldDual4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPThroatMetricDiagonalDefinitenessNoGo4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPThroatMetricPositiveDualizer4D

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
trace.  This is not yet full `BRST-GLOBAL-01`: invariance of all nine
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
open P0EFTJanusMappingTorusD8NonabelianGhostLinearFullFieldBRST4D
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
open P0EFTJanusProgramPNonlinearGlobalBRST4D
open P0EFTJanusProgramPCandidateABRSTInvarianceReduction4D
open P0EFTJanusProgramPThroatMetricGeometricAntifieldDual4D
open P0EFTJanusProgramPTensorialCoadjointAntifieldBRST4D
open P0EFTJanusProgramPGeneralMetricGeometricAntifieldDual4D
open P0EFTJanusMappingTorusTensorialDiffeomorphismRepresentation4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVThroatBoundary4D
open P0EFTJanusMappingTorusIntrinsicMetricBVThroatIntegrated4D
open P0EFTJanusProgramPThroatMetricDiagonalDefinitenessNoGo4D
open P0EFTJanusProgramPThroatMetricPositiveDualizer4D
open P0EFTJanusMappingTorusGlobalMatterArbitraryDiffeomorphismNoether4D
open P0EFTJanusMappingTorusGlobalMatterMultipletDiagonalDiffeomorphismNoether4D
open P0EFTJanusMappingTorusDiagonalDiffeomorphismAction4D

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
  tensorialCoadjointClosure :
    ∀ actions : TensorialInfinitesimalLieActionData period hPeriod,
      TensorialCoadjointAntifieldBRSTCertificate4D
        period hPeriod actions
  throatLorentzPairingAlgebraicAudit :
    ThroatMetricDiagonalDefinitenessNoGoCertificate4D
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
  tensorialCoadjointClosure :=
    programP_tensorial_coadjoint_antifield_gate period hPeriod
  throatLorentzPairingAlgebraicAudit :=
    throatMetricDiagonalDefinitenessNoGoCertificate4D
  scalarMatterArbitraryDiffeomorphismInvariant :=
    arbitraryDiffeomorphismMatterActionOrbit_hasDerivAt_zero period hPeriod

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

end
end P0EFTJanusProgramPGlobalBRSTFrontier4D
end JanusFormal
