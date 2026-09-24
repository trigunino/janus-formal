import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12ProjectedGraphCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12AbelianPolynomialDenseDomain4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarCoordinateL24D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12CandidateAAbelianGhostMinimalCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12CandidateAAbelianGhostL2Pairing4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12CandidateAFPFormalAdjointCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12OffDiagonalCore4D

/-! Polynomial ambient samples give genuine cores of both actual abelian ghost realizations. -/
namespace JanusFormal
namespace P0EFTJanusProgramPT12AbelianPolynomialProjectedCore4D
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 600000
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory Set
open scoped ENNReal Manifold ContDiff InnerProductSpace Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
open P0EFTJanusMappingTorusL2PTFunctionalSpace4D
open P0EFTJanusMappingTorusPhysicalGaugeSobolevComplex4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusGlobalGeneralMetricAbelianLorenzCodifferential4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalGaugeTangentIntrinsicEmbedding4D
open P0EFTJanusProgramPGlobalPairedAbelianBRSTGaugeFermion4D
open P0EFTJanusProgramPGlobalAbelianLorenzGraphRiesz4D

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

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance canonicalLorentzVolumeFinite :
    IsFiniteMeasure
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

open P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D


local instance (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    CompleteSpace (GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric) :=
  globalPairedAbelianOffShellGraphCompleteSpace period hPeriod metric

open P0EFTJanusProgramPT12FPCanonicalFormalAdjoint4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
set_option backward.isDefEq.respectTransparency false

open P0EFTJanusProgramPT12PairedFPCanonicalAdjoint4D
open P0EFTJanusProgramPT12DenseAdjointGraphClosable4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTAbelianNakanishiLautrupL2Residual4D

open P0EFTJanusProgramPT12PairedFPClosable4D
open P0EFTJanusProgramPT12AbelianTwoSidedGhostGraph4D
open P0EFTJanusProgramPT12AbelianTwoSidedGhostRotation4D
open P0EFTJanusProgramPT12AbelianGhostSmoothRotation4D
open P0EFTJanusProgramPT12AbelianTwoSidedSignedPairing4D
open P0EFTJanusProgramPT12AbelianLorenzGraphShear4D

open P0EFTJanusProgramPT12AbelianTwoSidedForgetInjective4D

variable {configuration : GlobalFieldConfiguration period hPeriod}
variable {couplings : GlobalCandidateAActionCouplings}
variable {NonNullFace NullFace : Type*}
variable [Fintype NonNullFace] [Fintype NullFace]
variable (data : GlobalCandidateAActionData period hPeriod configuration couplings
  NonNullFace NullFace)

open P0EFTJanusProgramPT12CandidateAAbelianFaithfulRealization4D
open P0EFTJanusProgramPT12ClosedFeatureOperator4D

open P0EFTJanusProgramPT12CandidateAFPCanonicalClosed4D
open P0EFTJanusProgramPT12ClosedFeatureAdjoint4D

open P0EFTJanusProgramPT12CandidateAFPCanonicalAdjoint4D
open P0EFTJanusProgramPT12OffDiagonalClosedOperator4D
open P0EFTJanusProgramPT12OffDiagonalSelfAdjoint4D

open P0EFTJanusProgramPT12CandidateAAbelianGhostSelfAdjoint4D
open P0EFTJanusProgramPT12AbelianGhostIntrinsicDefect4D
open P0EFTJanusProgramPT12GhostRotationDefect4D

open P0EFTJanusProgramPT12CandidateAFPFormalAdjointCore4D
open P0EFTJanusProgramPT12ClosedFeatureCore4D
open P0EFTJanusProgramPT12OffDiagonalClosure4D
open P0EFTJanusProgramPT12OffDiagonalCore4D

open P0EFTJanusMappingTorusScalarCoordinateDensity4D
open P0EFTJanusMappingTorusScalarCoordinateL24D
open P0EFTJanusProgramPGlobalAbelianFaddeevPopovGreenStokes4D
open P0EFTJanusProgramPT12CandidateAAbelianGhostMinimalCore4D
variable [hPos : Fact (0 < period)]

open P0EFTJanusProgramPT12AbelianPolynomialDenseDomain4D
open P0EFTJanusProgramPT12ProjectedGraphCore4D

private def polynomialGhostInputLinearMap :
    PolynomialGhostCoefficients period × PolynomialGhostCoefficients period →ₗ[Real]
      CandidateAAbelianGhostL2 period hPeriod :=
  (WithLp.prodContinuousLinearEquiv 2 Real
    (GlobalPairedGaugeLieL2 period hPeriod) (GlobalPairedGaugeLieL2 period hPeriod)).symm.toLinearMap.comp
    ((polynomialGhostL2 period hPeriod).prodMap (polynomialGhostL2 period hPeriod))

abbrev PolynomialGhostGraphCoefficients :=
  (PolynomialGhostCoefficients period × PolynomialGhostCoefficients period) ×
  (PolynomialGhostCoefficients period × PolynomialGhostCoefficients period)

def polynomialGhostGraphSamples : PolynomialGhostGraphCoefficients period →ₗ[Real]
    WithLp 2 (CandidateAAbelianGhostL2 period hPeriod × CandidateAAbelianGhostL2 period hPeriod) :=
  (WithLp.prodContinuousLinearEquiv 2 Real
    (CandidateAAbelianGhostL2 period hPeriod) (CandidateAAbelianGhostL2 period hPeriod)).symm.toLinearMap.comp
    ((polynomialGhostInputLinearMap period hPeriod).prodMap (polynomialGhostInputLinearMap period hPeriod))

theorem polynomialGhostGraphSamples_denseRange : DenseRange (polynomialGhostGraphSamples period hPeriod) :=
  (WithLp.prodContinuousLinearEquiv 2 Real
    (CandidateAAbelianGhostL2 period hPeriod) (CandidateAAbelianGhostL2 period hPeriod)).symm.surjective.denseRange.comp
      ((polynomialGhostInput_denseRange period hPeriod).prodMap (polynomialGhostInput_denseRange period hPeriod))
      (WithLp.prodContinuousLinearEquiv 2 Real
        (CandidateAAbelianGhostL2 period hPeriod) (CandidateAAbelianGhostL2 period hPeriod)).symm.continuous

def abelianPolynomialMinimalCore : Submodule Real (CandidateAAbelianGhostL2 period hPeriod) :=
  (projectedCoreInput (candidateAAbelianGhostMinimal period hPeriod data)
    (candidateAAbelianGhostMinimal_isClosed period hPeriod data) (polynomialGhostGraphSamples period hPeriod)).range

theorem abelianPolynomialMinimalCore_hasCore :
    (candidateAAbelianGhostMinimal period hPeriod data).HasCore (abelianPolynomialMinimalCore period hPeriod data) :=
  projectedCore_hasCore _ _ _ (polynomialGhostGraphSamples_denseRange period hPeriod)

/-- This is a core of the canonical self-adjoint realization; no minimal/maximal equality is assumed. -/
def abelianPolynomialSelfAdjointCore : Submodule Real (CandidateAAbelianGhostL2 period hPeriod) :=
  (projectedCoreInput (candidateAAbelianGhostOperator period hPeriod data)
    (candidateAAbelianGhostOperator_isClosed period hPeriod data) (polynomialGhostGraphSamples period hPeriod)).range

theorem abelianPolynomialSelfAdjointCore_hasCore :
    (candidateAAbelianGhostOperator period hPeriod data).HasCore (abelianPolynomialSelfAdjointCore period hPeriod data) :=
  projectedCore_hasCore _ _ _ (polynomialGhostGraphSamples_denseRange period hPeriod)

/-- Projection computes the field and its image in the actual self-adjoint graph. -/
theorem abelianPolynomialSelfAdjointCore_apply (coefficients : PolynomialGhostGraphCoefficients period) :
    candidateAAbelianGhostOperator period hPeriod data
      ⟨projectedCoreInput (candidateAAbelianGhostOperator period hPeriod data)
        (candidateAAbelianGhostOperator_isClosed period hPeriod data)
        (polynomialGhostGraphSamples period hPeriod) coefficients,
       projectedCore_mem_domain _ _ _ coefficients⟩ =
      projectedCoreOutput (candidateAAbelianGhostOperator period hPeriod data)
        (candidateAAbelianGhostOperator_isClosed period hPeriod data)
        (polynomialGhostGraphSamples period hPeriod) coefficients :=
  projectedCore_apply _ _ _ coefficients

/-- Exact weak characterization of the actual graph, including nonsmooth domain elements. -/
theorem abelianPolynomialSelfAdjointCore_graph_iff
    (input output : CandidateAAbelianGhostL2 period hPeriod) :
    (input, output) ∈ (candidateAAbelianGhostOperator period hPeriod data).graph ↔
    ∀ coefficients : PolynomialGhostGraphCoefficients period,
      inner Real (projectedCoreOutput (candidateAAbelianGhostOperator period hPeriod data)
        (candidateAAbelianGhostOperator_isClosed period hPeriod data)
        (polynomialGhostGraphSamples period hPeriod) coefficients) input =
      inner Real (projectedCoreInput (candidateAAbelianGhostOperator period hPeriod data)
        (candidateAAbelianGhostOperator_isClosed period hPeriod data)
        (polynomialGhostGraphSamples period hPeriod) coefficients) output :=
  projectedCore_selfAdjoint_graph_iff _ _ _
    (polynomialGhostGraphSamples_denseRange period hPeriod)
    (candidateAAbelianGhostOperator_dense_domain period hPeriod data)
    (candidateAAbelianGhostOperator_selfAdjoint period hPeriod data) input output

theorem abelianPolynomialSelfAdjointCore_domain_iff
    (input : CandidateAAbelianGhostL2 period hPeriod) :
    input ∈ (candidateAAbelianGhostOperator period hPeriod data).domain ↔
    ∃ output, ∀ coefficients : PolynomialGhostGraphCoefficients period,
      inner Real (projectedCoreOutput (candidateAAbelianGhostOperator period hPeriod data)
        (candidateAAbelianGhostOperator_isClosed period hPeriod data)
        (polynomialGhostGraphSamples period hPeriod) coefficients) input =
      inner Real (projectedCoreInput (candidateAAbelianGhostOperator period hPeriod data)
        (candidateAAbelianGhostOperator_isClosed period hPeriod data)
        (polynomialGhostGraphSamples period hPeriod) coefficients) output := by
  constructor
  · intro hInput
    exact ⟨_, (abelianPolynomialSelfAdjointCore_graph_iff period hPeriod data _ _).mp
      ((candidateAAbelianGhostOperator period hPeriod data).mem_graph ⟨input, hInput⟩)⟩
  · rintro ⟨output, hPair⟩
    obtain ⟨vector, hInput, _⟩ := (LinearPMap.mem_graph_iff _).mp
      ((abelianPolynomialSelfAdjointCore_graph_iff period hPeriod data input output).mpr hPair)
    change (vector : CandidateAAbelianGhostL2 period hPeriod) = input at hInput
    exact hInput ▸ vector.property

end
end P0EFTJanusProgramPT12AbelianPolynomialProjectedCore4D
end JanusFormal
