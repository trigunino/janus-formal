import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarCoordinateL24D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12CandidateAAbelianGhostMinimalCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12CandidateAAbelianGhostL2Pairing4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12CandidateAFPFormalAdjointCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12OffDiagonalCore4D

/-! Explicit spatial polynomial ghosts form a dense family in the minimal BRST domain. -/
namespace JanusFormal
namespace P0EFTJanusProgramPT12AbelianPolynomialDenseDomain4D
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

abbrev PolynomialGhostCoefficients := GlobalPairedAbelianLorenzCoordinateIndex → scalarCoordinateAlgebra period

def polynomialGhost (coefficients : PolynomialGhostCoefficients period) : GlobalPairedGaugeLieSmooth period hPeriod :=
  globalPairedGaugeLieSmoothOfComponents period hPeriod (fun i => scalarCoordinateSmoothMap period hPeriod (coefficients i))

def polynomialGhostL2 : PolynomialGhostCoefficients period →ₗ[Real] GlobalPairedGaugeLieL2 period hPeriod where
  toFun coefficients := WithLp.toLp 2 fun i => scalarCoordinateToL2 period hPeriod (coefficients i)
  map_add' first second := by
    apply PiLp.ext
    intro i
    exact map_add (scalarCoordinateToL2 period hPeriod) _ _
  map_smul' r coefficients := by
    apply PiLp.ext
    intro i
    exact map_smul (scalarCoordinateToL2 period hPeriod) _ _

theorem polynomialGhostL2_eq_smooth (coefficients : PolynomialGhostCoefficients period) :
    polynomialGhostL2 period hPeriod coefficients =
      globalPairedGaugeLieL2LinearMap period hPeriod (polynomialGhost period hPeriod coefficients) := by
  apply PiLp.ext
  intro i
  change scalarCoordinateToL2 period hPeriod (coefficients i) =
    smoothToCanonicalPhysicalBulkL2 period hPeriod
      (ghostComponent period hPeriod (globalPairedGaugeLieSmoothOfComponents period hPeriod
        (fun j => scalarCoordinateSmoothMap period hPeriod (coefficients j)) i.1) i.2)
  rw [ghostComponent_globalPairedGaugeLieSmoothOfComponents, scalarCoordinateToL2_eq_smooth]

theorem polynomialGhostL2_denseRange : DenseRange (polynomialGhostL2 period hPeriod) := by
  let coordinateEquiv := PiLp.continuousLinearEquiv 2 Real
    (fun _ : GlobalPairedAbelianLorenzCoordinateIndex => CanonicalPhysicalBulkL2 period hPeriod)
  have hCoordinates : DenseRange (coordinateEquiv ∘ polynomialGhostL2 period hPeriod) :=
    DenseRange.piMap fun _ => scalarCoordinateToL2_denseRange period hPeriod
  have hBack := coordinateEquiv.symm.surjective.denseRange.comp hCoordinates coordinateEquiv.symm.continuous
  simpa [coordinateEquiv, Function.comp_def] using hBack

def polynomialGhostInput (pair : PolynomialGhostCoefficients period × PolynomialGhostCoefficients period) :
    CandidateAAbelianGhostL2 period hPeriod :=
  WithLp.toLp 2 (polynomialGhostL2 period hPeriod pair.1, polynomialGhostL2 period hPeriod pair.2)

theorem polynomialGhostInput_denseRange : DenseRange (polynomialGhostInput period hPeriod) := by
  have hDense := (polynomialGhostL2_denseRange period hPeriod).prodMap (polynomialGhostL2_denseRange period hPeriod)
  exact (WithLp.prodContinuousLinearEquiv 2 Real
    (GlobalPairedGaugeLieL2 period hPeriod) (GlobalPairedGaugeLieL2 period hPeriod)).symm.surjective.denseRange.comp
      hDense (WithLp.prodContinuousLinearEquiv 2 Real
        (GlobalPairedGaugeLieL2 period hPeriod) (GlobalPairedGaugeLieL2 period hPeriod)).symm.continuous

/-- The spatial polynomial pair belongs to the actual minimal graph, with the full metric-dependent image. -/
theorem polynomialGhostInput_minimal_graph
    (pair : PolynomialGhostCoefficients period × PolynomialGhostCoefficients period) :
    (polynomialGhostInput period hPeriod pair,
      WithLp.toLp 2
        (globalPairedAbelianFPL2LinearMap period hPeriod (globalCandidateAMetricBySector period hPeriod data)
          (polynomialGhost period hPeriod pair.2),
        pairedFPCanonicalAdjointL2 period hPeriod (globalCandidateAMetricBySector period hPeriod data)
          (polynomialGhost period hPeriod pair.1))) ∈
      (candidateAAbelianGhostMinimal period hPeriod data).graph := by
  unfold polynomialGhostInput
  rw [polynomialGhostL2_eq_smooth, polynomialGhostL2_eq_smooth]
  apply (offDiagonalOperator_mem_graph_iff _ _ _ _).mpr
  constructor
  · exact (LinearPMap.mem_graph_iff _).mpr
      ⟨⟨_, candidateAFPCanonicalMinimal_smooth_mem period hPeriod data (polynomialGhost period hPeriod pair.2)⟩,
        rfl, candidateAFPCanonicalMinimal_smooth_apply period hPeriod data _⟩
  · exact (LinearPMap.mem_graph_iff _).mpr
      ⟨⟨_, candidateAFPFormalAdjointMinimal_smooth_mem period hPeriod data (polynomialGhost period hPeriod pair.1)⟩,
        rfl, candidateAFPFormalAdjointMinimal_smooth_apply period hPeriod data _⟩

theorem polynomialGhostInput_mem_domain
    (pair : PolynomialGhostCoefficients period × PolynomialGhostCoefficients period) :
    polynomialGhostInput period hPeriod pair ∈ (candidateAAbelianGhostMinimal period hPeriod data).domain := by
  obtain ⟨state, hInput, _⟩ := (LinearPMap.mem_graph_iff _).mp
    (polynomialGhostInput_minimal_graph period hPeriod data pair)
  change (state : CandidateAAbelianGhostL2 period hPeriod) = polynomialGhostInput period hPeriod pair at hInput
  exact hInput ▸ state.property

end
end P0EFTJanusProgramPT12AbelianPolynomialDenseDomain4D
end JanusFormal
