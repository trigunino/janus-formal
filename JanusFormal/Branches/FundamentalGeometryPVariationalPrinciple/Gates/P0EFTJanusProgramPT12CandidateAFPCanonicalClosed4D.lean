import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12CandidateAAbelianFaithfulRealization4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12ClosedFeatureOperator4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12GraphClosureEstimate4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12NormalGraphResolvent4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12MinimalNormInverse4D

/-! The actual Candidate-A FP as a minimal closed operator in canonical L2. -/
namespace JanusFormal
namespace P0EFTJanusProgramPT12CandidateAFPCanonicalClosed4D
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

/-- Closure of the genuine smooth FP graph, using the actual two gravity metrics. -/
def candidateAFPCanonicalMinimal :
    GlobalPairedGaugeLieL2 period hPeriod →ₗ.[Real] GlobalPairedGaugeLieL2 period hPeriod :=
  closedFeatureOperator (globalPairedGaugeLieL2LinearMap period hPeriod)
    (globalPairedAbelianFPL2LinearMap period hPeriod (globalCandidateAMetricBySector period hPeriod data))

theorem candidateAFPCanonicalMinimal_graph :
    (candidateAFPCanonicalMinimal period hPeriod data).graph =
      CanonicalPairedFPGraph period hPeriod (globalCandidateAMetricBySector period hPeriod data) :=
  closedFeatureOperator_graph _ _ (candidateAPairedFPGraph_input_injective period hPeriod data)

theorem candidateAFPCanonicalMinimal_isClosed :
    (candidateAFPCanonicalMinimal period hPeriod data).IsClosed :=
  closedFeatureOperator_isClosed _ _ (candidateAPairedFPGraph_input_injective period hPeriod data)

theorem candidateAFPCanonicalMinimal_dense_domain :
    Dense ((candidateAFPCanonicalMinimal period hPeriod data).domain :
      Set (GlobalPairedGaugeLieL2 period hPeriod)) :=
  closedFeatureOperator_dense_domain _ _ (globalPairedGaugeLieL2LinearMap_denseRange period hPeriod)

theorem candidateAFPCanonicalMinimal_smooth_mem
    (field : GlobalPairedGaugeLieSmooth period hPeriod) :
    globalPairedGaugeLieL2LinearMap period hPeriod field ∈
      (candidateAFPCanonicalMinimal period hPeriod data).domain :=
  closedFeatureOperator_smooth_mem _ _ field

theorem candidateAFPCanonicalMinimal_smooth_apply
    (field : GlobalPairedGaugeLieSmooth period hPeriod) :
    candidateAFPCanonicalMinimal period hPeriod data
      ⟨globalPairedGaugeLieL2LinearMap period hPeriod field,
        candidateAFPCanonicalMinimal_smooth_mem period hPeriod data field⟩ =
      globalPairedAbelianFPL2LinearMap period hPeriod
        (globalCandidateAMetricBySector period hPeriod data) field :=
  closedFeatureOperator_smooth_apply _ _ (candidateAPairedFPGraph_input_injective period hPeriod data) field

/-- No smaller closed L2 extension can contain the actual smooth FP action. -/
theorem candidateAFPCanonicalMinimal_le_closed_extension
    (extension : GlobalPairedGaugeLieL2 period hPeriod →ₗ.[Real] GlobalPairedGaugeLieL2 period hPeriod)
    (hClosed : extension.IsClosed)
    (hExtends : ∀ field, (globalPairedGaugeLieL2LinearMap period hPeriod field,
      globalPairedAbelianFPL2LinearMap period hPeriod
        (globalCandidateAMetricBySector period hPeriod data) field) ∈ extension.graph) :
    candidateAFPCanonicalMinimal period hPeriod data ≤ extension :=
  closedFeatureOperator_minimal _ _ (candidateAPairedFPGraph_input_injective period hPeriod data)
    extension hClosed hExtends

/-- A smooth a priori estimate suffices for both analytic properties of the minimal actual FP.
The estimate remains an explicit obligation; no spectral or ellipticity hypothesis is inserted. -/
theorem candidateAFPCanonicalMinimal_finite_observation
    {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F] [FiniteDimensional Real F]
    (observation : GlobalPairedGaugeLieL2 period hPeriod →L[Real] F) (C : NNReal)
    (hEstimate : ∀ field : GlobalPairedGaugeLieSmooth period hPeriod,
      ‖globalPairedGaugeLieL2LinearMap period hPeriod field‖ ≤ C *
        (‖globalPairedAbelianFPL2LinearMap period hPeriod
          (globalCandidateAMetricBySector period hPeriod data) field‖ +
          ‖observation (globalPairedGaugeLieL2LinearMap period hPeriod field)‖)) :
    IsClosed (LinearMap.range (candidateAFPCanonicalMinimal period hPeriod data).toFun :
      Set (GlobalPairedGaugeLieL2 period hPeriod)) ∧
    FiniteDimensional Real (LinearMap.ker (candidateAFPCanonicalMinimal period hPeriod data).toFun) :=
  P0EFTJanusProgramPT12GraphClosureEstimate4D.closedFeatureOperator_finite_observation _ _
    (candidateAPairedFPGraph_input_injective period hPeriod data) observation C hEstimate

open P0EFTJanusProgramPT12NormalGraphResolvent4D

/-- Auxiliary normal resolvent of the installed FP; no change to the FP action or domain. -/
def candidateAFPNormalResolvent : GlobalPairedGaugeLieL2 period hPeriod →L[Real]
    GlobalPairedGaugeLieL2 period hPeriod :=
  normalResolvent (candidateAFPCanonicalMinimal period hPeriod data)
    (candidateAFPCanonicalMinimal_isClosed period hPeriod data)

theorem candidateAFPNormalResolvent_opNorm_le : ‖candidateAFPNormalResolvent period hPeriod data‖ ≤ 1 :=
  normalResolvent_opNorm_le _ (candidateAFPCanonicalMinimal_isClosed period hPeriod data)

theorem candidateAFPNormalResolvent_selfAdjoint : IsSelfAdjoint (candidateAFPNormalResolvent period hPeriod data) :=
  normalResolvent_selfAdjoint _ (candidateAFPCanonicalMinimal_isClosed period hPeriod data)

theorem candidateAFPNormalResolvent_nonnegative (f : GlobalPairedGaugeLieL2 period hPeriod) :
    0 ≤ inner Real f (candidateAFPNormalResolvent period hPeriod data f) :=
  normalResolvent_nonnegative _ (candidateAFPCanonicalMinimal_isClosed period hPeriod data) f

theorem candidateAFPNormalResolvent_solves (f : GlobalPairedGaugeLieL2 period hPeriod) :
    ∃ (u : (candidateAFPCanonicalMinimal period hPeriod data).domain)
      (hImage : candidateAFPCanonicalMinimal period hPeriod data u ∈
        (candidateAFPCanonicalMinimal period hPeriod data).adjoint.domain),
      u.val = candidateAFPNormalResolvent period hPeriod data f ∧
      u.val + (candidateAFPCanonicalMinimal period hPeriod data).adjoint
        ⟨candidateAFPCanonicalMinimal period hPeriod data u, hImage⟩ = f ∧
      ‖u.val‖ ≤ ‖f‖ ∧ 2 * ‖candidateAFPCanonicalMinimal period hPeriod data u‖ ≤ ‖f‖ := by
  let A := candidateAFPCanonicalMinimal period hPeriod data
  let hClosed := candidateAFPCanonicalMinimal_isClosed period hPeriod data
  let u : A.domain := ⟨normalResolvent A hClosed f, normalResolvent_mem_domain A hClosed f⟩
  have hImage : A u ∈ A.adjoint.domain := by
    rw [normalResolvent_apply]
    exact normalResolventImage_mem_adjoint_domain A hClosed f
  refine ⟨u, hImage, rfl, ?_, normalResolvent_norm_le A hClosed f, ?_⟩
  · change u.val + A.adjoint ⟨A u, hImage⟩ = f
    simpa only [u, normalResolvent_apply] using
      normalResolvent_equation A hClosed (candidateAFPCanonicalMinimal_dense_domain period hPeriod data) f
  · rw [normalResolvent_apply]
    exact normalResolventImage_norm_le_half A hClosed f

theorem candidateAFPNormalResolvent_unique (f : GlobalPairedGaugeLieL2 period hPeriod)
    (u : (candidateAFPCanonicalMinimal period hPeriod data).domain)
    (hImage : candidateAFPCanonicalMinimal period hPeriod data u ∈
      (candidateAFPCanonicalMinimal period hPeriod data).adjoint.domain)
    (hEquation : u.val + (candidateAFPCanonicalMinimal period hPeriod data).adjoint
      ⟨candidateAFPCanonicalMinimal period hPeriod data u, hImage⟩ = f) :
    u.val = candidateAFPNormalResolvent period hPeriod data f :=
  normalResolvent_unique _ (candidateAFPCanonicalMinimal_isClosed period hPeriod data)
    (candidateAFPCanonicalMinimal_dense_domain period hPeriod data) f u hImage hEquation

theorem candidateAFPNormalResolvent_fixed_iff_null (u : GlobalPairedGaugeLieL2 period hPeriod) :
    candidateAFPNormalResolvent period hPeriod data u = u ↔
      (u, 0) ∈ (candidateAFPCanonicalMinimal period hPeriod data).graph :=
  normalResolvent_fixed_iff_null _ (candidateAFPCanonicalMinimal_isClosed period hPeriod data) u

open P0EFTJanusProgramPT12MinimalNormInverse4D

/-- The actual unshifted FP inverse on its range, with minimum-norm output. -/
def candidateAFPMinimalInverse :
    GlobalPairedGaugeLieL2 period hPeriod →ₗ.[Real] GlobalPairedGaugeLieL2 period hPeriod :=
  minimalNormInverse (candidateAFPCanonicalMinimal period hPeriod data)

theorem candidateAFPMinimalInverse_isClosed :
    (candidateAFPMinimalInverse period hPeriod data).IsClosed :=
  minimalNormInverse_isClosed _ (candidateAFPCanonicalMinimal_isClosed period hPeriod data)

theorem candidateAFPMinimalInverse_domain :
    (candidateAFPMinimalInverse period hPeriod data).domain =
      LinearMap.range (candidateAFPCanonicalMinimal period hPeriod data).toFun :=
  minimalNormInverse_domain _ (candidateAFPCanonicalMinimal_isClosed period hPeriod data)

theorem candidateAFPMinimalInverse_solves
    (rhs : (candidateAFPMinimalInverse period hPeriod data).domain) :
    ∃ u : (candidateAFPCanonicalMinimal period hPeriod data).domain,
      candidateAFPCanonicalMinimal period hPeriod data u = rhs.val ∧
      u.val = candidateAFPMinimalInverse period hPeriod data rhs ∧
      ∀ v : (candidateAFPCanonicalMinimal period hPeriod data).domain,
        candidateAFPCanonicalMinimal period hPeriod data v = rhs.val → ‖u.val‖ ≤ ‖v.val‖ := by
  have hGraph := (minimalNormInverse_solves (candidateAFPCanonicalMinimal period hPeriod data) rhs).1
  let u : (candidateAFPCanonicalMinimal period hPeriod data).domain :=
    ⟨candidateAFPMinimalInverse period hPeriod data rhs, LinearPMap.mem_domain_of_mem_graph hGraph⟩
  refine ⟨u, ?_, rfl, ?_⟩
  · exact (candidateAFPCanonicalMinimal period hPeriod data).mem_graph_snd_inj
      ((candidateAFPCanonicalMinimal period hPeriod data).mem_graph u) hGraph rfl
  · intro v hv
    exact minimalNormInverse_norm_le_solution _
      (candidateAFPCanonicalMinimal_isClosed period hPeriod data) rhs v hv

end
end P0EFTJanusProgramPT12CandidateAFPCanonicalClosed4D
end JanusFormal
