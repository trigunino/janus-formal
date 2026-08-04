import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPrimitiveSpinCGeometricSignedFredholm4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalFullLLOnShellFredholmReduction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalAbelianFaddeevPopovGreenStokes4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalAbelianFaddeevPopovLagrangianSelfAdjoint4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalGeneralMetricDeDonderGraphCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalAbelianLorenzGraphRiesz4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarSmoothApproximation4D

/-!
# Common analytic domain for the global Candidate-A Hessian

This is the sole P3 assembly file of `HESSIAN-GLOBAL-01`.  It reuses the
existing D10-free common domain and the existing diagonal graph realization;
it does not introduce another completion.

The bounded same-action Riesz operator is already self-adjoint and closed on
that complete graph Hilbert space.  The smooth typed core is dense and
injective.  SpinC is closed/Fredholm and the stationary LL quotient is
Fredholm of index zero.

The remaining differential frontier is deliberately not hidden in a data
field: the projections of the completed de Donder/Lorenz/Faddeev--Popov
feature graphs must still be proved single-valued.  The intrinsic Abelian FP
part is already reduced to the existing scalar Green datum by the imported
Green-core adapter.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateACommonAnalyticDomainClosure4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 2400000

noncomputable section

open Set Topology
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D
open P0EFTJanusProgramPPrimitiveSpinCGeometricSignedFredholm4D
open P0EFTJanusProgramPGlobalFullLLOnShellFredholmReduction4D
open P0EFTJanusProgramPGlobalAbelianFaddeevPopovGreenStokes4D
open P0EFTJanusProgramPGlobalAbelianFaddeevPopovLagrangianSelfAdjoint4D
open P0EFTJanusProgramPGlobalGeneralMetricDeDonderGraphCore4D
open P0EFTJanusProgramPGlobalAbelianLorenzGraphRiesz4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarSmoothApproximation4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveWeightedTransportedGlobalGreen4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszL2OperatorGraphMinimalProgramPClosure4D
open P0EFTJanusMappingTorusGlobalLLVariation4D

variable (period : Real) (hPeriod : period ≠ 0)

local instance commonAnalyticDomainL2NormedAddCommGroup
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    NormedAddCommGroup
      (GlobalCandidateADiagonalExtendedBulkL2Hilbert period hPeriod metric
        couplings.matterMassSquared data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkNormedAddCommGroup
    period hPeriod metric couplings.matterMassSquared data analysis

local instance commonAnalyticDomainL2InnerProductSpace
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    InnerProductSpace Real
      (GlobalCandidateADiagonalExtendedBulkL2Hilbert period hPeriod metric
        couplings.matterMassSquared data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkInnerProductSpace
    period hPeriod metric couplings.matterMassSquared data analysis

local instance commonAnalyticDomainL2NormedSpace
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    NormedSpace Real
      (GlobalCandidateADiagonalExtendedBulkL2Hilbert period hPeriod metric
        couplings.matterMassSquared data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkNormedSpace
    period hPeriod metric couplings.matterMassSquared data analysis

local instance commonAnalyticDomainL2Module
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    Module Real
      (GlobalCandidateADiagonalExtendedBulkL2Hilbert period hPeriod metric
        couplings.matterMassSquared data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkModule
    period hPeriod metric couplings.matterMassSquared data analysis

private theorem continuousLinearMap_graph_isClosed
    {H : Type*} [NormedAddCommGroup H] [NormedSpace Real H]
    (operator : H →L[Real] H) :
    IsClosed (operator.toLinearMap.graph : Set (H × H)) := by
  rw [show (operator.toLinearMap.graph : Set (H × H)) =
      {pair | pair.2 = operator pair.1} by
    ext pair
    rfl]
  exact isClosed_eq continuous_snd (operator.continuous.comp continuous_fst)

/-! ## Existing rectangular graphs from a dense formal-adjoint core -/

universe u v w x z

/-- Interface over an already constructed graph completion.  It creates no
new graph space: the dense embedding and both projections are supplied by the
existing de Donder/Lorenz realizations. -/
structure ExistingRectangularHilbertGraph
    (Core : Type u) (Graph : Type v) (Source : Type w) (Target : Type x)
    [AddCommGroup Core] [Module Real Core]
    [NormedAddCommGroup Graph] [NormedSpace Real Graph]
    [NormedAddCommGroup Source] [InnerProductSpace Real Source]
    [NormedAddCommGroup Target] [InnerProductSpace Real Target] where
  inclusion : Core →ₗ[Real] Source
  operator : Core →ₗ[Real] Target
  smoothEmbedding : Core →ₗ[Real] Graph
  smoothEmbedding_dense : DenseRange smoothEmbedding
  baseProjection : Graph →L[Real] Source
  featureProjection : Graph →L[Real] Target
  baseProjection_smooth : ∀ field,
    baseProjection (smoothEmbedding field) = inclusion field
  featureProjection_smooth : ∀ field,
    featureProjection (smoothEmbedding field) = operator field
  jointProjection_injective : Function.Injective
    (fun field => (baseProjection field, featureProjection field))

namespace ExistingRectangularHilbertGraph

variable {Core : Type u} {Graph : Type v} {Source : Type w} {Target : Type x}
  [AddCommGroup Core] [Module Real Core]
  [NormedAddCommGroup Graph] [NormedSpace Real Graph]
  [NormedAddCommGroup Source] [InnerProductSpace Real Source]
  [NormedAddCommGroup Target] [InnerProductSpace Real Target]

/-- A dense target test core carrying the actual formal adjoint. -/
structure DenseFormalAdjointCore
    (data : ExistingRectangularHilbertGraph Core Graph Source Target)
    (TestCore : Type z) [AddCommGroup TestCore] [Module Real TestCore] where
  inclusion : TestCore →ₗ[Real] Target
  formalAdjoint : TestCore →ₗ[Real] Source
  dense : DenseRange inclusion
  pairing : ∀ field : Core, ∀ test : TestCore,
    inner Real (data.operator field) (inclusion test) =
      inner Real (data.inclusion field) (formalAdjoint test)

namespace DenseFormalAdjointCore

variable {TestCore : Type z} [AddCommGroup TestCore] [Module Real TestCore]
  {data : ExistingRectangularHilbertGraph Core Graph Source Target}

/-- The formal-adjoint identity extends from the algebraic graph to its
existing topological completion. -/
theorem completedGraph_pairing
    (testCore : DenseFormalAdjointCore data TestCore)
    (graphField : Graph) (test : TestCore) :
    inner Real (data.featureProjection graphField) (testCore.inclusion test) =
      inner Real (data.baseProjection graphField)
        (testCore.formalAdjoint test) := by
  let good : Set Graph :=
    {field |
      inner Real (data.featureProjection field) (testCore.inclusion test) =
        inner Real (data.baseProjection field) (testCore.formalAdjoint test)}
  have hGoodClosed : IsClosed good := by
    dsimp [good]
    apply isClosed_eq <;> fun_prop
  have hCore : Set.range data.smoothEmbedding ⊆ good := by
    rintro field ⟨smoothField, rfl⟩
    change
      inner Real (data.featureProjection (data.smoothEmbedding smoothField))
          (testCore.inclusion test) =
        inner Real (data.baseProjection (data.smoothEmbedding smoothField))
          (testCore.formalAdjoint test)
    simpa only [data.featureProjection_smooth,
      data.baseProjection_smooth] using testCore.pairing smoothField test
  have hClosure : closure (Set.range data.smoothEmbedding) = Set.univ :=
    data.smoothEmbedding_dense.closure_range
  have hGraphMem : graphField ∈ closure (Set.range data.smoothEmbedding) := by
    rw [hClosure]
    trivial
  exact (closure_minimal hCore hGoodClosed) hGraphMem

/-- A vertical vector in the completed rectangular graph has zero feature. -/
theorem feature_eq_zero_of_base_eq_zero
    (testCore : DenseFormalAdjointCore data TestCore)
    (graphField : Graph)
    (hVertical : data.baseProjection graphField = 0) :
    data.featureProjection graphField = 0 := by
  let residual : Target := data.featureProjection graphField
  have hTestOrthogonal (test : TestCore) :
      inner Real residual (testCore.inclusion test) = 0 := by
    have hPairing := testCore.completedGraph_pairing graphField test
    rw [hVertical] at hPairing
    simpa [residual] using hPairing
  let good : Set Target := {test | inner Real residual test = 0}
  have hGoodClosed : IsClosed good := by
    dsimp [good]
    apply isClosed_eq <;> fun_prop
  have hRange : Set.range testCore.inclusion ⊆ good := by
    rintro test ⟨smoothTest, rfl⟩
    exact hTestOrthogonal smoothTest
  have hClosure : closure (Set.range testCore.inclusion) = Set.univ :=
    testCore.dense.closure_range
  have hResidualMem : residual ∈ closure (Set.range testCore.inclusion) := by
    rw [hClosure]
    trivial
  have hResidualOrthogonal : inner Real residual residual = 0 :=
    (closure_minimal hRange hGoodClosed) hResidualMem
  have hNormSq : ‖residual‖ ^ 2 = 0 := by
    simpa [real_inner_self_eq_norm_sq] using hResidualOrthogonal
  have hNorm : ‖residual‖ = 0 := by
    nlinarith [sq_nonneg ‖residual‖]
  exact norm_eq_zero.mp hNorm

/-- A dense formal-adjoint core proves that the existing graph projection is
injective. -/
theorem baseProjection_injective
    (testCore : DenseFormalAdjointCore data TestCore) :
    Function.Injective data.baseProjection := by
  intro first second hBase
  have hDifferenceBase : data.baseProjection (first - second) = 0 := by
    rw [map_sub, hBase, sub_self]
  have hDifferenceFeature : data.featureProjection (first - second) = 0 :=
    testCore.feature_eq_zero_of_base_eq_zero (first - second) hDifferenceBase
  have hFeature : data.featureProjection first =
      data.featureProjection second := by
    simpa only [map_sub, sub_eq_zero] using hDifferenceFeature
  exact data.jointProjection_injective (Prod.ext hBase hFeature)

end DenseFormalAdjointCore
end ExistingRectangularHilbertGraph

/-! ## Canonical dense scalar test packets -/

/-- Independent smooth scalar tests for every de Donder output coordinate.
This is only a test core for the existing graph target. -/
abbrev GlobalGeneralMetricDeDonderAdjointTestCore :=
  GlobalGeneralMetricDeDonderFrameIndex period hPeriod →
    SmoothQuotientField period hPeriod Real

/-- Coordinatewise inclusion of the de Donder test packet into the existing
physical `L²` target. -/
def globalGeneralMetricDeDonderAdjointTestInclusion :
    GlobalGeneralMetricDeDonderAdjointTestCore period hPeriod →ₗ[Real]
      GlobalGeneralMetricDeDonderFrameL2 period hPeriod where
  toFun test := WithLp.toLp 2 fun index =>
    smoothToCanonicalPhysicalBulkL2 period hPeriod (test index)
  map_add' first second := by
    apply PiLp.ext
    intro index
    exact (smoothToCanonicalPhysicalBulkL2 period hPeriod).map_add
      (first index) (second index)
  map_smul' scalar test := by
    apply PiLp.ext
    intro index
    exact (smoothToCanonicalPhysicalBulkL2 period hPeriod).map_smul
      scalar (test index)

/-- Smooth scalar packets are dense in the full finite de Donder coordinate
target. -/
theorem globalGeneralMetricDeDonderAdjointTestInclusion_denseRange :
    DenseRange
      (globalGeneralMetricDeDonderAdjointTestInclusion period hPeriod) := by
  let coordinateEquiv := PiLp.continuousLinearEquiv 2 Real
    (fun _ : GlobalGeneralMetricDeDonderFrameIndex period hPeriod =>
      CanonicalPhysicalBulkL2 period hPeriod)
  have hPi : DenseRange (Pi.map fun _ :
      GlobalGeneralMetricDeDonderFrameIndex period hPeriod =>
        smoothToCanonicalPhysicalBulkL2 period hPeriod) :=
    DenseRange.piMap fun _ =>
      smoothToCanonicalPhysicalBulkL2_denseRange period hPeriod
  have hCoordinates : DenseRange (coordinateEquiv ∘
      globalGeneralMetricDeDonderAdjointTestInclusion period hPeriod) := by
    change DenseRange (Pi.map fun _ :
      GlobalGeneralMetricDeDonderFrameIndex period hPeriod =>
        smoothToCanonicalPhysicalBulkL2 period hPeriod)
    exact hPi
  have hBack :=
    (coordinateEquiv.symm.surjective.denseRange).comp
      hCoordinates coordinateEquiv.symm.continuous
  simpa [coordinateEquiv, Function.comp_def] using hBack

/-- Independent smooth scalar tests for every paired Lorenz output
coordinate. -/
abbrev GlobalPairedAbelianLorenzAdjointTestCore :=
  GlobalPairedAbelianLorenzCoordinateIndex →
    SmoothQuotientField period hPeriod Real

/-- Coordinatewise inclusion of the paired Lorenz test packet into the
existing physical `L²` target. -/
def globalPairedAbelianLorenzAdjointTestInclusion :
    GlobalPairedAbelianLorenzAdjointTestCore period hPeriod →ₗ[Real]
      GlobalPairedAbelianLorenzL2 period hPeriod where
  toFun test := WithLp.toLp 2 fun index =>
    smoothToCanonicalPhysicalBulkL2 period hPeriod (test index)
  map_add' first second := by
    apply PiLp.ext
    intro index
    exact (smoothToCanonicalPhysicalBulkL2 period hPeriod).map_add
      (first index) (second index)
  map_smul' scalar test := by
    apply PiLp.ext
    intro index
    exact (smoothToCanonicalPhysicalBulkL2 period hPeriod).map_smul
      scalar (test index)

/-- Smooth scalar packets are dense in the full finite paired Lorenz
coordinate target. -/
theorem globalPairedAbelianLorenzAdjointTestInclusion_denseRange :
    DenseRange
      (globalPairedAbelianLorenzAdjointTestInclusion period hPeriod) := by
  let coordinateEquiv := PiLp.continuousLinearEquiv 2 Real
    (fun _ : GlobalPairedAbelianLorenzCoordinateIndex =>
      CanonicalPhysicalBulkL2 period hPeriod)
  have hPi : DenseRange (Pi.map fun _ :
      GlobalPairedAbelianLorenzCoordinateIndex =>
        smoothToCanonicalPhysicalBulkL2 period hPeriod) :=
    DenseRange.piMap fun _ =>
      smoothToCanonicalPhysicalBulkL2_denseRange period hPeriod
  have hCoordinates : DenseRange (coordinateEquiv ∘
      globalPairedAbelianLorenzAdjointTestInclusion period hPeriod) := by
    change DenseRange (Pi.map fun _ :
      GlobalPairedAbelianLorenzCoordinateIndex =>
        smoothToCanonicalPhysicalBulkL2 period hPeriod)
    exact hPi
  have hBack :=
    (coordinateEquiv.symm.surjective.denseRange).comp
      hCoordinates coordinateEquiv.symm.continuous
  simpa [coordinateEquiv, Function.comp_def] using hBack

/-! ### Adapters for the two existing differential completions -/

/-- First projection of the already existing de Donder graph. -/
def globalGeneralMetricDeDonderBaseProjection
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    GlobalGeneralMetricDeDonderGraphHilbert period hPeriod metric →L[Real]
      GlobalGeneralMetricTensorFrameL2 period hPeriod :=
  (WithLp.fstL 2 Real
      (GlobalGeneralMetricTensorFrameL2 period hPeriod)
      (GlobalGeneralMetricDeDonderFrameL2 period hPeriod)).comp
    (globalGeneralMetricDeDonderGraphSubmodule
      period hPeriod metric).subtypeL

/-- The common closability interface uses the existing de Donder graph, not a
new completion. -/
def globalGeneralMetricDeDonderExistingGraph
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    ExistingRectangularHilbertGraph
      (SmoothSymmetricCovariantTwoTensor period hPeriod)
      (GlobalGeneralMetricDeDonderGraphHilbert period hPeriod metric)
      (GlobalGeneralMetricTensorFrameL2 period hPeriod)
      (GlobalGeneralMetricDeDonderFrameL2 period hPeriod) where
  inclusion := globalGeneralMetricTensorFrameL2LinearMap period hPeriod
  operator := globalGeneralMetricDeDonderFrameL2LinearMap
    period hPeriod metric
  smoothEmbedding := globalGeneralMetricDeDonderSmoothEmbedding
    period hPeriod metric
  smoothEmbedding_dense :=
    globalGeneralMetricDeDonderSmoothEmbedding_denseRange
      period hPeriod metric
  baseProjection := globalGeneralMetricDeDonderBaseProjection
    period hPeriod metric
  featureProjection := globalGeneralMetricDeDonderFeatureProjection
    period hPeriod metric
  baseProjection_smooth := fun _ => rfl
  featureProjection_smooth := fun _ => rfl
  jointProjection_injective := by
    intro first second hEqual
    apply Subtype.ext
    apply WithLp.ofLp_injective 2
    apply Prod.ext
    · exact congrArg Prod.fst hEqual
    · exact congrArg Prod.snd hEqual

/-- A genuine dense formal-adjoint core makes the existing de Donder graph
single-valued. -/
theorem globalGeneralMetricDeDonderBaseProjection_injective_of_adjointCore
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    {TestCore : Type*} [AddCommGroup TestCore] [Module Real TestCore]
    (testCore : ExistingRectangularHilbertGraph.DenseFormalAdjointCore
      (globalGeneralMetricDeDonderExistingGraph period hPeriod metric)
      TestCore) :
    Function.Injective
      (globalGeneralMetricDeDonderBaseProjection period hPeriod metric) :=
  testCore.baseProjection_injective

/-- First projection of the already existing paired Lorenz graph. -/
def globalPairedAbelianLorenzBaseProjection
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    GlobalPairedAbelianLorenzGraphHilbert period hPeriod metric →L[Real]
      GlobalPairedAbelianPotentialL2 period hPeriod :=
  (WithLp.fstL 2 Real
      (GlobalPairedAbelianPotentialL2 period hPeriod)
      (GlobalPairedAbelianLorenzL2 period hPeriod)).comp
    (globalPairedAbelianLorenzGraphSubmodule
      period hPeriod metric).subtypeL

/-- The common closability interface uses the existing paired Lorenz graph. -/
def globalPairedAbelianLorenzExistingGraph
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    ExistingRectangularHilbertGraph
      (GlobalPairedAbelianPotentialSmooth period hPeriod)
      (GlobalPairedAbelianLorenzGraphHilbert period hPeriod metric)
      (GlobalPairedAbelianPotentialL2 period hPeriod)
      (GlobalPairedAbelianLorenzL2 period hPeriod) where
  inclusion := globalPairedAbelianPotentialL2LinearMap period hPeriod
  operator := globalPairedAbelianLorenzL2LinearMap period hPeriod metric
  smoothEmbedding := globalPairedAbelianLorenzSmoothEmbedding
    period hPeriod metric
  smoothEmbedding_dense :=
    globalPairedAbelianLorenzSmoothEmbedding_denseRange
      period hPeriod metric
  baseProjection := globalPairedAbelianLorenzBaseProjection
    period hPeriod metric
  featureProjection := globalPairedAbelianLorenzFeatureProjection
    period hPeriod metric
  baseProjection_smooth := fun _ => rfl
  featureProjection_smooth := fun _ => rfl
  jointProjection_injective := by
    intro first second hEqual
    apply Subtype.ext
    apply WithLp.ofLp_injective 2
    apply Prod.ext
    · exact congrArg Prod.fst hEqual
    · exact congrArg Prod.snd hEqual

/-- A genuine dense formal-adjoint core makes the existing paired Lorenz
graph single-valued. -/
theorem globalPairedAbelianLorenzBaseProjection_injective_of_adjointCore
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    {TestCore : Type*} [AddCommGroup TestCore] [Module Real TestCore]
    (testCore : ExistingRectangularHilbertGraph.DenseFormalAdjointCore
      (globalPairedAbelianLorenzExistingGraph period hPeriod metric)
      TestCore) :
    Function.Injective
      (globalPairedAbelianLorenzBaseProjection period hPeriod metric) :=
  testCore.baseProjection_injective

/-! ## Unconditional common-domain spine -/

/-- The physical common domain is closed, inhabited and contains no D10
coordinate. -/
theorem globalCandidateACommonAnalyticDomain_physical_certificate
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    GlobalPhysicalAnalysisCertificate period hPeriod analysis :=
  globalPhysicalAnalysisCertificate period hPeriod analysis

/-- The exact smooth core of the existing diagonal realization is both dense
and injective. -/
theorem globalCandidateACommonAnalyticDomain_core_certificate
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    DenseRange
        (diagonalExtendedBulkL2SmoothEmbedding period hPeriod metric
          couplings.matterMassSquared data analysis) ∧
      Function.Injective
        (diagonalExtendedBulkL2SmoothEmbedding period hPeriod metric
          couplings.matterMassSquared data analysis) :=
  ⟨diagonalExtendedBulkL2SmoothEmbedding_denseRange period hPeriod metric
      couplings.matterMassSquared data analysis,
    diagonalExtendedBulkL2SmoothEmbedding_injective period hPeriod metric
      couplings.matterMassSquared data analysis⟩

/-- The existing bounded representative of the exact same-action Hessian is
self-adjoint on the complete diagonal graph Hilbert space. -/
def globalCandidateACommonAnalyticDomain_riesz_isSelfAdjoint
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :=
  diagonalExtendedBulkL2RieszOperator_isSelfAdjoint period hPeriod metric
    couplings.matterMassSquared data analysis

/-- The graph of the bounded same-action Riesz representative is closed. -/
theorem globalCandidateACommonAnalyticDomain_riesz_graph_isClosed
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    IsClosed
      ((diagonalExtendedBulkL2RieszOperator period hPeriod metric
          couplings.matterMassSquared data analysis).toLinearMap.graph :
        Set
          (GlobalCandidateADiagonalExtendedBulkL2Hilbert period hPeriod metric
              couplings.matterMassSquared data analysis ×
            GlobalCandidateADiagonalExtendedBulkL2Hilbert period hPeriod metric
              couplings.matterMassSquared data analysis)) := by
  exact @continuousLinearMap_graph_isClosed
    (GlobalCandidateADiagonalExtendedBulkL2Hilbert period hPeriod metric
      couplings.matterMassSquared data analysis)
    (commonAnalyticDomainL2NormedAddCommGroup period hPeriod metric data analysis)
    (commonAnalyticDomainL2NormedSpace period hPeriod metric data analysis)
    (diagonalExtendedBulkL2RieszOperator period hPeriod metric
      couplings.matterMassSquared data analysis)

/-- Existing primitive signed SpinC Fredholm block. -/
def globalCandidateACommonAnalyticDomain_spinC_fredholm
    (mass : Real) :=
  primitiveSpinCGeometricSignedMassRealOperator_fredholm
    period hPeriod mass

/-- Existing stationary LL quotient Fredholm block. -/
def globalCandidateACommonAnalyticDomain_ll_fredholm_of_stationary
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (hStationary : ∀ point,
      LLStationaryAt period hPeriod
        (data.boundary.llFields period hPeriod) point) :=
  globalCandidateAFullLLFieldQuotientRieszOperator_fredholm_criterion_of_stationary
    period hPeriod data analysis hStationary

/-- The same stationary LL quotient has index zero. -/
def globalCandidateACommonAnalyticDomain_ll_index_zero_of_stationary
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (hStationary : ∀ point,
      LLStationaryAt period hPeriod
        (data.boundary.llFields period hPeriod) point) :=
  globalCandidateAFullLLFieldQuotientRieszIndex_zero_of_stationary
    period hPeriod data analysis hStationary

/-! ## Exact differential frontier -/

/-- Intrinsic Abelian FP closability is already generated by the scalar Green
datum; no separate FP closability premise is needed. -/
def globalCandidateACommonAnalyticDomain_intrinsicAbelianFP_closable
    (green : CanonicalPhysicalScalarIntrinsicWaveGlobalGreenStokesData
      period hPeriod 0) :=
  intrinsicAbelianFaddeevPopovScalarGreenCore_closable_certificate
    period hPeriod green

/-- The sharp existing Program-P analytic endpoint supplies the same FP
closability certificate without adding a second Green datum. -/
def globalCandidateACommonAnalyticDomain_intrinsicAbelianFP_closable_of_graphMinimalAnalytic
    (analytic :
      CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszL2OperatorGraphDirectCoerciveMinimalAnalyticData
        period hPeriod 0) :=
  globalCandidateACommonAnalyticDomain_intrinsicAbelianFP_closable
    period hPeriod
      (intrinsicAbelianFPGraphMinimalGreen period hPeriod analytic)

/-- The same pre-existing endpoint also gives the actual adjoint-domain
equality and the exact smooth-core FP operator identification. -/
def globalCandidateACommonAnalyticDomain_intrinsicAbelianFP_selfAdjoint_of_graphMinimalAnalytic
    (analytic :
      CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszL2OperatorGraphDirectCoerciveMinimalAnalyticData
        period hPeriod 0) :=
  intrinsicAbelianFPGraphMinimal_selfAdjoint_certificate
    period hPeriod analytic

/-- The unrestricted intrinsic Abelian FP frontier is exactly the already
named scalar off-shell Stokes identity. -/
theorem globalCandidateACommonAnalyticDomain_intrinsicAbelianFP_nonempty_iff
    : Nonempty
        (CanonicalPhysicalScalarIntrinsicWaveGlobalGreenStokesData
          period hPeriod 0) ↔
      ∀ field test :
          P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D.SmoothScalarField
            period hPeriod,
        (∫ point,
          P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerGreenL2Reduction4D.canonicalPhysicalScalarEulerSkewDensity
            period hPeriod 0 field test point
          ∂P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D.intrinsicCanonicalLorentzVolumeMeasure
            period hPeriod) =
        P0EFTJanusMappingTorusCutBulkGlobalOrientedBoundaryCurrent4D.cutBulkGlobalOrientedScalarCurrentIntegral
          period hPeriod field test :=
  CanonicalPhysicalScalarIntrinsicWaveGlobalGreenStokesData.nonempty_iff_eulerSkew_integral_eq_orientedBoundary
    period hPeriod

end
end P0EFTJanusProgramPGlobalCandidateACommonAnalyticDomainClosure4D
end JanusFormal
