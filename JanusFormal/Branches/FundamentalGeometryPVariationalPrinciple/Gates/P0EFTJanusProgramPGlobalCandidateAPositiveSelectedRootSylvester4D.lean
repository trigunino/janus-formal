import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameSylvesterRegularStratumLocalRoot4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPositiveRawSplitCharpolyContDiffLocalRootBranch4D

/-!
# Intrinsic Sylvester regularity of the positive selected Candidate-A root

The unqualified geometry stores an arbitrary smooth real square root.  This
gate isolates the actual physical branch condition: in the regular metric
basis already carried by the action data, the stored root is the existing
positive raw spectral selector.  Matrix Sylvester bijectivity then transports
through the basis equivalence to the intrinsic endomorphism bundle.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAPositiveSelectedRootSylvester4D

set_option autoImplicit false
set_option maxHeartbeats 10000000

noncomputable section

open scoped Manifold ContDiff Matrix.Norms.Frobenius
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusPositiveRawSplitCharpolyContDiffLocalRootBranch4D
open P0EFTJanusPositiveRawSplitCharpolySylvesterClosure4D
open P0EFTJanusPositiveRealJordanPresentationBridge4D
open P0EFTJanusProgramPGlobalCandidateAGeometry4D
open P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameCorner4D
open P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameCornerAlgebra4D
open P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameCornerLocalRoot4D
open P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameSylvesterRegularity4D
open P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameSylvesterCornerLocalRoot4D
open P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameSylvesterRegularStratumLocalRoot4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D

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

local instance effectiveTangentFiniteDimensional
    (point : EffectiveQuotient period hPeriod) :
    FiniteDimensional Real (TangentFiber period hPeriod point) := by
  change FiniteDimensional Real CoverCoordinates
  infer_instance

local instance effectiveTangentT2
    (point : EffectiveQuotient period hPeriod) :
    T2Space (TangentFiber period hPeriod point) := by
  change T2Space CoverCoordinates
  infer_instance

attribute [local instance]
  P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameSylvesterRegularStratumLocalRoot4D.strongFiniteFrameCornerNormedAddCommGroup
  P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameSylvesterRegularStratumLocalRoot4D.strongFiniteFrameCornerNormedSpace
  P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameSylvesterRegularStratumLocalRoot4D.strongFiniteFrameCornerCompleteSpaceInstance

/-! ## Basis transport for finite-dimensional endomorphisms -/

/-- Continuous endomorphisms and their `4 × 4` matrices are linearly
equivalent on every tangent fiber. -/
def candidateAEndomorphismMatrixEquiv
    {V : Type*} [AddCommGroup V] [Module Real V]
    [TopologicalSpace V] [IsTopologicalAddGroup V]
    [ContinuousSMul Real V] [T2Space V] [FiniteDimensional Real V]
    (basis : Module.Basis (Fin 4) Real V) :
    (V →L[Real] V) ≃ₗ[Real] Matrix (Fin 4) (Fin 4) Real :=
  (LinearMap.toContinuousLinearMap
      (𝕜 := Real) (E := V) (F' := V)).symm.trans
    (LinearMap.toMatrix basis basis)

theorem candidateAEndomorphismMatrixEquiv_comp
    {V : Type*} [AddCommGroup V] [Module Real V]
    [TopologicalSpace V] [IsTopologicalAddGroup V]
    [ContinuousSMul Real V] [T2Space V] [FiniteDimensional Real V]
    (basis : Module.Basis (Fin 4) Real V)
    (first second : V →L[Real] V) :
    candidateAEndomorphismMatrixEquiv basis (first.comp second) =
      candidateAEndomorphismMatrixEquiv basis first *
        candidateAEndomorphismMatrixEquiv basis second :=
  LinearMap.toMatrix_comp basis basis basis
    first.toLinearMap second.toLinearMap

/-- Matrix form of the intrinsic Sylvester map. -/
def candidateAMatrixSylvester
    (root : Matrix (Fin 4) (Fin 4) Real) :
    Matrix (Fin 4) (Fin 4) Real →ₗ[Real]
      Matrix (Fin 4) (Fin 4) Real where
  toFun variation := root * variation + variation * root
  map_add' first second := by
    simp [mul_add, add_mul, add_assoc, add_left_comm]
  map_smul' scalar variation := by simp

theorem candidateAMatrixSylvester_eq_canonical
    (root : Matrix (Fin 4) (Fin 4) Real) :
    candidateAMatrixSylvester root =
      (canonicalSylvesterOperator root).toLinearMap := by
  ext variation
  rfl

theorem candidateAEndomorphismMatrixEquiv_sylvester
    {V : Type*} [AddCommGroup V] [Module Real V]
    [TopologicalSpace V] [IsTopologicalAddGroup V]
    [ContinuousSMul Real V] [T2Space V] [FiniteDimensional Real V]
    (basis : Module.Basis (Fin 4) Real V)
    (root variation : V →L[Real] V) :
    candidateAEndomorphismMatrixEquiv basis
        (root.comp variation + variation.comp root) =
      candidateAMatrixSylvester
        (candidateAEndomorphismMatrixEquiv basis root)
        (candidateAEndomorphismMatrixEquiv basis variation) := by
  change candidateAEndomorphismMatrixEquiv basis
      (root.comp variation + variation.comp root) =
    candidateAEndomorphismMatrixEquiv basis root *
        candidateAEndomorphismMatrixEquiv basis variation +
      candidateAEndomorphismMatrixEquiv basis variation *
        candidateAEndomorphismMatrixEquiv basis root
  rw [map_add,
    candidateAEndomorphismMatrixEquiv_comp,
    candidateAEndomorphismMatrixEquiv_comp]

theorem intrinsicCandidateASylvesterAt_bijective_of_matrix
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (basis : Module.Basis (Fin 4) Real
      (TangentFiber period hPeriod point))
    (hMatrix : Function.Bijective
      (candidateAMatrixSylvester
        (geometry.rootMatrixAt period hPeriod point basis))) :
    Function.Bijective
      (intrinsicCandidateASylvesterAt period hPeriod geometry point) := by
  let encode := candidateAEndomorphismMatrixEquiv basis
  have hEncode (variation : TangentFiber period hPeriod point →L[Real]
      TangentFiber period hPeriod point) :
      encode
          (intrinsicCandidateASylvesterAt
            period hPeriod geometry point variation) =
        candidateAMatrixSylvester
          (geometry.rootMatrixAt period hPeriod point basis)
          (encode variation) := by
    exact candidateAEndomorphismMatrixEquiv_sylvester basis
      (geometry.rootAt point) variation
  constructor
  · intro first second hEqual
    apply encode.injective
    apply hMatrix.1
    rw [← hEncode, ← hEncode, hEqual]
  · intro target
    obtain ⟨matrix, hImage⟩ := hMatrix.2 (encode target)
    let source := encode.symm matrix
    refine ⟨source, ?_⟩
    apply encode.injective
    rw [hEncode]
    simp only [source, LinearEquiv.apply_symm_apply]
    exact hImage

/-! ## The physical positive-root selection certificate -/

/-- Matrix of the genuine relative endomorphism in the regular plus-metric
basis already present in the action data. -/
def globalCandidateARelativeMatrixAt
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (point : EffectiveQuotient period hPeriod) :
    Matrix (Fin 4) (Fin 4) Real :=
  LinearMap.toMatrix
    (regularMetricBasisAt period hPeriod data.plusGravity.metric point)
    (regularMetricBasisAt period hPeriod data.plusGravity.metric point)
    (relativeEndomorphismAt period hPeriod
      configuration.geometry.plusMetric
      configuration.geometry.minusMetric point).toLinearMap

/-- The selected physical branch: positive split relative spectrum and exact
agreement of the stored intrinsic root with the existing positive selector.
No Sylvester hypothesis is included. -/
structure GlobalCandidateAPositiveSelectedRootCertificate4D
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace) where
  positiveSpectrum : ∀ point,
    PositiveRealSplitCharpoly4
      (globalCandidateARelativeMatrixAt period hPeriod data point)
  selectedRoot : ∀ point,
    configuration.geometry.rootMatrixAt period hPeriod point
        (regularMetricBasisAt period hPeriod data.plusGravity.metric point) =
      positiveRawRegularRoot
        (globalCandidateARelativeMatrixAt period hPeriod data point)
        (positiveSpectrum point)

/-- The positive physical selector is intrinsically Sylvester-regular at
every spacetime point. -/
theorem GlobalCandidateAPositiveSelectedRootCertificate4D.intrinsicRegular
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace}
    (selection : GlobalCandidateAPositiveSelectedRootCertificate4D
      period hPeriod data) :
    IsGlobalCandidateASylvesterRegular period hPeriod
      configuration.geometry := by
  intro point
  apply intrinsicCandidateASylvesterAt_bijective_of_matrix
    period hPeriod configuration.geometry point
      (regularMetricBasisAt period hPeriod data.plusGravity.metric point)
  rw [selection.selectedRoot point]
  rw [candidateAMatrixSylvester_eq_canonical]
  exact canonicalPositiveRawSylvester_bijective
    (globalCandidateARelativeMatrixAt period hPeriod data point)
    (selection.positiveSpectrum point)

/-- Consequently the existing strong finite-frame local-root theorem applies
to the physically positive selected root, with no added regularity axiom. -/
theorem global_candidate_a_positive_selected_root_strong_local_gate
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace}
    (selection : GlobalCandidateAPositiveSelectedRootCertificate4D
      period hPeriod data)
    (frame : SmoothD8Frame period hPeriod) :
    Function.Bijective
        (strongFiniteFrameCornerSylvester
          period hPeriod frame configuration.geometry.plusMetric
          (strongGlobalCandidateAFiniteFrameRootCorner
            period hPeriod configuration.geometry frame)) ∧
      HasLocalC2InverseOpenBranch
        (StrongFiniteFrameCorner period hPeriod frame
          configuration.geometry.plusMetric)
        (strongFiniteFrameCornerSquare
          period hPeriod frame configuration.geometry.plusMetric)
        (strongGlobalCandidateAFiniteFrameRootCorner
          period hPeriod configuration.geometry frame) :=
  global_candidate_a_strong_finite_frame_sylvester_contDiff_local_root_gate
    period hPeriod configuration.geometry frame selection.intrinsicRegular

/-! ## Positive selection along an entire local action family -/

/-- A physical local chart selects the existing positive root at every
admissible parameter.  No separate Sylvester field is stored. -/
structure GlobalCandidateAPositiveSelectedLocalVariationalChart4D
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure) where
  selected : ∀ point (hPoint : point ∈ chart.family.domain),
    GlobalCandidateAPositiveSelectedRootCertificate4D period hPeriod
      (chart.family.datumAt point hPoint).2

/-- Positive selection makes the whole admissible chart intrinsically
Sylvester-regular. -/
theorem GlobalCandidateAPositiveSelectedLocalVariationalChart4D.sylvesterRegular
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    {chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure}
    (selection : GlobalCandidateAPositiveSelectedLocalVariationalChart4D
      period hPeriod chart) :
    IsGlobalCandidateALocalVariationalChartSylvesterRegular
      period hPeriod chart := by
  intro point hPoint
  exact (selection.selected point hPoint).intrinsicRegular

/-- Every admissible point of a positive-selected physical chart activates
the existing strong open-domain `C²` root branch. -/
theorem global_candidate_a_positive_selected_local_variational_chart_root_gate
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (selection : GlobalCandidateAPositiveSelectedLocalVariationalChart4D
      period hPeriod chart)
    (point : chart.Model) (hPoint : point ∈ chart.family.domain)
    (frame : SmoothD8Frame period hPeriod) :
    let geometry := ((chart.family.datumAt point hPoint).1).geometry
    Function.Bijective
        (strongFiniteFrameCornerSylvester
          period hPeriod frame geometry.plusMetric
          (strongGlobalCandidateAFiniteFrameRootCorner
            period hPeriod geometry frame)) ∧
      HasLocalC2InverseOpenBranch
        (StrongFiniteFrameCorner period hPeriod frame geometry.plusMetric)
        (strongFiniteFrameCornerSquare
          period hPeriod frame geometry.plusMetric)
        (strongGlobalCandidateAFiniteFrameRootCorner
          period hPeriod geometry frame) :=
  global_candidate_a_sylvester_regular_local_variational_chart_root_gate
    period hPeriod chart selection.sylvesterRegular point hPoint frame

end
end P0EFTJanusProgramPGlobalCandidateAPositiveSelectedRootSylvester4D
end JanusFormal
