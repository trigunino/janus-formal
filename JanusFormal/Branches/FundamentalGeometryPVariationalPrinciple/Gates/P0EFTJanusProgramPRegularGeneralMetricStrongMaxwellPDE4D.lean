import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricGlobalMaxwellDivergence4D

/-! # Pointwise strong Maxwell PDE in every holonomic chart -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricStrongMaxwellPDE4D

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 800000

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerAtlas4D
open P0EFTJanusMappingTorusGeneralMetricSymmetricTensorDivergence4D
open P0EFTJanusMappingTorusGeneralMetricSymmetricTensorDivergenceIntrinsic4D
open P0EFTJanusProgramPRegularGeneralMetricGlobalMaxwellDivergence4D

variable (period : Real) (hPeriod : period ≠ 0)

abbrev Index4 :=
  P0EFTJanusMappingTorusGeneralMetricSymmetricTensorDivergence4D.Index4

abbrev Vector4 :=
  P0EFTJanusMappingTorusGeneralMetricSymmetricTensorDivergence4D.Vector4

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveTangentFiniteDimensional
    (point : EffectiveQuotient period hPeriod) :
    FiniteDimensional Real
      (TangentSpace coverModelWithCorners point) := by
  change FiniteDimensional Real CoverCoordinates
  infer_instance

local instance effectiveTangentT2
    (point : EffectiveQuotient period hPeriod) :
    T2Space (TangentSpace coverModelWithCorners point) := by
  change T2Space CoverCoordinates
  infer_instance

/-- One coordinate component of `∇^μ F_μν`. -/
def regularLocalMaxwellDivergenceComponent
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) (index : Index4) : Real :=
  localSymmetricTensorDivergenceModelCovector period hPeriod metric.metric
    (regularGlobalGaugeCurvatureTensor period hPeriod metric potential
      component) patch coordinate (Pi.single index 1)

/-- A local intrinsic divergence covector vanishes exactly when its four
coordinate components vanish. -/
theorem regularLocalMaxwellDivergenceIntrinsic_eq_zero_iff
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    localSymmetricTensorDivergenceIntrinsicCovector period hPeriod
        metric.metric
        (regularGlobalGaugeCurvatureTensor period hPeriod metric potential
          component) patch coordinate = 0 ↔
      ∀ index : Index4,
        regularLocalMaxwellDivergenceComponent period hPeriod metric potential
          component patch coordinate index = 0 := by
  let model := localSymmetricTensorDivergenceModelCovector period hPeriod
    metric.metric
    (regularGlobalGaugeCurvatureTensor period hPeriod metric potential
      component) patch coordinate
  constructor
  · intro hZero index
    unfold regularLocalMaxwellDivergenceComponent
    rw [← localSymmetricTensorDivergenceIntrinsicCovector_frame period
      hPeriod metric.metric
      (regularGlobalGaugeCurvatureTensor period hPeriod metric potential
        component) patch coordinate (Pi.single index 1)]
    rw [hZero]
    rfl
  · intro hComponents
    have hLinear : model.toLinearMap = 0 := by
      apply (Pi.basisFun Real Index4).ext
      intro index
      simpa [model, regularLocalMaxwellDivergenceComponent,
        Pi.basisFun_apply] using hComponents index
    have hModel : model = 0 := by
      apply ContinuousLinearMap.ext
      intro vector
      exact LinearMap.congr_fun hLinear vector
    unfold localSymmetricTensorDivergenceIntrinsicCovector
    change LinearMap.toContinuousLinearMap
      (model.toLinearMap.comp
        ((Pi.basisFun Real Index4).equiv (patch.frame coordinate)
          (Equiv.refl Index4)).symm.toLinearMap) = 0
    rw [hModel]
    rfl

/-- At any chart point, vanishing of the global Maxwell covector is precisely
the four local component equations. -/
theorem regularGlobalMaxwellDivergence_at_eq_zero_iff
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    regularGlobalMaxwellDivergence period hPeriod metric potential component
        (patch.coordinateMap coordinate) = 0 ↔
      ∀ index : Index4,
        regularLocalMaxwellDivergenceComponent period hPeriod metric potential
          component patch coordinate index = 0 := by
  rw [regularGlobalMaxwellDivergence_eq_local]
  exact regularLocalMaxwellDivergenceIntrinsic_eq_zero_iff period hPeriod
    metric potential component patch coordinate

/-- The chart-free source-free Maxwell equation. -/
def RegularGeneralMetricStrongMaxwellEquation
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod) : Prop :=
  ∀ component : Fin 2,
    regularGlobalMaxwellDivergence period hPeriod metric potential component = 0

/-- The global equation is equivalent to all eight scalar equations in every
holonomic chart. -/
theorem regularGeneralMetricStrongMaxwellEquation_iff_local_components
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod) :
    RegularGeneralMetricStrongMaxwellEquation period hPeriod metric potential ↔
      ∀ (component : Fin 2)
        (patch : SmoothHolonomicFrameChart4 period hPeriod)
        (coordinate : Vector4) (index : Index4),
        regularLocalMaxwellDivergenceComponent period hPeriod metric potential
          component patch coordinate index = 0 := by
  constructor
  · intro hGlobal component patch coordinate
    have hAt := congrArg
      (fun field => field (patch.coordinateMap coordinate))
      (hGlobal component)
    change regularGlobalMaxwellDivergence period hPeriod metric potential
        component (patch.coordinateMap coordinate) = 0 at hAt
    exact (regularGlobalMaxwellDivergence_at_eq_zero_iff period hPeriod metric
      potential component patch coordinate).mp hAt
  · intro hLocal component
    apply ContMDiffSection.ext
    intro point
    change regularGlobalMaxwellDivergence period hPeriod metric potential
        component point = 0
    let witness :=
      canonicalPhysicalScalarEulerChartWitness period hPeriod point
    rw [← witness.coordinate_eq]
    exact (regularGlobalMaxwellDivergence_at_eq_zero_iff period hPeriod metric
      potential component witness.patch witness.coordinate).mpr
        (hLocal component witness.patch witness.coordinate)

/-- Gate marker for the global/local pointwise strong Maxwell PDE. -/
theorem regular_general_metric_strong_maxwell_pde_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod) :
    RegularGeneralMetricStrongMaxwellEquation period hPeriod metric potential ↔
      ∀ (component : Fin 2)
        (patch : SmoothHolonomicFrameChart4 period hPeriod)
        (coordinate : Vector4) (index : Index4),
        regularLocalMaxwellDivergenceComponent period hPeriod metric potential
          component patch coordinate index = 0 :=
  regularGeneralMetricStrongMaxwellEquation_iff_local_components period hPeriod
    metric potential

end

end P0EFTJanusProgramPRegularGeneralMetricStrongMaxwellPDE4D
end JanusFormal
