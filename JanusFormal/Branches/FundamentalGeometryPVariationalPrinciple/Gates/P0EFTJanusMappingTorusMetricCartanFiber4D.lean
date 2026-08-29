import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusMetricCartanFiberCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralLorentzTensor4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusSmoothDiffeomorphismGhostLieBracket4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGradedScalarGhostAction4D

/-!
# Metric Cartan fibers on the effective quotient

The generic Cartan residual specializes canonically to a smooth symmetric
tensor and a `C∞` diffeomorphism ghost.  Only global smooth assembly of the
resulting fiber tensors is retained as an explicit contract.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusMetricCartanFiber4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusSmoothDiffeomorphismGhostLieBracket4D
open P0EFTJanusMappingTorusMetricCartanFiberCore4D
open P0EFTJanusMappingTorusGradedScalarGhostAction4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient :=
  MappingTorus (sphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

private abbrev TangentSection :=
  ∀ point : EffectiveQuotient period hPeriod,
    TangentSpace coverModelWithCorners point

private abbrev Ghost :=
  CInfinityDiffeomorphismGhost period hPeriod

/-- Smoothness of tensor evaluation on locally differentiable test sections.
This is the exact local hypothesis consumed by the generic tensoriality
criterion. -/
theorem smoothSymmetricTensorEvaluation_mdifferentiableAt
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (first second : TangentSection period hPeriod)
    (hFirst : MDifferentiableAt coverModelWithCorners
      (coverModelWithCorners.prod 𝓘(Real, CoverCoordinates))
      (T% first) point)
    (hSecond : MDifferentiableAt coverModelWithCorners
      (coverModelWithCorners.prod 𝓘(Real, CoverCoordinates))
      (T% second) point) :
    MDifferentiableAt coverModelWithCorners 𝓘(Real, Real)
      (fun current =>
        tensor.tensor current (first current) (second current)) point := by
  have hTensorAt :=
    tensor.tensor.contMDiff.mdifferentiableAt (x := point) (by simp)
  have hAppliedAt := hTensorAt.clm_bundle_apply₂ hFirst hSecond
  rw [mdifferentiableAt_section] at hAppliedAt
  simpa using hAppliedAt

/-- The pointwise metric Cartan derivative, already packaged as a symmetric
covariant two-tensor in the selected fiber. -/
def smoothMetricCartanFiber
    (acting : Ghost period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    TangentSpace coverModelWithCorners point →L[Real]
      TangentSpace coverModelWithCorners point →L[Real] Real :=
  metricCartanFiberCovariantTwoTensor coverModelWithCorners
    acting tensor.tensor point
    (smoothSymmetricTensorEvaluation_mdifferentiableAt
      period hPeriod tensor point)

/-- Evaluation of the specialized fiber tensor is the Cartan formula. -/
theorem smoothMetricCartanFiber_apply
    (acting : Ghost period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (first second : Ghost period hPeriod) :
    smoothMetricCartanFiber period hPeriod acting tensor point
        (first point) (second point) =
      metricCartanResidualAt coverModelWithCorners acting tensor.tensor
        point first second := by
  exact metricCartanFiberCovariantTwoTensor_apply coverModelWithCorners
    acting tensor.tensor point
    (smoothSymmetricTensorEvaluation_mdifferentiableAt
      period hPeriod tensor point)
    first second
    (first.contMDiff.mdifferentiableAt (by simp))
    (second.contMDiff.mdifferentiableAt (by simp))

/-- The specialized fiber tensor is symmetric. -/
theorem smoothMetricCartanFiber_symm
    (acting : Ghost period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (first second : TangentSpace coverModelWithCorners point) :
    smoothMetricCartanFiber period hPeriod acting tensor point first second =
      smoothMetricCartanFiber period hPeriod acting tensor point second first := by
  exact metricCartanFiberCovariantTwoTensor_symm coverModelWithCorners
    acting tensor.tensor point
    (smoothSymmetricTensorEvaluation_mdifferentiableAt
      period hPeriod tensor point)
    tensor.symmetric first second

/-- Evaluation of a smooth symmetric tensor on two smooth tangent sections
is a genuine smooth scalar field. -/
def smoothMetricEvaluationScalar
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (first second : Ghost period hPeriod) :
    CInfinityScalarField period hPeriod :=
  ⟨fun point => tensor.tensor point (first point) (second point), by
    intro point
    have hAppliedAt :=
      (tensor.tensor.contMDiff point).clm_bundle_apply₂
        (first.contMDiff point) (second.contMDiff point)
    rw [Bundle.contMDiffAt_section] at hAppliedAt
    simpa using hAppliedAt⟩

/-- The Cartan residual evaluated on any two global smooth test fields is a
global smooth scalar. -/
def smoothMetricCartanResidualScalar
    (acting : Ghost period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (first second : Ghost period hPeriod) :
    CInfinityScalarField period hPeriod :=
  cInfinityScalarLieDerivative period hPeriod acting
      (smoothMetricEvaluationScalar period hPeriod tensor first second) -
    smoothMetricEvaluationScalar period hPeriod tensor
      (smoothGhostLieBracket period hPeriod acting first) second -
    smoothMetricEvaluationScalar period hPeriod tensor first
      (smoothGhostLieBracket period hPeriod acting second)

@[simp]
theorem smoothMetricCartanResidualScalar_apply
    (acting : Ghost period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (first second : Ghost period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    smoothMetricCartanResidualScalar period hPeriod acting tensor
        first second point =
      metricCartanResidualAt coverModelWithCorners acting tensor.tensor
        point first second := by
  change
    mvfderiv coverModelWithCorners
        (fun current =>
          tensor.tensor current (first current) (second current))
        point (acting point) -
      tensor.tensor point
        (VectorField.mlieBracket coverModelWithCorners acting first point)
        (second point) -
      tensor.tensor point (first point)
        (VectorField.mlieBracket coverModelWithCorners acting second point) =
      _
  rfl

/-- Remaining honest analytic input for one ghost/tensor pair: the proven
fiber construction must assemble to a globally smooth tensor section. -/
structure SmoothMetricCartanBundlingData
    (acting : Ghost period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) where
  bundled : SmoothSymmetricCovariantTwoTensor period hPeriod
  fiber_eq :
    ∀ point,
      bundled.tensor point =
        smoothMetricCartanFiber period hPeriod acting tensor point

/-- Any global smooth bundling witness satisfies the intrinsic Cartan
evaluation formula. -/
theorem SmoothMetricCartanBundlingData.cartan
    {acting : Ghost period hPeriod}
    {tensor : SmoothSymmetricCovariantTwoTensor period hPeriod}
    (data : SmoothMetricCartanBundlingData period hPeriod acting tensor)
    (point : EffectiveQuotient period hPeriod)
    (first second : Ghost period hPeriod) :
    data.bundled.tensor point (first point) (second point) =
      metricCartanResidualAt coverModelWithCorners acting tensor.tensor
        point first second := by
  rw [data.fiber_eq]
  exact smoothMetricCartanFiber_apply period hPeriod acting tensor point
    first second

end

end P0EFTJanusMappingTorusMetricCartanFiber4D
end JanusFormal
