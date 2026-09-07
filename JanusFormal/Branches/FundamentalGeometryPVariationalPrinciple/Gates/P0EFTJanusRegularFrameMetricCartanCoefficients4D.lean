import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusRegularFrameSymmetricTensorDivergence4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusMetricCartanGlobalAction4D

/-! # Intrinsic metric Cartan action in a fixed regular frame

Smooth frame coefficients reconstruct every smooth tangent ghost. The
intrinsic bracket product rule gives the nonholonomic coefficient formula
for the genuine Cartan action on any smooth symmetric tensor.
-/

namespace JanusFormal
namespace P0EFTJanusRegularFrameMetricCartanCoefficients4D

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 600000

noncomputable section
open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusSmoothDiffeomorphismGhostLieBracket4D
open P0EFTJanusMappingTorusGradedScalarGhostAction4D
open P0EFTJanusMappingTorusScalarGhostCEClosure4D
open P0EFTJanusMappingTorusMetricCartanFiberCore4D
open P0EFTJanusMappingTorusMetricCartanGlobalAction4D
open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D
open P0EFTJanusRegularFrameSymmetricTensorDivergence4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
private abbrev Ghost := CInfinityDiffeomorphismGhost period hPeriod

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- A genuine smooth tangent ghost, assembled from smooth regular-frame coefficients. -/
def regularFrameGhostFromCoefficients
    (reference : RegularGeneralLorentzMetric period hPeriod)
    (coefficients : Fin 4 → SmoothScalarField period hPeriod) : Ghost period hPeriod :=
  ∑ index : Fin 4, cInfinityScalarSmulGhost period hPeriod
    (analyticScalarToCInfinity period hPeriod (coefficients index)) (reference.frame index)

@[simp] theorem regularFrameGhostFromCoefficients_apply
    (reference : RegularGeneralLorentzMetric period hPeriod)
    (coefficients : Fin 4 → SmoothScalarField period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    regularFrameGhostFromCoefficients period hPeriod reference coefficients point =
      ∑ index : Fin 4, coefficients index point • reference.frame index point := by
  let evaluation : Ghost period hPeriod →ₗ[Real]
      TangentSpace coverModelWithCorners point :=
    { toFun := fun ghost => ghost point
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have h := map_sum evaluation (fun index : Fin 4 =>
    cInfinityScalarSmulGhost period hPeriod
      (analyticScalarToCInfinity period hPeriod (coefficients index)) (reference.frame index))
    Finset.univ
  exact h

/-- Canonical smooth coefficients of an arbitrary smooth tangent ghost. -/
def regularFrameCartanGhostCoefficient
    (reference : RegularGeneralLorentzMetric period hPeriod)
    (ghost : Ghost period hPeriod) (index : Fin 4) : SmoothScalarField period hPeriod :=
  generalMetricFiniteFrameCoefficient period hPeriod
    (regularGeneralLorentzMetricSmoothD8Frame period hPeriod reference)
    reference.metric ghost index

theorem regularFrameGhostFromCoefficients_reconstructs
    (reference : RegularGeneralLorentzMetric period hPeriod) (ghost : Ghost period hPeriod) :
    regularFrameGhostFromCoefficients period hPeriod reference
        (regularFrameCartanGhostCoefficient period hPeriod reference ghost) = ghost := by
  apply ContMDiffSection.ext
  intro point
  rw [regularFrameGhostFromCoefficients_apply]
  exact (generalMetricFiniteFrame_reconstructs period hPeriod
    (regularGeneralLorentzMetricSmoothD8Frame period hPeriod reference)
    reference.metric ghost point).symm

private theorem scalarFrameGhost_bracket
    (reference : RegularGeneralLorentzMetric period hPeriod)
    (scalar : SmoothScalarField period hPeriod)
    (direction test : Fin 4) (point : EffectiveQuotient period hPeriod) :
    smoothGhostLieBracket period hPeriod
        (cInfinityScalarSmulGhost period hPeriod
          (analyticScalarToCInfinity period hPeriod scalar) (reference.frame direction))
        (reference.frame test) point =
      -(frameDerivative period hPeriod Real
          (regularGeneralLorentzMetricSmoothD8Frame period hPeriod reference) scalar point test) •
          reference.frame direction point +
        scalar point • regularFrameLieBracket period hPeriod reference direction test point := by
  exact VectorField.mlieBracket_smul_left
    (scalar.contMDiff_toFun.mdifferentiableAt (by simp))
    ((reference.frame direction).contMDiff.mdifferentiableAt (by simp))

private theorem scalarFrameGhost_cartanCoefficient
    (reference : RegularGeneralLorentzMetric period hPeriod)
    (scalar : SmoothScalarField period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) (direction first second : Fin 4) :
    regularFrameSymmetricTensorCoefficient period hPeriod reference
        (smoothMetricCartanAction period hPeriod
          (cInfinityScalarSmulGhost period hPeriod
            (analyticScalarToCInfinity period hPeriod scalar) (reference.frame direction))
          tensor) first second point =
      scalar point * frameDerivative period hPeriod Real
          (regularGeneralLorentzMetricSmoothD8Frame period hPeriod reference)
          (regularFrameSymmetricTensorCoefficient period hPeriod reference tensor first second)
          point direction +
        frameDerivative period hPeriod Real
          (regularGeneralLorentzMetricSmoothD8Frame period hPeriod reference)
          scalar point first *
          regularFrameSymmetricTensorCoefficient period hPeriod reference tensor direction second
            point +
        frameDerivative period hPeriod Real
          (regularGeneralLorentzMetricSmoothD8Frame period hPeriod reference)
          scalar point second *
          regularFrameSymmetricTensorCoefficient period hPeriod reference tensor first direction
            point -
        ∑ upper : Fin 4,
          (scalar point * regularFrameStructureCoefficient period hPeriod reference
              direction first upper point *
            regularFrameSymmetricTensorCoefficient period hPeriod reference tensor upper second
              point +
          scalar point * regularFrameStructureCoefficient period hPeriod reference
              direction second upper point *
            regularFrameSymmetricTensorCoefficient period hPeriod reference tensor first upper
              point) := by
  rw [regularFrameSymmetricTensorCoefficient_apply, smoothMetricCartanAction_apply]
  unfold metricCartanResidualAt
  change mvfderiv coverModelWithCorners
      (regularFrameSymmetricTensorCoefficient period hPeriod reference tensor first second).toFun
      point (scalar point • reference.frame direction point) -
    tensor.tensor point
      (smoothGhostLieBracket period hPeriod
        (cInfinityScalarSmulGhost period hPeriod
          (analyticScalarToCInfinity period hPeriod scalar) (reference.frame direction))
        (reference.frame first) point) (reference.frame second point) -
    tensor.tensor point (reference.frame first point)
      (smoothGhostLieBracket period hPeriod
        (cInfinityScalarSmulGhost period hPeriod
          (analyticScalarToCInfinity period hPeriod scalar) (reference.frame direction))
        (reference.frame second) point) = _
  rw [map_smul, scalarFrameGhost_bracket, scalarFrameGhost_bracket,
    regularFrameStructureCoefficient_reconstructs,
    regularFrameStructureCoefficient_reconstructs]
  simp only [map_add, map_sum, map_smul, add_apply,
    sum_apply, smul_apply, smul_eq_mul]
  change scalar point * frameDerivative period hPeriod Real
      (regularGeneralLorentzMetricSmoothD8Frame period hPeriod reference)
      (regularFrameSymmetricTensorCoefficient period hPeriod reference tensor first second)
      point direction -
    (-(frameDerivative period hPeriod Real
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod reference) scalar point first) *
        regularFrameSymmetricTensorCoefficient period hPeriod reference tensor direction second
          point +
      scalar point * ∑ upper : Fin 4,
        regularFrameStructureCoefficient period hPeriod reference direction first upper point *
          regularFrameSymmetricTensorCoefficient period hPeriod reference tensor upper second
            point) -
    (-(frameDerivative period hPeriod Real
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod reference) scalar point second) *
        regularFrameSymmetricTensorCoefficient period hPeriod reference tensor first direction
          point +
      scalar point * ∑ upper : Fin 4,
        regularFrameStructureCoefficient period hPeriod reference direction second upper point *
          regularFrameSymmetricTensorCoefficient period hPeriod reference tensor first upper
            point) = _
  simp only [Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
  ring

/-- Gate 653: the actual Cartan action has the nonholonomic frame coefficient formula. -/
theorem smoothMetricCartanAction_regularFrameCoefficient
    (reference : RegularGeneralLorentzMetric period hPeriod)
    (coefficients : Fin 4 → SmoothScalarField period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) (first second : Fin 4) :
    regularFrameSymmetricTensorCoefficient period hPeriod reference
        (smoothMetricCartanAction period hPeriod
          (regularFrameGhostFromCoefficients period hPeriod reference coefficients) tensor)
        first second point =
      ∑ direction : Fin 4,
        (coefficients direction point * frameDerivative period hPeriod Real
            (regularGeneralLorentzMetricSmoothD8Frame period hPeriod reference)
            (regularFrameSymmetricTensorCoefficient period hPeriod reference tensor first second)
            point direction +
          frameDerivative period hPeriod Real
            (regularGeneralLorentzMetricSmoothD8Frame period hPeriod reference)
            (coefficients direction) point first *
            regularFrameSymmetricTensorCoefficient period hPeriod reference tensor direction second
              point +
          frameDerivative period hPeriod Real
            (regularGeneralLorentzMetricSmoothD8Frame period hPeriod reference)
            (coefficients direction) point second *
            regularFrameSymmetricTensorCoefficient period hPeriod reference tensor first direction
              point -
          ∑ upper : Fin 4,
            (coefficients direction point * regularFrameStructureCoefficient period hPeriod reference
                direction first upper point *
              regularFrameSymmetricTensorCoefficient period hPeriod reference tensor upper second
                point +
            coefficients direction point * regularFrameStructureCoefficient period hPeriod reference
                direction second upper point *
              regularFrameSymmetricTensorCoefficient period hPeriod reference tensor first upper
                point)) := by
  let evaluation : Ghost period hPeriod →ₗ[Real] Real :=
    { toFun := fun ghost => regularFrameSymmetricTensorCoefficient period hPeriod reference
        (smoothMetricCartanAction period hPeriod ghost tensor) first second point
      map_add' := by
        intro left right
        rw [smoothMetricCartanAction_add_acting]
        rfl
      map_smul' := by
        intro scalar ghost
        rw [smoothMetricCartanAction_smul_acting]
        rfl }
  change evaluation (∑ index : Fin 4,
    cInfinityScalarSmulGhost period hPeriod
      (analyticScalarToCInfinity period hPeriod (coefficients index))
      (reference.frame index)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro direction _
  exact scalarFrameGhost_cartanCoefficient period hPeriod reference (coefficients direction)
    tensor point direction first second

/-- The same formula applies to every smooth ghost via its canonical smooth coefficients. -/
theorem smoothMetricCartanAction_eq_reconstructedGhost
    (reference : RegularGeneralLorentzMetric period hPeriod)
    (ghost : Ghost period hPeriod) (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    smoothMetricCartanAction period hPeriod ghost tensor =
      smoothMetricCartanAction period hPeriod
        (regularFrameGhostFromCoefficients period hPeriod reference
          (regularFrameCartanGhostCoefficient period hPeriod reference ghost)) tensor := by
  rw [regularFrameGhostFromCoefficients_reconstructs]

end
end P0EFTJanusRegularFrameMetricCartanCoefficients4D
end JanusFormal
