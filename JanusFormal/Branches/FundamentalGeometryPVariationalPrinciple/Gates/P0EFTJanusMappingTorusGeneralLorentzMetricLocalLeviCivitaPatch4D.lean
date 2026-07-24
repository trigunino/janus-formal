import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.StdBasis
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusScalarStressLeviCivitaConnectionJet4D

/-!
# Smooth local Levi--Civita patches for general quotient metrics

A supplied smooth holonomic chart/frame turns a genuine
`SmoothGeneralLorentzMetric` into smooth coordinate coefficients.  This gate
constructs their coordinate derivatives, the local Christoffel symbols and the
pointwise Levi--Civita stress jet, then proves patchwise stress conservation
under the scalar Euler equation.  No compatibility on overlaps and no global
connection are asserted.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open Module
open scoped Manifold ContDiff Matrix Matrix.Norms.Frobenius
open P0EFTJanusMetricCoupledScalarMatterJetVariation
open P0EFTJanusMetricInducedScalarStressVariation4D
open P0EFTJanusScalarStressCovariantJetConservation4D
open P0EFTJanusScalarStressCoordinateConnectionJet4D
open P0EFTJanusScalarStressLeviCivitaConnectionJet4D
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D

variable (period : Real) (hPeriod : period ≠ 0)

abbrev Index4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Index4
abbrev Vector4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4
abbrev Matrix4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Matrix4
abbrev MetricDerivative4 :=
  P0EFTJanusScalarStressLeviCivitaConnectionJet4D.MetricDerivative4

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

private abbrev TangentFiber (point : EffectiveQuotient period hPeriod) :=
  TangentSpace coverModelWithCorners point

/-- A supplied smooth holonomic coordinate patch.  The final field is the
standard local-trivialization evaluation law: every genuine smooth symmetric
two-tensor has smooth scalar coefficients in this frame. -/
structure SmoothHolonomicFrameChart4 where
  coordinateMap : Vector4 → EffectiveQuotient period hPeriod
  coordinateMap_contMDiff :
    ContMDiff (modelWithCornersSelf Real Vector4) coverModelWithCorners ∞
      coordinateMap
  coordinateMap_isLocalDiffeomorph :
    IsLocalDiffeomorph (modelWithCornersSelf Real Vector4)
      coverModelWithCorners ∞ coordinateMap
  frame : ∀ coordinate,
    Basis Index4 Real (TangentFiber period hPeriod (coordinateMap coordinate))
  frame_eq_coordinateDerivative : ∀ coordinate index,
    frame coordinate index =
      mfderiv (modelWithCornersSelf Real Vector4) coverModelWithCorners
        coordinateMap coordinate (Pi.single index 1)
  frame_contMDiff : ∀ index,
    ContMDiff (modelWithCornersSelf Real Vector4)
      coverModelWithCorners.tangent ∞
      (fun coordinate =>
        (⟨coordinateMap coordinate, frame coordinate index⟩ :
          TangentBundle coverModelWithCorners
            (EffectiveQuotient period hPeriod)))
  tensorCoefficient_contDiff : ∀
      (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
      (first second : Index4),
    ContDiff Real ∞ (fun coordinate =>
      tensor.tensor (coordinateMap coordinate)
        (frame coordinate first) (frame coordinate second))

/-- Covariant metric coefficient in the supplied holonomic frame. -/
def localMetricCoefficient
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (first second : Index4) (coordinate : Vector4) : Real :=
  metric.tensor.tensor (patch.coordinateMap coordinate)
    (patch.frame coordinate first) (patch.frame coordinate second)

/-- Matrix of the metric in the supplied frame. -/
def localMetricMatrix
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) : Matrix4 :=
  fun first second =>
    localMetricCoefficient period hPeriod metric patch first second coordinate

theorem localMetricCoefficient_contDiff
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (first second : Index4) :
    ContDiff Real ∞
      (localMetricCoefficient period hPeriod metric patch first second) :=
  patch.tensorCoefficient_contDiff metric.tensor first second

theorem localMetricMatrix_contDiff
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) :
    ContDiff Real ∞ (localMetricMatrix period hPeriod metric patch) := by
  have hFormula : localMetricMatrix period hPeriod metric patch =
      fun coordinate => ∑ first : Index4, ∑ second : Index4,
        localMetricCoefficient period hPeriod metric patch first second coordinate •
          Matrix.single first second (1 : Real) := by
    funext coordinate
    simpa [localMetricMatrix] using
      (Matrix.matrix_eq_sum_single
        (localMetricMatrix period hPeriod metric patch coordinate))
  rw [hFormula]
  apply ContDiff.sum
  intro first _
  apply ContDiff.sum
  intro second _
  exact
    (localMetricCoefficient_contDiff period hPeriod metric patch first second).smul_const _

private def localMetricBilinForm
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    LinearMap.BilinForm Real
      (TangentFiber period hPeriod (patch.coordinateMap coordinate)) :=
  (metric.tensor.tensor (patch.coordinateMap coordinate)).toBilinForm

private theorem localMetricBilinForm_nondegenerate
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    (localMetricBilinForm period hPeriod metric patch coordinate).Nondegenerate := by
  constructor
  · intro vector hVector
    apply metric_nondegenerate_at period hPeriod metric
    apply ContinuousLinearMap.ext
    intro second
    simpa [localMetricBilinForm] using hVector second
  · intro vector hVector
    apply metric_nondegenerate_at period hPeriod metric
    apply ContinuousLinearMap.ext
    intro second
    rw [metric.tensor.symmetric]
    simpa [localMetricBilinForm] using hVector second

theorem localMetricMatrix_det_ne_zero
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    (localMetricMatrix period hPeriod metric patch coordinate).det ≠ 0 := by
  have hDet :=
    (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero
      (patch.frame coordinate)).mp
      (localMetricBilinForm_nondegenerate period hPeriod metric patch coordinate)
  have hMatrix :
      localMetricMatrix period hPeriod metric patch coordinate =
        LinearMap.BilinForm.toMatrix (patch.frame coordinate)
          (localMetricBilinForm period hPeriod metric patch coordinate) := by
    ext first second
    simp [localMetricMatrix, localMetricCoefficient, localMetricBilinForm]
  rw [hMatrix]
  exact hDet

/-- The local coefficient matrix defines the pointwise fixed-sign metric
expected by the finite-index Levi--Civita gate. -/
def localFixedSignMetric
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) : FixedSignMetric4 where
  metric := localMetricMatrix period hPeriod metric patch coordinate
  orientation := (localMetricMatrix period hPeriod metric patch coordinate).det
  orientation_ne_zero :=
    localMetricMatrix_det_ne_zero period hPeriod metric patch coordinate
  metric_symmetric := by
    ext first second
    simp only [Matrix.transpose_apply, localMetricMatrix, localMetricCoefficient]
    exact metric.tensor.symmetric _ _ _
  metric_mem_domain := by
    have hDet := localMetricMatrix_det_ne_zero period hPeriod metric patch coordinate
    simpa [fixedDeterminantSignDomain, pow_two] using sq_pos_of_ne_zero hDet

theorem localMetricInverse_contDiff
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) :
    ContDiff Real ∞ (fun coordinate =>
      (localMetricMatrix period hPeriod metric patch coordinate)⁻¹) := by
  rw [contDiff_iff_contDiffAt]
  intro coordinate
  have hUnit : IsUnit (localMetricMatrix period hPeriod metric patch coordinate) :=
    (localFixedSignMetric period hPeriod metric patch coordinate).metric_isUnit
  have hFunctions :
      (fun current =>
        (localMetricMatrix period hPeriod metric patch current)⁻¹) =
        fun current =>
          Ring.inverse (localMetricMatrix period hPeriod metric patch current) := by
    funext current
    exact Matrix.nonsing_inv_eq_ringInverse
      (A := localMetricMatrix period hPeriod metric patch current)
  rw [hFunctions]
  have hInverse : ContDiffAt Real ∞
      (Ring.inverse : Matrix4 → Matrix4) (hUnit.unit : Matrix4) :=
    contDiffAt_ringInverse Real hUnit.unit
  rw [hUnit.unit_spec] at hInverse
  exact hInverse.comp coordinate
    (localMetricMatrix_contDiff period hPeriod metric patch).contDiffAt

private def matrixEntryCLM (first second : Index4) : Matrix4 →L[Real] Real :=
  LinearMap.toContinuousLinearMap
    { toFun := fun matrix => matrix first second
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }

theorem localMetricInverseEntry_contDiff
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (first second : Index4) :
    ContDiff Real ∞ (fun coordinate =>
      (localMetricMatrix period hPeriod metric patch coordinate)⁻¹ first second) :=
  (matrixEntryCLM first second).contDiff.comp
    (localMetricInverse_contDiff period hPeriod metric patch)

/-- Coordinate partial derivative `∂_derivative g_first,second`. -/
def localMetricDerivative
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) : MetricDerivative4 :=
  fun derivative first second =>
    fderiv Real
      (localMetricCoefficient period hPeriod metric patch first second)
      coordinate (Pi.single derivative 1)

theorem localMetricDerivative_contDiff
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (derivative first second : Index4) :
    ContDiff Real ∞ (fun coordinate =>
      localMetricDerivative period hPeriod metric patch coordinate
        derivative first second) := by
  have hDerivative : ContDiff Real ∞
      (fderiv Real
        (localMetricCoefficient period hPeriod metric patch first second)) :=
    (localMetricCoefficient_contDiff period hPeriod metric patch first second).fderiv_right
      (m := ∞) (by simp)
  exact hDerivative.clm_apply contDiff_const

theorem localMetricDerivative_symmetric
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) (derivative first second : Index4) :
    localMetricDerivative period hPeriod metric patch coordinate
        derivative first second =
      localMetricDerivative period hPeriod metric patch coordinate
        derivative second first := by
  have hCoefficient :
      localMetricCoefficient period hPeriod metric patch first second =
        localMetricCoefficient period hPeriod metric patch second first := by
    funext current
    exact metric.tensor.symmetric _ _ _
  unfold localMetricDerivative
  rw [hCoefficient]

/-- Smooth Christoffel coefficients of the supplied local chart. -/
def localLeviCivitaChristoffel
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) (upper first second : Index4) : Real :=
  leviCivitaChristoffel
    (localFixedSignMetric period hPeriod metric patch coordinate)
    (localMetricDerivative period hPeriod metric patch coordinate)
    upper first second

theorem localLeviCivitaChristoffel_contDiff
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (upper first second : Index4) :
    ContDiff Real ∞ (fun coordinate =>
      localLeviCivitaChristoffel period hPeriod metric patch coordinate
        upper first second) := by
  unfold localLeviCivitaChristoffel leviCivitaChristoffel
  apply ContDiff.sum
  intro contracted _
  exact
    (localMetricInverseEntry_contDiff period hPeriod metric patch
      upper contracted).mul
      (contDiff_const.mul
        (((localMetricDerivative_contDiff period hPeriod metric patch
              first second contracted).add
            (localMetricDerivative_contDiff period hPeriod metric patch
              second first contracted)).sub
          (localMetricDerivative_contDiff period hPeriod metric patch
            contracted first second)))

/-- Pointwise Levi--Civita connection jet supplied by the smooth patch. -/
def localLeviCivitaConnectionJet
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) : MetricCompatibleTorsionFreeConnectionJet4 :=
  leviCivitaConnectionJet
    (localFixedSignMetric period hPeriod metric patch coordinate)
    (localMetricDerivative period hPeriod metric patch coordinate)
    (localMetricDerivative_symmetric period hPeriod metric patch coordinate)

@[simp]
theorem localLeviCivitaConnectionJet_christoffel
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) (upper first second : Index4) :
    (localLeviCivitaConnectionJet period hPeriod metric patch coordinate).christoffel
        upper first second =
      localLeviCivitaChristoffel period hPeriod metric patch coordinate
        upper first second :=
  rfl

/-- Canonical coordinate-stress realization at each point of the patch. -/
def localLeviCivitaStressRealization
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (potentialValue potentialSlope : Vector4 → Real)
    (jet : Vector4 → CoordinateScalarJet2)
    (coordinate : Vector4) :
    CoordinateStressDerivativeRealization
      (localLeviCivitaConnectionJet period hPeriod metric patch coordinate)
      (potentialValue coordinate) (potentialSlope coordinate) (jet coordinate) :=
  leviCivitaCoordinateStressDerivativeRealization
    (localFixedSignMetric period hPeriod metric patch coordinate)
    (localMetricDerivative period hPeriod metric patch coordinate)
    (localMetricDerivative_symmetric period hPeriod metric patch coordinate)
    (potentialValue coordinate) (potentialSlope coordinate) (jet coordinate)

/-- Local scalar-stress conservation at every coordinate of the supplied
patch, conditional only on the pointwise Euler equation there. -/
theorem localLeviCivitaStressDivergence_eq_zero_of_euler
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (potentialValue potentialSlope : Vector4 → Real)
    (jet : Vector4 → CoordinateScalarJet2)
    (hEuler : ∀ coordinate,
      covariantScalarStressEulerResidual
        (localFixedSignMetric period hPeriod metric patch coordinate)
        (potentialSlope coordinate)
        (coordinateScalarJetNormalForm
          (localLeviCivitaConnectionJet period hPeriod metric patch coordinate)
          (jet coordinate)) = 0) :
    ∀ coordinate,
      coordinateCovariantStressDivergence
        (localLeviCivitaStressRealization period hPeriod metric patch
          potentialValue potentialSlope jet coordinate) = 0 := by
  intro coordinate
  exact leviCivitaCoordinateStressDivergence_eq_zero_of_euler
    (localFixedSignMetric period hPeriod metric patch coordinate)
    (localMetricDerivative period hPeriod metric patch coordinate)
    (localMetricDerivative_symmetric period hPeriod metric patch coordinate)
    (potentialValue coordinate) (potentialSlope coordinate) (jet coordinate)
    (hEuler coordinate)

end

end P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
end JanusFormal
