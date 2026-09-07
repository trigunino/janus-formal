import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2GaugeCoefficientFrameTransport4D

/-! # Exact coefficient transition preserving the intrinsic gauge potential

This transition compares arbitrary regular frames, including the distinct
frames produced by direct and iterated principal-root charts. Its dependence
on those frames is retained.
-/

namespace JanusFormal
namespace P0EFTJanusRegularFrameGaugeCoefficientTransition4D

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 600000

noncomputable section
open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusProgramPGlobalGaugeTangentIntrinsicEmbedding4D
open P0EFTJanusProgramPRegularFrameGaugePotentialReconstruction4D
open P0EFTJanusProgramPRegularGeneralMetricC2GaugeCoefficientFrameTransport4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
private abbrev GaugeCoefficients := SmoothQuotientField period hPeriod GaugeFiber
local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- Read in the new frame the intrinsic potential reconstructed in the old frame. -/
def regularFrameGaugeCoefficientTransition
    (oldMetric newMetric : RegularGeneralLorentzMetric period hPeriod)
    (coefficients : GaugeCoefficients period hPeriod) : GaugeCoefficients period hPeriod :=
  gaugePotentialFrameCoefficients period hPeriod newMetric
    (regularFrameGaugePotentialFromCoefficients period hPeriod oldMetric coefficients)

/-- The transition preserves the actual smooth potential exactly. -/
theorem regularFrameGaugeCoefficientTransition_preserves_potential
    (oldMetric newMetric : RegularGeneralLorentzMetric period hPeriod)
    (coefficients : GaugeCoefficients period hPeriod) :
    regularFrameGaugePotentialFromCoefficients period hPeriod newMetric
        (regularFrameGaugeCoefficientTransition period hPeriod oldMetric newMetric coefficients) =
      regularFrameGaugePotentialFromCoefficients period hPeriod oldMetric coefficients :=
  regularFrameGaugePotentialFromCoefficients_frameCoefficients period hPeriod newMetric _

@[simp]
theorem regularFrameGaugeCoefficientTransition_refl
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (coefficients : GaugeCoefficients period hPeriod) :
    regularFrameGaugeCoefficientTransition period hPeriod metric metric coefficients = coefficients :=
  gaugePotentialFrameCoefficients_reconstructed period hPeriod metric coefficients

/-- Re-expression of any already given intrinsic potential. -/
theorem regularFrameGaugeCoefficientTransition_frameCoefficients
    (oldMetric newMetric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod) :
    regularFrameGaugeCoefficientTransition period hPeriod oldMetric newMetric
        (gaugePotentialFrameCoefficients period hPeriod oldMetric potential) =
      gaugePotentialFrameCoefficients period hPeriod newMetric potential := by
  unfold regularFrameGaugeCoefficientTransition
  rw [regularFrameGaugePotentialFromCoefficients_frameCoefficients]

/-- Successive coefficient changes preserve the same potential and compose exactly. -/
theorem regularFrameGaugeCoefficientTransition_comp
    (first second third : RegularGeneralLorentzMetric period hPeriod)
    (coefficients : GaugeCoefficients period hPeriod) :
    regularFrameGaugeCoefficientTransition period hPeriod second third
        (regularFrameGaugeCoefficientTransition period hPeriod first second coefficients) =
      regularFrameGaugeCoefficientTransition period hPeriod first third coefficients := by
  unfold regularFrameGaugeCoefficientTransition
  rw [regularFrameGaugePotentialFromCoefficients_frameCoefficients]

@[simp]
theorem regularFrameGaugeCoefficientTransition_inverse
    (oldMetric newMetric : RegularGeneralLorentzMetric period hPeriod)
    (coefficients : GaugeCoefficients period hPeriod) :
    regularFrameGaugeCoefficientTransition period hPeriod newMetric oldMetric
        (regularFrameGaugeCoefficientTransition period hPeriod oldMetric newMetric coefficients) =
      coefficients := by
  rw [regularFrameGaugeCoefficientTransition_comp, regularFrameGaugeCoefficientTransition_refl]

/-- Frame evaluation and reconstruction form a real-linear equivalence. -/
def regularFrameGaugePotentialCoefficientLinearEquiv
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    SmoothAbelianGaugePotential period hPeriod ≃ₗ[Real] GaugeCoefficients period hPeriod where
  toLinearMap := gaugePotentialFrameCoefficientsLinearMap period hPeriod metric
  invFun := regularFrameGaugePotentialFromCoefficients period hPeriod metric
  left_inv := regularFrameGaugePotentialFromCoefficients_frameCoefficients period hPeriod metric
  right_inv := gaugePotentialFrameCoefficients_reconstructed period hPeriod metric

/-- The exact change of smooth coefficient packets is invertible and linear. -/
def regularFrameGaugeCoefficientTransitionLinearEquiv
    (oldMetric newMetric : RegularGeneralLorentzMetric period hPeriod) :
    GaugeCoefficients period hPeriod ≃ₗ[Real] GaugeCoefficients period hPeriod :=
  (regularFrameGaugePotentialCoefficientLinearEquiv period hPeriod oldMetric).symm.trans
    (regularFrameGaugePotentialCoefficientLinearEquiv period hPeriod newMetric)

@[simp]
theorem regularFrameGaugeCoefficientTransitionLinearEquiv_apply
    (oldMetric newMetric : RegularGeneralLorentzMetric period hPeriod)
    (coefficients : GaugeCoefficients period hPeriod) :
    regularFrameGaugeCoefficientTransitionLinearEquiv period hPeriod oldMetric newMetric coefficients =
      regularFrameGaugeCoefficientTransition period hPeriod oldMetric newMetric coefficients := rfl

/-- Columns are the new frame vectors expressed in the old frame. -/
def regularFrameGaugeCoefficientTransitionMatrixAt
    (oldMetric newMetric : RegularGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod) : Matrix (Fin 4) (Fin 4) Real :=
  fun oldIndex newIndex =>
    (oldMetric.frameEquiv point).symm (newMetric.frame newIndex point) oldIndex

private theorem newFrame_eq_transition_sum
    (oldMetric newMetric : RegularGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod) (newIndex : Fin 4) :
    newMetric.frame newIndex point =
      ∑ oldIndex : Fin 4,
        regularFrameGaugeCoefficientTransitionMatrixAt period hPeriod oldMetric newMetric
          point oldIndex newIndex • oldMetric.frame oldIndex point := by
  let coordinates := (oldMetric.frameEquiv point).symm (newMetric.frame newIndex point)
  have hCoordinates : coordinates =
      ∑ oldIndex : Fin 4, coordinates oldIndex • (Pi.basisFun Real (Fin 4)) oldIndex := by
    exact ((Pi.basisFun Real (Fin 4)).sum_repr coordinates).symm
  calc
    _ = oldMetric.frameEquiv point coordinates :=
      ((oldMetric.frameEquiv point).apply_symm_apply _).symm
    _ = oldMetric.frameEquiv point
        (∑ oldIndex : Fin 4, coordinates oldIndex • (Pi.basisFun Real (Fin 4)) oldIndex) := by
      rw [← hCoordinates]
    _ = _ := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro oldIndex _
      rw [map_smul]
      exact congrArg (coordinates oldIndex • ·)
        (oldMetric.frame_eq_basisFun period hPeriod point oldIndex).symm

/-- The packet transition is the transpose matrix action `a_new = Cᵀ a_old`. -/
theorem regularFrameGaugeCoefficientTransition_apply
    (oldMetric newMetric : RegularGeneralLorentzMetric period hPeriod)
    (coefficients : GaugeCoefficients period hPeriod)
    (point : EffectiveQuotient period hPeriod) (newIndex : Fin 4) (component : Fin 2) :
    regularFrameGaugeCoefficientTransition period hPeriod oldMetric newMetric coefficients
        point (newIndex, component) =
      ∑ oldIndex : Fin 4,
        regularFrameGaugeCoefficientTransitionMatrixAt period hPeriod oldMetric newMetric
          point oldIndex newIndex * coefficients point (oldIndex, component) := by
  unfold regularFrameGaugeCoefficientTransition
  rw [gaugePotentialFrameCoefficients_apply,
    newFrame_eq_transition_sum period hPeriod oldMetric newMetric point newIndex, map_sum]
  apply Finset.sum_congr rfl
  intro oldIndex _
  rw [map_smul]
  change _ * regularFrameGaugeCovectorFromCoefficients period hPeriod oldMetric coefficients
      component point (oldMetric.frame oldIndex point) = _
  rw [regularFrameGaugeCovectorFromCoefficients_frame]

end
end P0EFTJanusRegularFrameGaugeCoefficientTransition4D
end JanusFormal
