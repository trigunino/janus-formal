import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMaxwellDensityConnectionJet4D

/-! # Concrete holonomic Maxwell density-divergence identity -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularHolonomicMaxwellDensityDivergence4D

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section

open scoped BigOperators Manifold ContDiff Matrix
open P0EFTJanusMetricCoupledScalarMatterJetVariation
open P0EFTJanusMetricInducedScalarStressVariation4D
open P0EFTJanusScalarStressCoordinateConnectionJet4D
open P0EFTJanusScalarStressLeviCivitaConnectionJet4D
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalInverseDerivative4D
open P0EFTJanusMappingTorusGeneralMetricSymmetricTensorCovariantDerivative4D
open P0EFTJanusMappingTorusGeneralMetricSymmetricTensorDivergence4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusIntrinsicAbelianMaxwellCurvature4D
open P0EFTJanusMappingTorusIntrinsicAbelianMaxwellAction4D
open P0EFTJanusMappingTorusConformalFrameFreeMaxwellHessian4D
open P0EFTJanusMappingTorusLocalMaxwellStressVariation4D
open P0EFTJanusMappingTorusLocalMaxwellEulerBoundary4D
open P0EFTJanusProgramPRegularFrameHolonomicMaxwellDensityBridge4D
open P0EFTJanusProgramPRegularGeneralMetricGlobalMaxwellDivergence4D
open P0EFTJanusProgramPRegularGlobalGaugeCurvatureHolonomicCoefficient4D
open P0EFTJanusMappingTorusLocalMetricVolumeChristoffelTrace4D
open P0EFTJanusMaxwellDensityConnectionJet4D

variable (period : Real) (hPeriod : period ≠ 0)

abbrev Index4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Index4
abbrev Vector4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4
abbrev Matrix4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Matrix4

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- The genuine local Levi--Civita data bundled in the finite connection-jet
interface used by Gate 429. -/
def regularLocalLeviCivitaConnectionJet
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) : MetricCompatibleTorsionFreeConnectionJet4 :=
  leviCivitaConnectionJet
    (localFixedSignMetric period hPeriod metric.metric patch coordinate)
    (localMetricDerivative period hPeriod metric.metric patch coordinate)
    (fun derivative first second =>
      localMetricDerivative_symmetric period hPeriod metric.metric patch
        coordinate derivative first second)

/-- Actual coordinate derivative of the metric volume. -/
def regularLocalMetricVolumeDerivative
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) (derivative : Index4) : Real :=
  fderiv Real (localMetricVolumeFactor period hPeriod metric.metric patch)
    coordinate (Pi.single derivative 1)

/-- Actual coordinate derivative of the local gauge-curvature matrix. -/
def regularLocalGaugeCurvatureDerivative
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) (derivative : Index4) : Matrix4 :=
  fun first second =>
    fderiv Real
      (fun current =>
        localGaugeCurvatureMatrix period hPeriod potential component patch
          current first second)
      coordinate (Pi.single derivative 1)

theorem regularLocalMetricVolumeDerivative_eq_connectionTrace
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) (derivative : Index4) :
    regularLocalMetricVolumeDerivative period hPeriod metric patch coordinate
        derivative =
      localMetricVolumeFactor period hPeriod metric.metric patch coordinate *
        ∑ contracted : Index4,
          (regularLocalLeviCivitaConnectionJet period hPeriod metric patch
            coordinate).christoffel contracted derivative contracted := by
  exact localMetricVolumeFactor_fderiv_basis_eq_christoffelTrace period hPeriod
    metric.metric patch coordinate derivative

theorem regularLocalInverseMetricDerivative_eq_connection
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) (derivative first second : Index4) :
    fderiv Real
        (fun current =>
          (localMetricMatrix period hPeriod metric.metric patch current)⁻¹
            first second)
        coordinate (Pi.single derivative 1) =
      (regularLocalLeviCivitaConnectionJet period hPeriod metric patch
        coordinate).inverseMetricDerivative derivative first second := by
  rw [show (fun current =>
        (localMetricMatrix period hPeriod metric.metric patch current)⁻¹
          first second) =
      fun current =>
        Ring.inverse (localMetricMatrix period hPeriod metric.metric patch current)
          first second by
    funext current
    exact congrFun (congrFun
      (Matrix.nonsing_inv_eq_ringInverse
        (A := localMetricMatrix period hPeriod metric.metric patch current))
      first) second]
  rw [localMetricInverseEntry_fderiv_basis,
    localActualInverseMetricDerivative_apply]
  rfl

/-- The actual `fderiv` of each holonomic excitation entry realizes exactly
the product-rule jet of Gate 429. -/
theorem regularHolonomicMaxwellExcitationField_coordinatePartial
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) (derivative first second : Index4) :
    coordinatePartial
        (fun current =>
          regularHolonomicMaxwellExcitationField period hPeriod metric potential
            patch component current first second)
        coordinate derivative =
      maxwellDensitizedRaisedCurvatureDerivativeAt
        (regularLocalLeviCivitaConnectionJet period hPeriod metric patch
          coordinate)
        (localMetricVolumeFactor period hPeriod metric.metric patch coordinate)
        (regularLocalMetricVolumeDerivative period hPeriod metric patch coordinate)
        (localGaugeCurvatureMatrix period hPeriod potential component patch
          coordinate)
        (regularLocalGaugeCurvatureDerivative period hPeriod potential component
          patch coordinate)
        derivative first second := by
  let volumeField := localMetricVolumeFactor period hPeriod metric.metric patch
  let inverseField := fun current =>
    (localMetricMatrix period hPeriod metric.metric patch current)⁻¹
  let curvatureField :=
    localGaugeCurvatureMatrix period hPeriod potential component patch
  let raisedEntry := fun current =>
    ∑ lowerFirst : Index4, ∑ lowerSecond : Index4,
      inverseField current first lowerFirst *
        inverseField current second lowerSecond *
        curvatureField current lowerFirst lowerSecond
  have hVolume : DifferentiableAt Real volumeField coordinate :=
    (localMetricVolumeFactor_contDiff period hPeriod metric.metric patch)
      |>.differentiable (by simp) coordinate
  have hInverse (left right : Index4) : DifferentiableAt Real
      (fun current => inverseField current left right) coordinate :=
    (localMetricInverseEntry_contDiff period hPeriod metric.metric patch left
      right).differentiable (by simp) coordinate
  have hCurvature (left right : Index4) : DifferentiableAt Real
      (fun current => curvatureField current left right) coordinate :=
    (localGaugeCurvatureMatrix_entry_contDiff period hPeriod potential component
      patch left right).differentiable (by simp) coordinate
  have hSummand (lowerFirst lowerSecond : Index4) : DifferentiableAt Real
      (fun current =>
        inverseField current first lowerFirst *
          inverseField current second lowerSecond *
          curvatureField current lowerFirst lowerSecond) coordinate :=
    ((hInverse first lowerFirst).mul (hInverse second lowerSecond)).mul
      (hCurvature lowerFirst lowerSecond)
  have hRaised : DifferentiableAt Real raisedEntry coordinate := by
    apply DifferentiableAt.fun_sum
    intro lowerFirst _
    apply DifferentiableAt.fun_sum
    intro lowerSecond _
    exact hSummand lowerFirst lowerSecond
  have hSummandDerivative (lowerFirst lowerSecond : Index4) :
      fderiv Real
          (fun current =>
            inverseField current first lowerFirst *
              inverseField current second lowerSecond *
              curvatureField current lowerFirst lowerSecond)
          coordinate (Pi.single derivative 1) =
        (regularLocalLeviCivitaConnectionJet period hPeriod metric patch
              coordinate).inverseMetricDerivative derivative first lowerFirst *
            inverseField coordinate second lowerSecond *
            curvatureField coordinate lowerFirst lowerSecond +
          inverseField coordinate first lowerFirst *
              (regularLocalLeviCivitaConnectionJet period hPeriod metric patch
                coordinate).inverseMetricDerivative derivative second lowerSecond *
            curvatureField coordinate lowerFirst lowerSecond +
          inverseField coordinate first lowerFirst *
            inverseField coordinate second lowerSecond *
            regularLocalGaugeCurvatureDerivative period hPeriod potential
              component patch coordinate derivative lowerFirst lowerSecond := by
    change (fderiv Real
        ((fun current => inverseField current first lowerFirst) *
          (fun current => inverseField current second lowerSecond) *
          fun current => curvatureField current lowerFirst lowerSecond)
        coordinate) (Pi.single derivative 1) = _
    rw [fderiv_mul ((hInverse first lowerFirst).mul
        (hInverse second lowerSecond)) (hCurvature lowerFirst lowerSecond),
      fderiv_mul (hInverse first lowerFirst) (hInverse second lowerSecond)]
    simp only [add_apply, smul_apply, smul_eq_mul, Pi.mul_apply]
    rw [regularLocalInverseMetricDerivative_eq_connection,
      regularLocalInverseMetricDerivative_eq_connection]
    unfold regularLocalGaugeCurvatureDerivative curvatureField
    ring
  have hRaisedDerivative :
      fderiv Real raisedEntry coordinate (Pi.single derivative 1) =
        ∑ lowerFirst : Index4, ∑ lowerSecond : Index4,
          (((regularLocalLeviCivitaConnectionJet period hPeriod metric patch
                coordinate).inverseMetricDerivative derivative first lowerFirst *
              inverseField coordinate second lowerSecond *
              curvatureField coordinate lowerFirst lowerSecond +
            inverseField coordinate first lowerFirst *
                (regularLocalLeviCivitaConnectionJet period hPeriod metric patch
                  coordinate).inverseMetricDerivative derivative second
                    lowerSecond *
              curvatureField coordinate lowerFirst lowerSecond) +
            inverseField coordinate first lowerFirst *
              inverseField coordinate second lowerSecond *
              regularLocalGaugeCurvatureDerivative period hPeriod potential
                component patch coordinate derivative lowerFirst lowerSecond) := by
    have hOuter := fderiv_fun_sum (𝕜 := Real) (x := coordinate)
      (u := Finset.univ)
      (A := fun lowerFirst current => ∑ lowerSecond : Index4,
        inverseField current first lowerFirst *
          inverseField current second lowerSecond *
          curvatureField current lowerFirst lowerSecond)
      (fun lowerFirst _ => by
        apply DifferentiableAt.fun_sum
        intro lowerSecond _
        exact hSummand lowerFirst lowerSecond)
    have hOuterApply := congrArg
      (fun derivativeMap : Vector4 →L[Real] Real =>
        derivativeMap (Pi.single derivative 1)) hOuter
    rw [show raisedEntry = fun current => ∑ lowerFirst : Index4,
        ∑ lowerSecond : Index4,
          inverseField current first lowerFirst *
            inverseField current second lowerSecond *
            curvatureField current lowerFirst lowerSecond by rfl]
    rw [hOuterApply]
    simp only [sum_apply]
    apply Finset.sum_congr rfl
    intro lowerFirst _
    have hInner := fderiv_fun_sum (𝕜 := Real) (x := coordinate)
      (u := Finset.univ)
      (A := fun lowerSecond current =>
        inverseField current first lowerFirst *
          inverseField current second lowerSecond *
          curvatureField current lowerFirst lowerSecond)
      (fun lowerSecond _ => hSummand lowerFirst lowerSecond)
    have hInnerApply := congrArg
      (fun derivativeMap : Vector4 →L[Real] Real =>
        derivativeMap (Pi.single derivative 1)) hInner
    rw [hInnerApply]
    simp only [sum_apply]
    apply Finset.sum_congr rfl
    intro lowerSecond _
    exact hSummandDerivative lowerFirst lowerSecond
  unfold coordinatePartial regularHolonomicMaxwellExcitationField
    maxwellExcitationField maxwellExcitationAt
  change fderiv Real (volumeField * raisedEntry) coordinate
      (Pi.single derivative 1) = _
  have hProduct := congrArg
    (fun derivativeMap : Vector4 →L[Real] Real =>
      derivativeMap (Pi.single derivative 1))
    (fderiv_mul hVolume hRaised)
  rw [hProduct]
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [hRaisedDerivative]
  unfold maxwellDensitizedRaisedCurvatureDerivativeAt
  dsimp only [regularLocalLeviCivitaConnectionJet, leviCivitaConnectionJet,
    localFixedSignMetric, regularLocalMetricVolumeDerivative, volumeField,
    inverseField, curvatureField, raisedEntry]
  ring

/-- The finite covariant-curvature derivative is the actual local covariant
derivative of the reconstructed global tensor. -/
theorem regularLocalMaxwellCovariantCurvatureDerivative_eq_global
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) (derivative first second : Index4) :
    maxwellCovariantCurvatureDerivativeAt
        (regularLocalLeviCivitaConnectionJet period hPeriod metric patch
          coordinate)
        (localGaugeCurvatureMatrix period hPeriod potential component patch
          coordinate)
        (regularLocalGaugeCurvatureDerivative period hPeriod potential component
          patch coordinate)
        derivative first second =
      localSymmetricTensorCovariantDerivative period hPeriod metric.metric
        (regularGlobalGaugeCurvatureTensor period hPeriod metric potential
          component)
        patch coordinate derivative first second := by
  unfold maxwellCovariantCurvatureDerivativeAt
    regularLocalGaugeCurvatureDerivative
    localSymmetricTensorCovariantDerivative
  rw [regularGlobalGaugeCurvatureTensor_localDerivative]
  simp_rw [regularGlobalGaugeCurvatureTensor_localCoefficient]
  rfl

theorem regularLocalMaxwellRaisedCovariantDivergence_eq_global
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) (second : Index4) :
    maxwellRaisedCovariantDivergenceAt
        (regularLocalLeviCivitaConnectionJet period hPeriod metric patch
          coordinate)
        (localGaugeCurvatureMatrix period hPeriod potential component patch
          coordinate)
        (regularLocalGaugeCurvatureDerivative period hPeriod potential component
          patch coordinate)
        second =
      ∑ lowerSecond : Index4,
        (localMetricMatrix period hPeriod metric.metric patch coordinate)⁻¹
            second lowerSecond *
          localSymmetricTensorDivergenceCoefficient period hPeriod metric.metric
            (regularGlobalGaugeCurvatureTensor period hPeriod metric potential
              component)
            patch coordinate lowerSecond := by
  unfold maxwellRaisedCovariantDivergenceAt
    localSymmetricTensorDivergenceCoefficient
  simp_rw [regularLocalMaxwellCovariantCurvatureDerivative_eq_global]
  rfl

/-- Concrete density-divergence bridge: the Euler coefficient built from the
holonomic Maxwell excitation is the metric volume times the raised intrinsic
Maxwell divergence. -/
theorem regularHolonomicMaxwellEulerCoefficient_eq_volume_mul_raisedDivergence
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) (second : Index4) :
    maxwellEulerCoefficient
        (regularHolonomicMaxwellExcitationField period hPeriod metric potential
          patch component)
        coordinate second =
      localMetricVolumeFactor period hPeriod metric.metric patch coordinate *
        ∑ lowerSecond : Index4,
          (localMetricMatrix period hPeriod metric.metric patch coordinate)⁻¹
              second lowerSecond *
            localSymmetricTensorDivergenceCoefficient period hPeriod metric.metric
              (regularGlobalGaugeCurvatureTensor period hPeriod metric potential
                component)
              patch coordinate lowerSecond := by
  have hEuler :
      maxwellEulerCoefficient
          (regularHolonomicMaxwellExcitationField period hPeriod metric potential
            patch component)
          coordinate second =
        maxwellDensitizedRaisedDivergenceAt
          (regularLocalLeviCivitaConnectionJet period hPeriod metric patch
            coordinate)
          (localMetricVolumeFactor period hPeriod metric.metric patch coordinate)
          (regularLocalMetricVolumeDerivative period hPeriod metric patch
            coordinate)
          (localGaugeCurvatureMatrix period hPeriod potential component patch
            coordinate)
          (regularLocalGaugeCurvatureDerivative period hPeriod potential component
            patch coordinate)
          second := by
    unfold maxwellEulerCoefficient maxwellDensitizedRaisedDivergenceAt
    apply Finset.sum_congr rfl
    intro derivative _
    exact regularHolonomicMaxwellExcitationField_coordinatePartial period hPeriod
      metric potential component patch coordinate derivative derivative second
  rw [hEuler,
    maxwellDensitizedRaisedDivergence_eq_volume_mul_covariant,
    regularLocalMaxwellRaisedCovariantDivergence_eq_global]
  exact regularLocalMetricVolumeDerivative_eq_connectionTrace period hPeriod
    metric patch coordinate
  intro first secondIndex
  exact congrFun (congrFun
    (localGaugeCurvatureMatrix_transpose period hPeriod potential component patch
      coordinate) first) secondIndex

/-- Gate marker for the concrete local Euler/intrinsic-divergence identity. -/
theorem regular_holonomic_maxwell_density_divergence_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod) :
    ∀ (component : Fin 2)
        (patch : SmoothHolonomicFrameChart4 period hPeriod)
        (coordinate : Vector4) (second : Index4),
      maxwellEulerCoefficient
          (regularHolonomicMaxwellExcitationField period hPeriod metric potential
            patch component)
          coordinate second =
        localMetricVolumeFactor period hPeriod metric.metric patch coordinate *
          ∑ lowerSecond : Index4,
            (localMetricMatrix period hPeriod metric.metric patch coordinate)⁻¹
                second lowerSecond *
              localSymmetricTensorDivergenceCoefficient period hPeriod
                metric.metric
                (regularGlobalGaugeCurvatureTensor period hPeriod metric potential
                  component)
                patch coordinate lowerSecond :=
  regularHolonomicMaxwellEulerCoefficient_eq_volume_mul_raisedDivergence
    period hPeriod metric potential

end
end P0EFTJanusProgramPRegularHolonomicMaxwellDensityDivergence4D
end JanusFormal
