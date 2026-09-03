import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusLocalMaxwellEulerBoundary4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusConformalFrameFreeMaxwellHessian4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartMaxwell4D

/-! # Local Euler--boundary form of the regular intrinsic Maxwell variation -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongMaxwellLocalEulerBoundary4D

set_option autoImplicit false

noncomputable section

open scoped BigOperators Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusIntrinsicAbelianMaxwellCurvature4D
open P0EFTJanusMappingTorusIntrinsicAbelianMaxwellAction4D
open P0EFTJanusMappingTorusConformalFrameFreeMaxwellHessian4D
open P0EFTJanusMappingTorusLocalMaxwellStressVariation4D
open P0EFTJanusMappingTorusLocalMaxwellEulerBoundary4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartMaxwell4D

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

/-- Coordinate vector of a potential variation in one holonomic chart. -/
def regularIntrinsicMaxwellLocalPotentialCoordinates
    (variation : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) :
    Vector4 → Vector4 :=
  fun coordinate index =>
    localGaugeOneForm period hPeriod variation component patch coordinate
      (fun _ : Fin 1 => Pi.single index 1)

/-- Local volume field attached to a regular metric. -/
def regularIntrinsicMaxwellLocalVolumeField
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) : Vector4 → Real :=
  fun coordinate => metric.volume (patch.coordinateMap coordinate)

/-- Local inverse-metric field attached to a regular metric. -/
def regularIntrinsicMaxwellLocalInverseField
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) : Vector4 → Matrix4 :=
  fun coordinate =>
    (localMetricMatrix period hPeriod metric.metric patch coordinate)⁻¹

/-- Local curvature field of an intrinsic Maxwell potential. -/
def regularIntrinsicMaxwellLocalCurvatureField
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) :
    Fin 2 → Vector4 → Matrix4 :=
  fun component coordinate =>
    localGaugeCurvatureMatrix period hPeriod potential component patch coordinate

/-- Densitized local Maxwell excitation. -/
def regularIntrinsicMaxwellLocalExcitationField
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) :
    Fin 2 → Vector4 → Matrix4 :=
  maxwellExcitationField
    (regularIntrinsicMaxwellLocalVolumeField period hPeriod metric patch)
    (regularIntrinsicMaxwellLocalInverseField period hPeriod metric patch)
    (regularIntrinsicMaxwellLocalCurvatureField period hPeriod potential patch)

private theorem extDeriv_oneForm_apply_twoVectorFields
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (oneForm : E → E [⋀^Fin 1]→L[Real] Real)
    (first second : E → E) (point : E)
    (hForm : DifferentiableAt Real oneForm point)
    (hFirst : DifferentiableAt Real first point)
    (hSecond : DifferentiableAt Real second point) :
    extDeriv oneForm point ![first point, second point] =
      fderiv Real (fun current => oneForm current (fun _ => second current))
          point (first point) -
        fderiv Real (fun current => oneForm current (fun _ => first current))
          point (second point) -
        oneForm point
          (fun _ => VectorField.lieBracket Real first second point) := by
  let fields : Fin 2 → E → E := ![first, second]
  have hVectors :
      (![first point, second point] : Fin 2 → E) = (fields · point) := by
    funext index
    fin_cases index <;> rfl
  rw [hVectors]
  rw [extDeriv_apply_vectorField
      (n := 0) (x := point) (F := Real)
      (V := fields) hForm (by
        intro index
        fin_cases index
        · exact hFirst
        · exact hSecond)]
  simp [fields, Fin.sum_univ_two]
  have hIci : Finset.Ici (0 : Fin 1) = Finset.univ := by
    ext index
    fin_cases index
    simp
  rw [hIci]
  simp only [Fin.sum_univ_one]
  have hRemoved (current : E) :
      Fin.removeNth (1 : Fin 2)
          (Matrix.vecCons (first current)
            (fun _ : Fin 1 => second current)) =
        (fun _ : Fin 1 => first current) := by
    funext index
    fin_cases index
    rfl
  simp_rw [hRemoved]
  have hBracket :
      Matrix.vecCons (VectorField.lieBracket Real first second point)
          (Fin.removeNth (0 : Fin 1)
            (fun _ : Fin 1 => second point)) =
        (fun _ : Fin 1 =>
          VectorField.lieBracket Real first second point) := by
    funext index
    fin_cases index
    rfl
  rw [hBracket]
  ring

/-- The curvature matrix of the variation is its coordinate curl. -/
theorem regularIntrinsicMaxwellLocalCurvature_eq_gaugeCurvatureVelocity
    (variation : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) (first second : Index4) :
    gaugeCurvatureVelocity
        (regularIntrinsicMaxwellLocalPotentialCoordinates period hPeriod
          variation component patch)
        coordinate first second =
      localGaugeCurvatureMatrix period hPeriod variation component patch
        coordinate first second := by
  let oneForm := localGaugeOneForm period hPeriod variation component patch
  let firstField : Vector4 → Vector4 := fun _ => Pi.single first 1
  let secondField : Vector4 → Vector4 := fun _ => Pi.single second 1
  have hForm : DifferentiableAt Real oneForm coordinate :=
    (localGaugeOneForm_contDiff period hPeriod variation component patch)
      |>.differentiable (by simp) coordinate
  have hFirst : DifferentiableAt Real firstField coordinate :=
    differentiableAt_const (Pi.single first 1)
  have hSecond : DifferentiableAt Real secondField coordinate :=
    differentiableAt_const (Pi.single second 1)
  have hFormula := extDeriv_oneForm_apply_twoVectorFields oneForm firstField
    secondField coordinate hForm hFirst hSecond
  have hBracket :
      VectorField.lieBracket Real firstField secondField coordinate = 0 := by
    simp [firstField, secondField, VectorField.lieBracket]
  rw [hBracket] at hFormula
  have hOneFormZero :
      oneForm coordinate (fun _ : Fin 1 => (0 : Vector4)) = 0 := by
    exact (oneForm coordinate).map_zero
  rw [hOneFormZero, sub_zero] at hFormula
  change
    fderiv Real
          (fun current =>
            localGaugeOneForm period hPeriod variation component patch current
              (fun _ => Pi.single second 1))
          coordinate (Pi.single first 1) -
        fderiv Real
          (fun current =>
            localGaugeOneForm period hPeriod variation component patch current
              (fun _ => Pi.single first 1))
          coordinate (Pi.single second 1) =
      localGaugeCurvature period hPeriod variation component patch coordinate
        ![Pi.single first 1, Pi.single second 1]
  exact hFormula.symm

/-- The regular intrinsic first-variation density is the usual local gauge
variation before integration by parts. -/
theorem regularMaxwellFirstVariationField_eq_localGaugeVariation
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    regularMaxwellFirstVariationField period hPeriod metric
        (regularIntrinsicMaxwellLineOfPotentials period hPeriod metric
          potential variation)
        (patch.coordinateMap coordinate) =
      localMaxwellGaugeVariation
        (metric.volume (patch.coordinateMap coordinate))
        ((localMetricMatrix period hPeriod metric.metric patch coordinate)⁻¹)
        (fun component => localGaugeCurvatureMatrix period hPeriod potential
          component patch coordinate)
        (fun component => localGaugeCurvatureMatrix period hPeriod variation
          component patch coordinate) := by
  change metric.volume (patch.coordinateMap coordinate) *
      (-(1 / 4 : Real) *
        (globalMaxwellPairing period hPeriod metric.metric variation potential
            (patch.coordinateMap coordinate) +
          globalMaxwellPairing period hPeriod metric.metric potential variation
            (patch.coordinateMap coordinate))) = _
  rw [globalMaxwellPairing_eq_local, globalMaxwellPairing_eq_local]
  unfold localMaxwellGaugeVariation maxwellGaugePairingVelocityAt
    localMaxwellPairing
  simp_rw [mul_add, Finset.sum_add_distrib]
  ring

/-- Exact raw excitation form of the regular intrinsic first variation. -/
theorem regularMaxwellFirstVariationField_eq_sum_raw
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    regularMaxwellFirstVariationField period hPeriod metric
        (regularIntrinsicMaxwellLineOfPotentials period hPeriod metric
          potential variation)
        (patch.coordinateMap coordinate) =
      ∑ component : Fin 2,
        rawMaxwellGaugeVariation
          (regularIntrinsicMaxwellLocalExcitationField period hPeriod metric
            potential patch component)
          (regularIntrinsicMaxwellLocalPotentialCoordinates period hPeriod
            variation component patch)
          coordinate := by
  rw [regularMaxwellFirstVariationField_eq_localGaugeVariation]
  have hRaw := localMaxwellGaugeVariation_eq_sum_raw
    (regularIntrinsicMaxwellLocalVolumeField period hPeriod metric patch)
    (regularIntrinsicMaxwellLocalInverseField period hPeriod metric patch)
    (regularIntrinsicMaxwellLocalCurvatureField period hPeriod potential patch)
    (fun component =>
      regularIntrinsicMaxwellLocalPotentialCoordinates period hPeriod
        variation component patch)
    coordinate
    (fun first second => by
      have hSymmetric := congrFun (congrFun
        (localFixedSignMetric period hPeriod metric.metric patch coordinate
          ).inverse_symmetric second) first
      simpa [regularIntrinsicMaxwellLocalInverseField,
        localFixedSignMetric] using hSymmetric)
  have hVelocity :
      (fun component =>
        gaugeCurvatureVelocity
          (regularIntrinsicMaxwellLocalPotentialCoordinates period hPeriod
            variation component patch) coordinate) =
        fun component => localGaugeCurvatureMatrix period hPeriod variation
          component patch coordinate := by
    funext component
    ext first second
    exact regularIntrinsicMaxwellLocalCurvature_eq_gaugeCurvatureVelocity
      period hPeriod variation component patch coordinate first second
  rw [hVelocity] at hRaw
  simpa [regularIntrinsicMaxwellLocalVolumeField,
    regularIntrinsicMaxwellLocalInverseField,
    regularIntrinsicMaxwellLocalCurvatureField,
    regularIntrinsicMaxwellLocalExcitationField] using hRaw

theorem regularIntrinsicMaxwellLocalPotentialCoordinates_entry_contDiff
    (variation : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (index : Index4) :
    ContDiff Real ∞ (fun coordinate =>
      regularIntrinsicMaxwellLocalPotentialCoordinates period hPeriod variation
        component patch coordinate index) := by
  let vector : Fin 1 → Vector4 := fun _ => Pi.single index 1
  change ContDiff Real ∞ (fun coordinate =>
    localGaugeOneForm period hPeriod variation component patch coordinate vector)
  exact
    (ContinuousAlternatingMap.apply Real Vector4 Real vector).contDiff.comp
      (localGaugeOneForm_contDiff period hPeriod variation component patch)

theorem regularIntrinsicMaxwellLocalExcitationField_entry_contDiff
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (first second : Index4) :
    ContDiff Real ∞ (fun coordinate =>
      regularIntrinsicMaxwellLocalExcitationField period hPeriod metric
        potential patch component coordinate first second) := by
  have hVolume : ContDiff Real ∞ (fun coordinate =>
      metric.volume (patch.coordinateMap coordinate)) :=
    (metric.volume.contMDiff_toFun.comp patch.coordinateMap_contMDiff).contDiff
  unfold regularIntrinsicMaxwellLocalExcitationField maxwellExcitationField
    maxwellExcitationAt regularIntrinsicMaxwellLocalVolumeField
    regularIntrinsicMaxwellLocalInverseField
    regularIntrinsicMaxwellLocalCurvatureField
  apply hVolume.mul
  apply ContDiff.sum
  intro lowerFirst _
  apply ContDiff.sum
  intro lowerSecond _
  exact
    ((localMetricInverseEntry_contDiff period hPeriod metric.metric patch first
        lowerFirst).mul
      (localMetricInverseEntry_contDiff period hPeriod metric.metric patch second
        lowerSecond)).mul
      (localGaugeCurvatureMatrix_entry_contDiff period hPeriod potential
        component patch lowerFirst lowerSecond)

theorem regularIntrinsicMaxwellLocalExcitationField_skew
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) (first second : Index4) :
    regularIntrinsicMaxwellLocalExcitationField period hPeriod metric potential
        patch component coordinate second first =
      -regularIntrinsicMaxwellLocalExcitationField period hPeriod metric potential
        patch component coordinate first second := by
  have hCurvature : ∀ first second,
      localGaugeCurvatureMatrix period hPeriod potential component patch
          coordinate second first =
        -localGaugeCurvatureMatrix period hPeriod potential component patch
          coordinate first second := by
    intro left right
    exact congrFun (congrFun
      (localGaugeCurvatureMatrix_transpose period hPeriod potential component
        patch coordinate) left) right
  have hSkew := maxwellExcitationAt_skew
    (regularIntrinsicMaxwellLocalVolumeField period hPeriod metric patch
      coordinate)
    (regularIntrinsicMaxwellLocalInverseField period hPeriod metric patch
      coordinate)
    (regularIntrinsicMaxwellLocalCurvatureField period hPeriod potential patch
      component coordinate) hCurvature
  simpa [regularIntrinsicMaxwellLocalExcitationField, maxwellExcitationField]
    using congrFun (congrFun hSkew first) second

/-- Exact local integration-by-parts form of the regular intrinsic Maxwell
first-variation density. -/
theorem regular_maxwell_first_variation_field_eq_euler_sub_boundary_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    regularMaxwellFirstVariationField period hPeriod metric
        (regularIntrinsicMaxwellLineOfPotentials period hPeriod metric
          potential variation)
        (patch.coordinateMap coordinate) =
      ∑ component : Fin 2,
        (maxwellEulerPairing
            (regularIntrinsicMaxwellLocalExcitationField period hPeriod metric
              potential patch component)
            (regularIntrinsicMaxwellLocalPotentialCoordinates period hPeriod
              variation component patch)
            coordinate -
          maxwellBoundaryDivergence
            (regularIntrinsicMaxwellLocalExcitationField period hPeriod metric
              potential patch component)
            (regularIntrinsicMaxwellLocalPotentialCoordinates period hPeriod
              variation component patch)
            coordinate) := by
  rw [regularMaxwellFirstVariationField_eq_sum_raw]
  apply Finset.sum_congr rfl
  intro component _
  exact rawMaxwellGaugeVariation_eq_euler_sub_boundaryDivergence
    (regularIntrinsicMaxwellLocalExcitationField period hPeriod metric
      potential patch component)
    (regularIntrinsicMaxwellLocalPotentialCoordinates period hPeriod variation
      component patch)
    coordinate
    (fun first second =>
      (regularIntrinsicMaxwellLocalExcitationField_entry_contDiff period hPeriod
        metric potential component patch first second).differentiable
          (by simp) coordinate)
    (fun second =>
      (regularIntrinsicMaxwellLocalPotentialCoordinates_entry_contDiff period
        hPeriod variation component patch second).differentiable
          (by simp) coordinate)
    (regularIntrinsicMaxwellLocalExcitationField_skew period hPeriod metric
      potential component patch coordinate)

end

end P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongMaxwellLocalEulerBoundary4D
end JanusFormal
