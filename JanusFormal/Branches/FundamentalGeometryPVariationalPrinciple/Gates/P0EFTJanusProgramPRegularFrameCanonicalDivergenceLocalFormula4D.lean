import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularFrameCanonicalDivergenceObstruction4D

/-!
# Local formula for the regular-frame canonical divergence

Every smooth tangent field is pulled into a holonomic chart by expanding it
in the genuine regular frame.  The ordinary weighted coordinate divergence
of that pullback is shown to equal the global algebraic canonical divergence.
Thus the ten global generator residuals become ten explicit local weighted
divergence equations.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularFrameCanonicalDivergenceLocalFormula4D

set_option autoImplicit false
set_option maxHeartbeats 2400000

noncomputable section

open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
open P0EFTJanusMappingTorusCanonicalTotalR4BallParametrization4D
open P0EFTJanusProgramPRegularFrameMaxwellCurvatureBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularFrameEinsteinHilbertFrameFreeActionMeasureBridge4D
open P0EFTJanusProgramPRegularFrameLocalMetricDivergence4D
open P0EFTJanusProgramPRegularFrameCanonicalDivergenceGluing4D
open P0EFTJanusProgramPRegularFrameCanonicalDivergenceLaw4D
open P0EFTJanusProgramPRegularFrameCanonicalDivergenceObstruction4D
open P0EFTJanusMappingTorusCanonicalTenFlowGeneratorDivergence4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev Index4 := Fin 4
private abbrev Vector4 := Index4 → Real

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- Weighted coordinate divergence of an arbitrary coordinate vector field. -/
def holonomicLocalDensityDivergence
    (density : Vector4 → Real)
    (field : Vector4 → Vector4)
    (coordinate : Vector4) : Real :=
  (∑ derivative : Index4,
      fderiv Real
        (fun current => density current * field current derivative)
        coordinate (Pi.single derivative 1)) /
    density coordinate

/-- The pre-existing regular-frame local divergence is the specialization to
one pulled frame vector. -/
theorem holonomicLocalDensityDivergence_pulledRegularFrame
    (density : Vector4 → Real)
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (vector : Index4) (coordinate : Vector4) :
    holonomicLocalDensityDivergence density
        (pulledRegularFrameVector period hPeriod metric patch vector)
        coordinate =
      regularFrameLocalDensityDivergence period hPeriod density metric patch
        vector coordinate :=
  rfl

/-- Exact coordinate Leibniz rule for weighted divergence. -/
theorem holonomicLocalDensityDivergence_smul
    (density scalar : Vector4 → Real)
    (field : Vector4 → Vector4)
    (coordinate : Vector4)
    (hDensity : DifferentiableAt Real density coordinate)
    (hDensityNe : density coordinate ≠ 0)
    (hScalar : DifferentiableAt Real scalar coordinate)
    (hField : DifferentiableAt Real field coordinate) :
    holonomicLocalDensityDivergence density
        (fun current => scalar current • field current) coordinate =
      scalar coordinate *
          holonomicLocalDensityDivergence density field coordinate +
        fderiv Real scalar coordinate (field coordinate) := by
  have hFieldComponent (derivative : Index4) :
      DifferentiableAt Real (fun current => field current derivative)
        coordinate := by
    fun_prop
  have hDensityField (derivative : Index4) :
      DifferentiableAt Real
        (fun current => density current * field current derivative)
        coordinate :=
    hDensity.mul (hFieldComponent derivative)
  have hProduct (derivative : Index4) :
      fderiv Real
          (fun current =>
            density current * (scalar current • field current) derivative)
          coordinate (Pi.single derivative 1) =
        fderiv Real scalar coordinate (Pi.single derivative 1) *
            (density coordinate * field coordinate derivative) +
          scalar coordinate *
            fderiv Real
              (fun current => density current * field current derivative)
              coordinate (Pi.single derivative 1) := by
    have hDerivative := fderiv_mul hScalar (hDensityField derivative)
    have hApply := congrArg
      (fun derivativeMap : Vector4 →L[Real] Real =>
        derivativeMap (Pi.single derivative 1)) hDerivative
    simp only [add_apply, smul_apply, smul_eq_mul] at hApply
    rw [show
      (fun current =>
        density current * (scalar current • field current) derivative) =
        scalar * (fun current => density current * field current derivative) by
      funext current
      simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
      ring]
    rw [hApply]
    ring
  have hAdvection :
      fderiv Real scalar coordinate (field coordinate) =
        ∑ derivative : Index4,
          fderiv Real scalar coordinate (Pi.single derivative 1) *
            field coordinate derivative := by
    conv_lhs => rw [pi_eq_sum_univ' (field coordinate)]
    rw [map_sum]
    simp only [map_smul, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro derivative _hDerivative
    ring
  have hNumerator :
      (∑ derivative : Index4,
          fderiv Real
            (fun current =>
              density current * (scalar current • field current) derivative)
            coordinate (Pi.single derivative 1)) =
        density coordinate *
            fderiv Real scalar coordinate (field coordinate) +
          scalar coordinate *
            ∑ derivative : Index4,
              fderiv Real
                (fun current => density current * field current derivative)
                coordinate (Pi.single derivative 1) := by
    simp_rw [hProduct]
    rw [Finset.sum_add_distrib]
    calc
      (∑ derivative : Index4,
          fderiv Real scalar coordinate (Pi.single derivative 1) *
              (density coordinate * field coordinate derivative)) +
            ∑ derivative : Index4,
              scalar coordinate *
                fderiv Real
                  (fun current => density current * field current derivative)
                  coordinate (Pi.single derivative 1) =
          density coordinate *
              (∑ derivative : Index4,
                fderiv Real scalar coordinate (Pi.single derivative 1) *
                  field coordinate derivative) +
            scalar coordinate *
              ∑ derivative : Index4,
                fderiv Real
                  (fun current => density current * field current derivative)
                  coordinate (Pi.single derivative 1) := by
        congr 1
        · rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro derivative _hDerivative
          ring
        · rw [Finset.mul_sum]
      _ = _ := by rw [← hAdvection]
  unfold holonomicLocalDensityDivergence
  rw [hNumerator]
  field_simp [hDensityNe]
  ring

/-- Weighted coordinate divergence commutes with a finite sum of smooth
coordinate vector fields. -/
theorem holonomicLocalDensityDivergence_finset_sum
    {ι : Type*} (indices : Finset ι)
    (density : Vector4 → Real)
    (fields : ι → Vector4 → Vector4)
    (coordinate : Vector4)
    (hDensity : DifferentiableAt Real density coordinate)
    (hFields : ∀ index ∈ indices,
      DifferentiableAt Real (fields index) coordinate) :
    holonomicLocalDensityDivergence density
        (fun current => ∑ index ∈ indices, fields index current)
        coordinate =
      ∑ index ∈ indices,
        holonomicLocalDensityDivergence density (fields index) coordinate := by
  have hProduct (index : ι) (hIndex : index ∈ indices)
      (derivative : Index4) :
      DifferentiableAt Real
        (fun current => density current * fields index current derivative)
        coordinate := by
    apply hDensity.mul
    have := hFields index hIndex
    fun_prop
  have hDerivative (derivative : Index4) :
      fderiv Real
          (fun current => density current *
            (∑ index ∈ indices, fields index current) derivative)
          coordinate (Pi.single derivative 1) =
        ∑ index ∈ indices,
          fderiv Real
            (fun current => density current * fields index current derivative)
            coordinate (Pi.single derivative 1) := by
    have hFunction :
        (fun current => density current *
          (∑ index ∈ indices, fields index current) derivative) =
        ∑ index ∈ indices, fun current =>
          density current * fields index current derivative := by
      funext current
      simp only [Finset.sum_apply]
      rw [Finset.mul_sum]
    rw [hFunction]
    rw [fderiv_sum
      (u := indices)
      (A := fun index current =>
        density current * fields index current derivative)
      (x := coordinate)
      (fun index hIndex => hProduct index hIndex derivative)]
    simp only [_root_.sum_apply]
  unfold holonomicLocalDensityDivergence
  simp_rw [hDerivative]
  rw [Finset.sum_comm]
  rw [Finset.sum_div]

/-- Pull back a smooth tangent field by its exact regular-frame expansion. -/
def pulledRegularFrameExpansion
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (vector : SmoothTangentField period hPeriod) : Vector4 → Vector4 :=
  fun coordinate => ∑ index : Index4,
    regularFrameCanonicalCoefficient period hPeriod metric vector index
        (patch.coordinateMap coordinate) •
      pulledRegularFrameVector period hPeriod metric patch index coordinate

/-- Tangent-space presentation of the same finite coordinate expansion. -/
def pulledRegularFrameExpansionTangent
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (vector : SmoothTangentField period hPeriod)
    (coordinate : Vector4) :
    TangentSpace (modelWithCornersSelf Real Vector4) coordinate :=
  ∑ index : Index4,
    regularFrameCanonicalCoefficient period hPeriod metric vector index
        (patch.coordinateMap coordinate) •
      (pulledRegularFrameVector period hPeriod metric patch index coordinate :
        TangentSpace (modelWithCornersSelf Real Vector4) coordinate)

/-- The chart differential maps the expanded coordinate field back to the
original intrinsic tangent field. -/
theorem coordinateMap_mfderiv_pulledRegularFrameExpansion
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (vector : SmoothTangentField period hPeriod)
    (coordinate : Vector4) :
    mfderiv (modelWithCornersSelf Real Vector4) coverModelWithCorners
        patch.coordinateMap coordinate
        (pulledRegularFrameExpansionTangent period hPeriod metric patch vector
          coordinate) =
      vector (patch.coordinateMap coordinate) := by
  rw [pulledRegularFrameExpansionTangent]
  change
    mfderiv (modelWithCornersSelf Real Vector4) coverModelWithCorners
        patch.coordinateMap coordinate
        (∑ index : Index4,
          regularFrameCanonicalCoefficient period hPeriod metric vector index
              (patch.coordinateMap coordinate) •
            (pulledRegularFrameVector period hPeriod metric patch index
              coordinate :
              TangentSpace (modelWithCornersSelf Real Vector4) coordinate)) = _
  rw [map_sum]
  calc
    _ = ∑ index : Index4,
        regularFrameCanonicalCoefficient period hPeriod metric vector index
            (patch.coordinateMap coordinate) •
          metric.frame index (patch.coordinateMap coordinate) := by
      apply Finset.sum_congr rfl
      intro index _hIndex
      let coefficient :=
        regularFrameCanonicalCoefficient period hPeriod metric vector index
          (patch.coordinateMap coordinate)
      let coordinateVector :
          TangentSpace (modelWithCornersSelf Real Vector4) coordinate :=
        pulledRegularFrameVector period hPeriod metric patch index coordinate
      let derivativeMap :=
        mfderiv (modelWithCornersSelf Real Vector4) coverModelWithCorners
          patch.coordinateMap coordinate
      have hBasis : derivativeMap coordinateVector =
          metric.frame index (patch.coordinateMap coordinate) := by
        dsimp only [derivativeMap, coordinateVector]
        exact coordinateMap_mfderiv_pulledRegularFrameVector period hPeriod
          metric patch coordinate index
      change derivativeMap (coefficient • coordinateVector) =
        coefficient • metric.frame index (patch.coordinateMap coordinate)
      calc
        derivativeMap (coefficient • coordinateVector) =
            coefficient • derivativeMap coordinateVector := by
          exact map_smul derivativeMap coefficient coordinateVector
        _ = _ := by rw [hBasis]
    _ = _ :=
      (regularFrameCanonicalCoefficient_reconstructs period hPeriod metric
        vector (patch.coordinateMap coordinate)).symm

/-- The expanded coordinate representative is smooth. -/
theorem pulledRegularFrameExpansion_contDiff
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (vector : SmoothTangentField period hPeriod) :
    ContDiff Real ∞
      (pulledRegularFrameExpansion period hPeriod metric patch vector) := by
  unfold pulledRegularFrameExpansion
  apply ContDiff.sum
  intro index _hIndex
  have hCoefficient : ContDiff Real ∞ (fun coordinate =>
      regularFrameCanonicalCoefficient period hPeriod metric vector index
        (patch.coordinateMap coordinate)) :=
    ((regularFrameCanonicalCoefficient period hPeriod metric vector index
      ).contMDiff_toFun.comp patch.coordinateMap_contMDiff).contDiff
  exact hCoefficient.smul
    (pulledRegularFrameVector_contDiff period hPeriod metric patch index)

/-- The global algebraic divergence has the ordinary intrinsic-density
formula in every concrete holonomic chart. -/
theorem regularFrameAlgebraicCanonicalDivergence_local
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hGauge : RegularGeneralMetricInCanonicalVolumeGauge
      period hPeriod metric)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (vector : SmoothTangentField period hPeriod)
    (coordinate : Vector4) :
    regularFrameAlgebraicCanonicalDivergence period hPeriod metric vector
        (patch.coordinateMap coordinate) =
      holonomicLocalDensityDivergence
        (localMetricVolumeFactor period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod) patch)
        (pulledRegularFrameExpansion period hPeriod metric patch vector)
        coordinate := by
  let density := localMetricVolumeFactor period hPeriod
    (intrinsicSmoothGeneralLorentzMetric period hPeriod) patch
  let coefficient : Index4 → Vector4 → Real := fun index current =>
    regularFrameCanonicalCoefficient period hPeriod metric vector index
      (patch.coordinateMap current)
  let term : Index4 → Vector4 → Vector4 := fun index current =>
    coefficient index current •
      pulledRegularFrameVector period hPeriod metric patch index current
  have hDensity : DifferentiableAt Real density coordinate :=
    (localMetricVolumeFactor_contDiff period hPeriod
      (intrinsicSmoothGeneralLorentzMetric period hPeriod) patch)
      |>.differentiable (by simp) coordinate
  have hDensityNe : density coordinate ≠ 0 :=
    localMetricVolumeFactor_ne_zero period hPeriod
      (intrinsicSmoothGeneralLorentzMetric period hPeriod) patch coordinate
  have hCoefficient (index : Index4) :
      DifferentiableAt Real (coefficient index) coordinate := by
    exact (((regularFrameCanonicalCoefficient period hPeriod metric vector
      index).contMDiff_toFun.comp patch.coordinateMap_contMDiff).contDiff
        ).differentiable (by simp) coordinate
  have hPulled (index : Index4) :
      DifferentiableAt Real
        (pulledRegularFrameVector period hPeriod metric patch index)
        coordinate :=
    (pulledRegularFrameVector_contDiff period hPeriod metric patch index
      ).differentiable (by simp) coordinate
  have hTerm (index : Index4) :
      DifferentiableAt Real (term index) coordinate :=
    (hCoefficient index).smul (hPulled index)
  have hFiniteSum := holonomicLocalDensityDivergence_finset_sum
    (indices := Finset.univ)
    density term coordinate hDensity
      (fun index _hIndex => hTerm index)
  have hTermFormula (index : Index4) :
      holonomicLocalDensityDivergence density (term index) coordinate =
        frameDerivative period hPeriod Real
            (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
            (regularFrameCanonicalCoefficient period hPeriod metric vector
              index)
            (patch.coordinateMap coordinate) index +
          regularFrameCanonicalCoefficient period hPeriod metric vector index
              (patch.coordinateMap coordinate) *
            regularFrameCanonicalDivergence period hPeriod metric index
              (patch.coordinateMap coordinate) := by
    change holonomicLocalDensityDivergence density
        (fun current => coefficient index current •
          pulledRegularFrameVector period hPeriod metric patch index current)
        coordinate = _
    rw [holonomicLocalDensityDivergence_smul density
      (coefficient index)
      (pulledRegularFrameVector period hPeriod metric patch index) coordinate
      hDensity hDensityNe (hCoefficient index) (hPulled index)]
    rw [holonomicLocalDensityDivergence_pulledRegularFrame]
    rw [← regularFrameCanonicalDivergence_local period hPeriod metric hGauge
      patch index coordinate]
    change
      regularFrameCanonicalCoefficient period hPeriod metric vector index
            (patch.coordinateMap coordinate) *
          regularFrameCanonicalDivergence period hPeriod metric index
            (patch.coordinateMap coordinate) +
        fderiv Real
          ((regularFrameCanonicalCoefficient period hPeriod metric vector
            index).toFun ∘ patch.coordinateMap) coordinate
          (pulledRegularFrameVector period hPeriod metric patch index
            coordinate) = _
    rw [fderiv_comp_coordinateMap_pulledRegularFrameVector period hPeriod
      metric
      (regularFrameCanonicalCoefficient period hPeriod metric vector index)
      patch coordinate index]
    ring
  rw [regularFrameAlgebraicCanonicalDivergence_apply]
  symm
  calc
    holonomicLocalDensityDivergence
          (localMetricVolumeFactor period hPeriod
            (intrinsicSmoothGeneralLorentzMetric period hPeriod) patch)
          (pulledRegularFrameExpansion period hPeriod metric patch vector)
          coordinate =
        ∑ index : Index4,
          holonomicLocalDensityDivergence density (term index) coordinate := by
      change holonomicLocalDensityDivergence density
          (fun current => ∑ index : Index4, term index current) coordinate =
        ∑ index : Index4,
          holonomicLocalDensityDivergence density (term index) coordinate
      simpa using hFiniteSum
    _ = _ := by
      apply Finset.sum_congr rfl
      intro index _hIndex
      exact hTermFormula index

/-- Each ten-flow obstruction is therefore a concrete weighted coordinate
divergence on every chart. -/
theorem regularFrameCanonicalGeneratorDivergenceResidual_local
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hGauge : RegularGeneralMetricInCanonicalVolumeGauge
      period hPeriod metric)
    (index : Fin 10)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    regularFrameCanonicalGeneratorDivergenceResidual period hPeriod metric
        index (patch.coordinateMap coordinate) =
      holonomicLocalDensityDivergence
        (localMetricVolumeFactor period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod) patch)
        (pulledRegularFrameExpansion period hPeriod metric patch
          (canonicalTenFlowVectorField period hPeriod index)) coordinate :=
  regularFrameAlgebraicCanonicalDivergence_local period hPeriod metric hGauge
    patch (canonicalTenFlowVectorField period hPeriod index) coordinate

/-- The concrete atlas supplies such a local residual formula through every
physical point. -/
theorem regularFrameCanonicalGeneratorDivergenceResidual_chartThroughEveryPoint
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hGauge : RegularGeneralMetricInCanonicalVolumeGauge
      period hPeriod metric)
    (index : Fin 10) (point : EffectiveQuotient period hPeriod) :
    ∃ (patch : SmoothHolonomicFrameChart4 period hPeriod)
        (coordinate : Vector4),
      patch.coordinateMap coordinate = point ∧
        regularFrameCanonicalGeneratorDivergenceResidual period hPeriod metric
            index point =
          holonomicLocalDensityDivergence
            (localMetricVolumeFactor period hPeriod
              (intrinsicSmoothGeneralLorentzMetric period hPeriod) patch)
            (pulledRegularFrameExpansion period hPeriod metric patch
              (canonicalTenFlowVectorField period hPeriod index)) coordinate := by
  obtain ⟨patch, coordinate, hCoordinate⟩ :=
    canonicalHolonomicChartThroughEveryPoint period hPeriod point
  refine ⟨patch, coordinate, hCoordinate, ?_⟩
  rw [← hCoordinate]
  exact regularFrameCanonicalGeneratorDivergenceResidual_local period hPeriod
    metric hGauge index patch coordinate

/-- Gate marker: the remaining ten global equations have exact local
weighted-divergence representatives covering the full quotient. -/
theorem regular_frame_canonical_divergence_local_formula_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hGauge : RegularGeneralMetricInCanonicalVolumeGauge
      period hPeriod metric) :
    ∀ (index : Fin 10) (point : EffectiveQuotient period hPeriod),
      ∃ (patch : SmoothHolonomicFrameChart4 period hPeriod)
          (coordinate : Vector4),
        patch.coordinateMap coordinate = point ∧
          regularFrameCanonicalGeneratorDivergenceResidual period hPeriod metric
              index point =
            holonomicLocalDensityDivergence
              (localMetricVolumeFactor period hPeriod
                (intrinsicSmoothGeneralLorentzMetric period hPeriod) patch)
              (pulledRegularFrameExpansion period hPeriod metric patch
                (canonicalTenFlowVectorField period hPeriod index)) coordinate :=
  regularFrameCanonicalGeneratorDivergenceResidual_chartThroughEveryPoint
    period hPeriod metric hGauge

end
end P0EFTJanusProgramPRegularFrameCanonicalDivergenceLocalFormula4D
end JanusFormal
