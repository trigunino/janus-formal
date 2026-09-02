import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartLocalActionDatum4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularFrameMetricInverse4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D

/-!
# Intrinsic gauge-potential reconstruction in a regular frame

The smooth inverse Gram matrix of a regular frame reconstructs an intrinsic
one-form from arbitrary smooth frame coefficients.  This supplies the missing
inverse to `gaugePotentialFrameCoefficients`.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularFrameGaugePotentialReconstruction4D

set_option autoImplicit false

noncomputable section

open Bundle Filter Set
open scoped Manifold ContDiff Topology BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusProgramPGlobalGaugeTangentIntrinsicEmbedding4D
open P0EFTJanusProgramPRegularFrameMetricInverse4D

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

private def gaugeEntryCLM (index : Fin 4 × Fin 2) :
    GaugeFiber →L[Real] Real :=
  LinearMap.toContinuousLinearMap
    { toFun := fun value => value index
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }

/-- One scalar component of a smooth coefficient packet. -/
def regularFrameGaugeCoefficient
    (coefficients : SmoothQuotientField period hPeriod GaugeFiber)
    (index : Fin 4 × Fin 2) : SmoothQuotientField period hPeriod Real where
  toFun := fun point => coefficients point index
  contMDiff_toFun :=
    (gaugeEntryCLM index).contMDiff.comp coefficients.contMDiff_toFun

/-- The metric pairing of one stored frame vector with a smooth tangent
field. -/
private def regularFrameMetricVectorPairing
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (frameIndex : Fin 4)
    (field : SmoothTangentField period hPeriod) :
    SmoothQuotientField period hPeriod Real where
  toFun := fun point => metric.metric.tensor.tensor point
    (metric.frame frameIndex point) (field point)
  contMDiff_toFun := by
    have hApplied := metric.metric.tensor.tensor.contMDiff.clm_bundle_apply
      (metric.frame frameIndex).contMDiff |>.clm_bundle_apply field.contMDiff
    intro point
    have hAppliedAt := hApplied point
    rw [Bundle.contMDiffAt_section] at hAppliedAt
    simpa using hAppliedAt

/-- Covector whose values in the regular frame are the supplied coefficient
field.  The inverse Gram matrix converts covariant metric pairings back to
dual-frame coordinates. -/
private def regularFrameMetricCovector
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (frameIndex : Fin 4) (point : EffectiveQuotient period hPeriod) :=
  metric.metric.tensor.tensor point (metric.frame frameIndex point)

private def regularFrameGaugeCovectorTerm
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (coefficients : SmoothQuotientField period hPeriod GaugeFiber)
    (component : Fin 2) (point : EffectiveQuotient period hPeriod)
    (row column : Fin 4) :=
  (coefficients point (row, component) *
    regularFrameMetricInverseMatrix period hPeriod metric row column point) •
      regularFrameMetricCovector period hPeriod metric column point

def regularFrameGaugeCovectorFromCoefficients
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (coefficients : SmoothQuotientField period hPeriod GaugeFiber)
    (component : Fin 2) (point : EffectiveQuotient period hPeriod) :=
  ∑ row : Fin 4, ∑ column : Fin 4,
    regularFrameGaugeCovectorTerm period hPeriod metric coefficients component
      point row column

/-- Evaluation of the reconstructed covector on any smooth tangent field is
smooth on the base. -/
private def regularFrameGaugeCovectorSmoothEvaluation
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (coefficients : SmoothQuotientField period hPeriod GaugeFiber)
    (component : Fin 2) (field : SmoothTangentField period hPeriod) :
    SmoothQuotientField period hPeriod Real where
  toFun := fun point =>
    regularFrameGaugeCovectorFromCoefficients period hPeriod metric
      coefficients component point (field point)
  contMDiff_toFun := by
    simp only [regularFrameGaugeCovectorFromCoefficients,
      regularFrameGaugeCovectorTerm, regularFrameMetricCovector]
    change ContMDiff coverModelWithCorners (modelWithCornersSelf Real Real) ∞
      (fun point => ∑ row : Fin 4, ∑ column : Fin 4,
        (coefficients point (row, component) *
          regularFrameMetricInverseMatrix period hPeriod metric row column
            point) *
          metric.metric.tensor.tensor point (metric.frame column point)
            (field point))
    apply contMDiff_finsetSum
    intro row _
    apply contMDiff_finsetSum
    intro column _
    exact ((regularFrameGaugeCoefficient period hPeriod coefficients
      (row, component)).contMDiff_toFun.mul
        (regularFrameMetricInverseMatrix period hPeriod metric row column
          ).contMDiff_toFun).mul
      (regularFrameMetricVectorPairing period hPeriod metric column field
        ).contMDiff_toFun

private def finiteGeneratorTangentField
    (index : Fin (finiteSmoothTangentFrame period hPeriod).count) :
    SmoothTangentField period hPeriod where
  toFun := fun point =>
    (finiteSmoothTangentFrame period hPeriod).vectorAt point index
  contMDiff_toFun :=
    (finiteSmoothTangentFrame period hPeriod).contMDiff_vector index

private def localReconstructedGaugeEvaluation
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (coefficients : SmoothQuotientField period hPeriod GaugeFiber)
    (component : Fin 2)
    (patch : FiniteTangentGeneratorPatch period hPeriod)
    (vector : TangentBundle coverModelWithCorners
      (EffectiveQuotient period hPeriod)) : Real :=
  ∑ basisIndex : FiniteTangentGeneratorBasisIndex,
    (finiteTangentGeneratorLocalCoefficient period hPeriod patch basisIndex
        vector.1 vector.2 *
      (finiteTangentGeneratorWeight period hPeriod patch vector.1)⁻¹) *
      regularFrameGaugeCovectorSmoothEvaluation period hPeriod metric
        coefficients component
          (finiteGeneratorTangentField period hPeriod
            (finiteTangentGeneratorIndexEquivFin period hPeriod
              (patch, basisIndex))) vector.1

private theorem localReconstructedGaugeEvaluation_contMDiffAt
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (coefficients : SmoothQuotientField period hPeriod GaugeFiber)
    (component : Fin 2)
    (patch : FiniteTangentGeneratorPatch period hPeriod)
    (vector : TangentBundle coverModelWithCorners
      (EffectiveQuotient period hPeriod))
    (hPoint : vector.1 ∈
      finiteTangentGeneratorOpenPatch period hPeriod patch)
    (hWeight :
      finiteTangentGeneratorWeight period hPeriod patch vector.1 ≠ 0) :
    ContMDiffAt coverModelWithCorners.tangent
      (modelWithCornersSelf Real Real) ∞
      (localReconstructedGaugeEvaluation period hPeriod metric coefficients
        component patch) vector := by
  have hProjection :
      ContMDiff coverModelWithCorners.tangent coverModelWithCorners ∞
        (fun current : TangentBundle coverModelWithCorners
          (EffectiveQuotient period hPeriod) => current.1) :=
    Bundle.contMDiff_proj
      (fun point : EffectiveQuotient period hPeriod =>
        TangentSpace coverModelWithCorners point)
  have hWeightSmooth :
      ContMDiffAt coverModelWithCorners.tangent
        (modelWithCornersSelf Real Real) ∞
        (fun current : TangentBundle coverModelWithCorners
          (EffectiveQuotient period hPeriod) =>
            finiteTangentGeneratorWeight period hPeriod patch current.1)
        vector :=
    ((finiteTangentGeneratorWeight_contMDiff period hPeriod patch).comp
      hProjection).contMDiffAt
  unfold localReconstructedGaugeEvaluation
  apply ContMDiffAt.sum
  intro basisIndex _
  have hCoefficient :=
    finiteTangentGeneratorLocalCoefficient_contMDiffAt period hPeriod patch
      basisIndex vector hPoint
  have hGenerator :
      ContMDiffAt coverModelWithCorners.tangent
        (modelWithCornersSelf Real Real) ∞
        (fun current : TangentBundle coverModelWithCorners
          (EffectiveQuotient period hPeriod) =>
            regularFrameGaugeCovectorSmoothEvaluation period hPeriod metric
              coefficients component
                (finiteGeneratorTangentField period hPeriod
                  (finiteTangentGeneratorIndexEquivFin period hPeriod
                    (patch, basisIndex))) current.1) vector :=
    ((regularFrameGaugeCovectorSmoothEvaluation period hPeriod metric
        coefficients component
          (finiteGeneratorTangentField period hPeriod
            (finiteTangentGeneratorIndexEquivFin period hPeriod
              (patch, basisIndex)))).contMDiff_toFun.comp
      hProjection).contMDiffAt
  exact (hCoefficient.mul (hWeightSmooth.inv₀ hWeight)).mul hGenerator

private theorem regularFrameGaugeCovector_eq_local
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (coefficients : SmoothQuotientField period hPeriod GaugeFiber)
    (component : Fin 2)
    (patch : FiniteTangentGeneratorPatch period hPeriod)
    (vector : TangentBundle coverModelWithCorners
      (EffectiveQuotient period hPeriod))
    (hPoint : vector.1 ∈
      finiteTangentGeneratorOpenPatch period hPeriod patch)
    (hWeight :
      finiteTangentGeneratorWeight period hPeriod patch vector.1 ≠ 0) :
    regularFrameGaugeCovectorFromCoefficients period hPeriod metric
        coefficients component vector.1 vector.2 =
      localReconstructedGaugeEvaluation period hPeriod metric coefficients
        component patch vector := by
  let covector := regularFrameGaugeCovectorFromCoefficients period hPeriod
    metric coefficients component vector.1
  rw [finiteTangentGeneratorLocalVector_reconstructs period hPeriod patch
    vector.1 hPoint vector.2]
  rw [map_sum]
  unfold localReconstructedGaugeEvaluation
  apply Finset.sum_congr rfl
  intro basisIndex _
  rw [map_smul]
  change
    finiteTangentGeneratorLocalCoefficient period hPeriod patch basisIndex
          vector.1 vector.2 *
        covector
          (finiteTangentGeneratorLocalVector period hPeriod patch basisIndex
            vector.1) = _
  change _ =
    (finiteTangentGeneratorLocalCoefficient period hPeriod patch basisIndex
        vector.1 vector.2 *
      (finiteTangentGeneratorWeight period hPeriod patch vector.1)⁻¹) *
      covector
        ((finiteSmoothTangentFrame period hPeriod).vectorAt vector.1
          (finiteTangentGeneratorIndexEquivFin period hPeriod
            (patch, basisIndex)))
  rw [finiteSmoothTangentFrame_vectorAt_generator]
  rw [map_smul]
  simp only [smul_eq_mul]
  field_simp

/-- Smooth intrinsic potential reconstructed from arbitrary smooth regular
frame coefficients. -/
def regularFrameGaugePotentialFromCoefficients
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (coefficients : SmoothQuotientField period hPeriod GaugeFiber) :
    SmoothAbelianGaugePotential period hPeriod where
  toFun := regularFrameGaugeCovectorFromCoefficients period hPeriod metric
    coefficients
  contMDiff_eval := fun component vector => by
    obtain ⟨patch, hPatchBound⟩ :=
      exists_finiteTangentGeneratorWeight_ge_inv_card period hPeriod vector.1
    letI : Nonempty (FiniteTangentGeneratorPatch period hPeriod) := ⟨patch⟩
    have hCard :
        0 < Fintype.card (FiniteTangentGeneratorPatch period hPeriod) :=
      Fintype.card_pos
    have hInvCard :
        0 < 1 / (Fintype.card
          (FiniteTangentGeneratorPatch period hPeriod) : Real) :=
      one_div_pos.mpr (by exact_mod_cast hCard)
    have hWeightPos :
        0 < finiteTangentGeneratorWeight period hPeriod patch vector.1 :=
      hInvCard.trans_le hPatchBound
    have hWeight :
        finiteTangentGeneratorWeight period hPeriod patch vector.1 ≠ 0 :=
      ne_of_gt hWeightPos
    have hPoint : vector.1 ∈
        finiteTangentGeneratorOpenPatch period hPeriod patch := by
      apply finiteTangentGeneratorClosedPatch_subset_openPatch
        period hPeriod patch
      exact subset_closure hWeight
    have hProjection :
        ContMDiff coverModelWithCorners.tangent coverModelWithCorners ∞
          (fun current : TangentBundle coverModelWithCorners
            (EffectiveQuotient period hPeriod) => current.1) :=
      Bundle.contMDiff_proj
        (fun point : EffectiveQuotient period hPeriod =>
          TangentSpace coverModelWithCorners point)
    have hEventuallyPoint : ∀ᶠ current in 𝓝 vector,
        current.1 ∈ finiteTangentGeneratorOpenPatch period hPeriod patch :=
      hProjection.continuous.continuousAt
        (finiteTangentGeneratorOpenPatch_isOpen period hPeriod patch
          |>.mem_nhds hPoint)
    have hWeightSmooth :
        ContMDiffAt coverModelWithCorners.tangent
          (modelWithCornersSelf Real Real) ∞
          (fun current : TangentBundle coverModelWithCorners
            (EffectiveQuotient period hPeriod) =>
              finiteTangentGeneratorWeight period hPeriod patch current.1)
          vector :=
      ((finiteTangentGeneratorWeight_contMDiff period hPeriod patch).comp
        hProjection).contMDiffAt
    have hEventuallyWeight : ∀ᶠ current in 𝓝 vector,
        finiteTangentGeneratorWeight period hPeriod patch current.1 ≠ 0 :=
      hWeightSmooth.continuousAt.eventually_ne hWeight
    apply (localReconstructedGaugeEvaluation_contMDiffAt period hPeriod
      metric coefficients component patch vector hPoint hWeight
        ).congr_of_eventuallyEq
    filter_upwards [hEventuallyPoint, hEventuallyWeight] with
      current hCurrentPoint hCurrentWeight
    exact regularFrameGaugeCovector_eq_local period hPeriod metric coefficients
      component patch current hCurrentPoint hCurrentWeight

@[simp]
theorem regularFrameGaugeCovectorFromCoefficients_frame
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (coefficients : SmoothQuotientField period hPeriod GaugeFiber)
    (component : Fin 2)
    (point : EffectiveQuotient period hPeriod)
    (frameIndex : Fin 4) :
    regularFrameGaugeCovectorFromCoefficients period hPeriod metric
        coefficients component point (metric.frame frameIndex point) =
      coefficients point (frameIndex, component) := by
  classical
  have hInverseEntry (row : Fin 4) :
      (∑ column : Fin 4,
        regularFrameMetricInverseMatrix period hPeriod metric row column point *
          metric.metric.tensor.tensor point
            (metric.frame column point) (metric.frame frameIndex point)) =
        (1 : Matrix (Fin 4) (Fin 4) Real) row frameIndex := by
    have hProduct := Matrix.nonsing_inv_mul
      (regularFrameMetricMatrixMap period hPeriod metric point)
      (isUnit_iff_ne_zero.mpr
        (regularFrameMetricMatrix_det_ne_zero
          period hPeriod metric point))
    have hEntry := congrFun (congrFun hProduct row) frameIndex
    simpa [Matrix.mul_apply, regularFrameMetricInverseMatrix,
      regularFrameMetricInverseMatrixMap, regularFrameMetricMatrixMap,
      regularFrameMetricMatrix] using hEntry
  simp only [regularFrameGaugeCovectorFromCoefficients,
    regularFrameGaugeCovectorTerm, regularFrameMetricCovector]
  calc
    (∑ row : Fin 4, ∑ column : Fin 4,
        (coefficients point (row, component) *
          regularFrameMetricInverseMatrix period hPeriod metric row column
            point) *
          metric.metric.tensor.tensor point
            (metric.frame column point) (metric.frame frameIndex point)) =
        ∑ row : Fin 4, coefficients point (row, component) *
          (∑ column : Fin 4,
            regularFrameMetricInverseMatrix period hPeriod metric row column
                point *
              metric.metric.tensor.tensor point
                (metric.frame column point)
                (metric.frame frameIndex point)) := by
      apply Finset.sum_congr rfl
      intro row _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro column _
      ring
    _ = ∑ row : Fin 4, coefficients point (row, component) *
        (1 : Matrix (Fin 4) (Fin 4) Real) row frameIndex := by
      apply Finset.sum_congr rfl
      intro row _
      rw [hInverseEntry row]
    _ = coefficients point (frameIndex, component) := by
      simp [Matrix.one_apply]

@[simp]
theorem gaugePotentialFrameCoefficients_reconstructed
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (coefficients : SmoothQuotientField period hPeriod GaugeFiber) :
    gaugePotentialFrameCoefficients period hPeriod metric
        (regularFrameGaugePotentialFromCoefficients
          period hPeriod metric coefficients) =
      coefficients := by
  apply SmoothQuotientField.ext period hPeriod GaugeFiber
  intro point
  apply (EuclideanSpace.equiv (Fin 4 × Fin 2) Real).injective
  funext index
  change
    regularFrameGaugeCovectorFromCoefficients period hPeriod metric
        coefficients index.2 point (metric.frame index.1 point) =
      coefficients point index
  exact regularFrameGaugeCovectorFromCoefficients_frame
    period hPeriod metric coefficients index.2 point index.1

/-- Arbitrary smooth regular-frame gauge coefficients are represented by a
genuine intrinsic smooth gauge potential. -/
theorem regular_frame_gauge_potential_reconstruction_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (coefficients : SmoothQuotientField period hPeriod GaugeFiber) :
    ∃ potential : SmoothAbelianGaugePotential period hPeriod,
      gaugePotentialFrameCoefficients period hPeriod metric potential =
        coefficients :=
  ⟨regularFrameGaugePotentialFromCoefficients period hPeriod metric
      coefficients,
    gaugePotentialFrameCoefficients_reconstructed period hPeriod metric
      coefficients⟩

end

end P0EFTJanusProgramPRegularFrameGaugePotentialReconstruction4D
end JanusFormal
