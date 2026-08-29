import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusMetricCartanFiber4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusTensorialDiffeomorphismRepresentation4D

/-!
# Global smooth metric Cartan action

The finite smooth tangent generators provide rescaled local frames wherever
one partition weight is nonzero.  A double local-frame expansion promotes the
fiberwise metric Cartan residual to a genuine global smooth symmetric tensor.
-/

open scoped Manifold ContDiff

noncomputable section

variable
    {E H M F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [FiniteDimensional ℝ F]

private theorem contMDiffAt_clm_apply_iff
    {n : WithTop ℕ∞}
    {f : M → F →L[ℝ] G}
    {x : M} :
    ContMDiffAt I 𝓘(ℝ, F →L[ℝ] G) n f x ↔
      ∀ y, ContMDiffAt I 𝓘(ℝ, G) n (fun z => f z y) x := by
  constructor
  · intro hf y
    exact hf.clm_apply contMDiffAt_const
  · intro hf
    let d := Module.finrank ℝ F
    have hd : d = Module.finrank ℝ (Fin d → ℝ) :=
      (Module.finrank_fin_fun ℝ).symm
    let e₁ := ContinuousLinearEquiv.ofFinrankEq hd
    let e₂ :=
      (e₁.arrowCongr (1 : G ≃L[ℝ] G)).trans
        (ContinuousLinearEquiv.piRing (Fin d))
    rw [← Function.id_comp f, ← e₂.symm_comp_self]
    exact e₂.symm.contDiff.contMDiff.contMDiffAt.comp x
      (contMDiffAt_pi_space.mpr fun i => hf _)

end

namespace JanusFormal
namespace P0EFTJanusMappingTorusMetricCartanGlobalAction4D

set_option synthInstance.maxHeartbeats 200000

noncomputable section

open Bundle Filter Module Set
open scoped Manifold ContDiff Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusMetricCartanFiberCore4D
open P0EFTJanusMappingTorusMetricCartanFiber4D
open P0EFTJanusMappingTorusGradedScalarGhostAction4D
open P0EFTJanusMappingTorusSmoothDiffeomorphismGhostLieBracket4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusScalarGhostCEClosure4D
open P0EFTJanusMappingTorusTensorialDiffeomorphismRepresentation4D

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

private abbrev Ghost :=
  CInfinityDiffeomorphismGhost period hPeriod

private abbrev TangentFiber
    (point : EffectiveQuotient period hPeriod) :=
  TangentSpace coverModelWithCorners point

private abbrev CotangentFiber
    (point : EffectiveQuotient period hPeriod) :=
  TangentFiber period hPeriod point →L[Real] Real

private abbrev TensorFiber
    (point : EffectiveQuotient period hPeriod) :=
  TangentFiber period hPeriod point →L[Real]
    CotangentFiber period hPeriod point

private abbrev TensorModel :=
  CoverCoordinates →L[Real] CoverCoordinates →L[Real] Real

private def patchTangentVector
    (patch : FiniteTangentGeneratorPatch period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (vector : CoverCoordinates) :
    TangentFiber period hPeriod point :=
  (trivializationAt CoverCoordinates (TangentFiber period hPeriod) patch.1).symm
    point vector

private def localMetricCartanEvaluation
    (acting : Ghost period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (patch : FiniteTangentGeneratorPatch period hPeriod)
    (first second : CoverCoordinates)
    (point : EffectiveQuotient period hPeriod) : Real :=
  ∑ secondIndex : FiniteTangentGeneratorBasisIndex,
    ∑ firstIndex : FiniteTangentGeneratorBasisIndex,
      ((finiteTangentGeneratorLocalCoefficient period hPeriod patch firstIndex
          point (patchTangentVector period hPeriod patch point first) *
          (finiteTangentGeneratorWeight period hPeriod patch point)⁻¹) *
        (finiteTangentGeneratorLocalCoefficient period hPeriod patch secondIndex
          point (patchTangentVector period hPeriod patch point second) *
          (finiteTangentGeneratorWeight period hPeriod patch point)⁻¹)) *
        smoothMetricCartanResidualScalar period hPeriod acting tensor
          (finiteGeneratorCInfinityGhost period hPeriod
            (finiteTangentGeneratorIndexEquivFin period hPeriod
              (patch, firstIndex)))
          (finiteGeneratorCInfinityGhost period hPeriod
            (finiteTangentGeneratorIndexEquivFin period hPeriod
              (patch, secondIndex))) point

private theorem patchTangentVector_contMDiffAt
    (patch : FiniteTangentGeneratorPatch period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (vector : CoverCoordinates)
    (hPoint :
      point ∈ finiteTangentGeneratorOpenPatch period hPeriod patch) :
    ContMDiffAt coverModelWithCorners coverModelWithCorners.tangent ∞
      (fun current =>
        TotalSpace.mk' CoverCoordinates current
          (patchTangentVector period hPeriod patch current vector))
      point := by
  let trivialization :=
    trivializationAt CoverCoordinates (TangentFiber period hPeriod) patch.1
  have hBase : point ∈ trivialization.baseSet := by
    exact hPoint
  apply (trivialization.contMDiffAt_section_iff hBase).2
  apply contMDiffAt_const.congr_of_eventuallyEq
  filter_upwards [trivialization.open_baseSet.mem_nhds hBase] with current hCurrent
  simpa [patchTangentVector, trivialization] using
    congrArg Prod.snd (trivialization.apply_mk_symm hCurrent vector)

private theorem localMetricCartanEvaluation_contMDiffAt
    (acting : Ghost period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (patch : FiniteTangentGeneratorPatch period hPeriod)
    (first second : CoverCoordinates)
    (point : EffectiveQuotient period hPeriod)
    (hPoint :
      point ∈ finiteTangentGeneratorOpenPatch period hPeriod patch)
    (hWeight :
      finiteTangentGeneratorWeight period hPeriod patch point ≠ 0) :
    ContMDiffAt coverModelWithCorners 𝓘(Real, Real) ∞
      (localMetricCartanEvaluation period hPeriod acting tensor patch
        first second) point := by
  have hWeightSmooth :
      ContMDiffAt coverModelWithCorners 𝓘(Real, Real) ∞
        (finiteTangentGeneratorWeight period hPeriod patch) point :=
    (finiteTangentGeneratorWeight_contMDiff period hPeriod patch).contMDiffAt
  unfold localMetricCartanEvaluation
  apply ContMDiffAt.sum
  intro secondIndex _
  apply ContMDiffAt.sum
  intro firstIndex _
  have hFirstCoefficient :
      ContMDiffAt coverModelWithCorners 𝓘(Real, Real) ∞
        (fun current =>
          finiteTangentGeneratorLocalCoefficient period hPeriod patch firstIndex
            current (patchTangentVector period hPeriod patch current first))
        point := by
    exact
      (finiteTangentGeneratorLocalCoefficient_contMDiffAt
        period hPeriod patch firstIndex
        ⟨point, patchTangentVector period hPeriod patch point first⟩ hPoint).comp
          point
          (patchTangentVector_contMDiffAt
            period hPeriod patch point first hPoint)
  have hSecondCoefficient :
      ContMDiffAt coverModelWithCorners 𝓘(Real, Real) ∞
        (fun current =>
          finiteTangentGeneratorLocalCoefficient period hPeriod patch secondIndex
            current (patchTangentVector period hPeriod patch current second))
        point := by
    exact
      (finiteTangentGeneratorLocalCoefficient_contMDiffAt
        period hPeriod patch secondIndex
        ⟨point, patchTangentVector period hPeriod patch point second⟩ hPoint).comp
          point
          (patchTangentVector_contMDiffAt
            period hPeriod patch point second hPoint)
  have hResidual :
      ContMDiffAt coverModelWithCorners 𝓘(Real, Real) ∞
        (smoothMetricCartanResidualScalar period hPeriod acting tensor
          (finiteGeneratorCInfinityGhost period hPeriod
            (finiteTangentGeneratorIndexEquivFin period hPeriod
              (patch, firstIndex)))
          (finiteGeneratorCInfinityGhost period hPeriod
            (finiteTangentGeneratorIndexEquivFin period hPeriod
              (patch, secondIndex))))
        point :=
    (smoothMetricCartanResidualScalar period hPeriod acting tensor
      (finiteGeneratorCInfinityGhost period hPeriod
        (finiteTangentGeneratorIndexEquivFin period hPeriod
          (patch, firstIndex)))
      (finiteGeneratorCInfinityGhost period hPeriod
        (finiteTangentGeneratorIndexEquivFin period hPeriod
          (patch, secondIndex)))).contMDiff.contMDiffAt
  exact
    ((hFirstCoefficient.mul (hWeightSmooth.inv₀ hWeight)).mul
      (hSecondCoefficient.mul (hWeightSmooth.inv₀ hWeight))).mul hResidual

private theorem smoothMetricCartanFiber_eq_local
    (acting : Ghost period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (patch : FiniteTangentGeneratorPatch period hPeriod)
    (first second : CoverCoordinates)
    (point : EffectiveQuotient period hPeriod)
    (hPoint :
      point ∈ finiteTangentGeneratorOpenPatch period hPeriod patch)
    (hWeight :
      finiteTangentGeneratorWeight period hPeriod patch point ≠ 0) :
    smoothMetricCartanFiber period hPeriod acting tensor point
        (patchTangentVector period hPeriod patch point first)
        (patchTangentVector period hPeriod patch point second) =
      localMetricCartanEvaluation period hPeriod acting tensor patch
        first second point := by
  rw [finiteTangentGeneratorLocalVector_reconstructs
    period hPeriod patch point hPoint
      (patchTangentVector period hPeriod patch point first)]
  rw [finiteTangentGeneratorLocalVector_reconstructs
    period hPeriod patch point hPoint
      (patchTangentVector period hPeriod patch point second)]
  simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul]
  unfold localMetricCartanEvaluation
  apply Finset.sum_congr rfl
  intro secondIndex _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro firstIndex _
  rw [smoothMetricCartanResidualScalar_apply]
  rw [← smoothMetricCartanFiber_apply period hPeriod acting tensor point
    (finiteGeneratorCInfinityGhost period hPeriod
      (finiteTangentGeneratorIndexEquivFin period hPeriod
        (patch, firstIndex)))
    (finiteGeneratorCInfinityGhost period hPeriod
      (finiteTangentGeneratorIndexEquivFin period hPeriod
        (patch, secondIndex)))]
  change
    finiteTangentGeneratorLocalCoefficient period hPeriod patch secondIndex
          point (patchTangentVector period hPeriod patch point second) *
        (finiteTangentGeneratorLocalCoefficient period hPeriod patch firstIndex
          point (patchTangentVector period hPeriod patch point first) *
          smoothMetricCartanFiber period hPeriod acting tensor point
            (finiteTangentGeneratorLocalVector period hPeriod patch
              firstIndex point)
            (finiteTangentGeneratorLocalVector period hPeriod patch
              secondIndex point)) =
      ((finiteTangentGeneratorLocalCoefficient period hPeriod patch firstIndex
          point (patchTangentVector period hPeriod patch point first) *
          (finiteTangentGeneratorWeight period hPeriod patch point)⁻¹) *
        (finiteTangentGeneratorLocalCoefficient period hPeriod patch secondIndex
          point (patchTangentVector period hPeriod patch point second) *
          (finiteTangentGeneratorWeight period hPeriod patch point)⁻¹)) *
        smoothMetricCartanFiber period hPeriod acting tensor point
          ((finiteSmoothTangentFrame period hPeriod).vectorAt point
            (finiteTangentGeneratorIndexEquivFin period hPeriod
              (patch, firstIndex)))
          ((finiteSmoothTangentFrame period hPeriod).vectorAt point
            (finiteTangentGeneratorIndexEquivFin period hPeriod
              (patch, secondIndex)))
  rw [finiteSmoothTangentFrame_vectorAt_generator,
    finiteSmoothTangentFrame_vectorAt_generator]
  simp only [map_smul, smul_apply, smul_eq_mul]
  field_simp

private def metricCartanCoordinate
    (acting : Ghost period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (patch : FiniteTangentGeneratorPatch period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    TensorModel :=
  (trivializationAt (TensorModel)
    (TensorFiber period hPeriod) patch.1
      ⟨point, smoothMetricCartanFiber period hPeriod acting tensor point⟩).2

private theorem metricCartanCoordinate_apply_eq_local
    (acting : Ghost period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (patch : FiniteTangentGeneratorPatch period hPeriod)
    (first second : CoverCoordinates)
    (point : EffectiveQuotient period hPeriod)
    (hPoint :
      point ∈ finiteTangentGeneratorOpenPatch period hPeriod patch)
    (hWeight :
      finiteTangentGeneratorWeight period hPeriod patch point ≠ 0) :
    metricCartanCoordinate period hPeriod acting tensor patch point
        first second =
      localMetricCartanEvaluation period hPeriod acting tensor patch
        first second point := by
  change
    ContinuousLinearMap.inCoordinates
        CoverCoordinates (TangentFiber period hPeriod)
        (CoverCoordinates →L[Real] Real) (CotangentFiber period hPeriod)
        patch.1 point patch.1 point
        (smoothMetricCartanFiber period hPeriod acting tensor point)
        first second =
      _
  rw [inCoordinates_apply_eq₂ hPoint hPoint (by simp)]
  simpa [patchTangentVector] using
    smoothMetricCartanFiber_eq_local period hPeriod acting tensor patch
      first second point hPoint hWeight

private theorem metricCartanCoordinate_contMDiffAt
    (acting : Ghost period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (patch : FiniteTangentGeneratorPatch period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (hPoint :
      point ∈ finiteTangentGeneratorOpenPatch period hPeriod patch)
    (hWeight :
      finiteTangentGeneratorWeight period hPeriod patch point ≠ 0) :
    ContMDiffAt coverModelWithCorners 𝓘(Real, TensorModel) ∞
      (metricCartanCoordinate period hPeriod acting tensor patch) point := by
  apply (contMDiffAt_clm_apply_iff coverModelWithCorners).2
  intro first
  apply (contMDiffAt_clm_apply_iff coverModelWithCorners).2
  intro second
  have hLocal :=
    localMetricCartanEvaluation_contMDiffAt period hPeriod acting tensor patch
      first second point hPoint hWeight
  have hEventuallyPoint :
      ∀ᶠ current in 𝓝 point,
        current ∈ finiteTangentGeneratorOpenPatch period hPeriod patch :=
    (finiteTangentGeneratorOpenPatch_isOpen period hPeriod patch).mem_nhds hPoint
  have hEventuallyWeight :
      ∀ᶠ current in 𝓝 point,
        finiteTangentGeneratorWeight period hPeriod patch current ≠ 0 :=
    (finiteTangentGeneratorWeight_contMDiff period hPeriod patch).continuous
      |>.continuousAt.eventually_ne hWeight
  apply hLocal.congr_of_eventuallyEq
  filter_upwards [hEventuallyPoint, hEventuallyWeight] with
    current hCurrentPoint hCurrentWeight
  exact metricCartanCoordinate_apply_eq_local period hPeriod acting tensor patch
    first second current hCurrentPoint hCurrentWeight

private theorem smoothMetricCartanFiber_contMDiff
    (acting : Ghost period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    ContMDiff coverModelWithCorners
      (coverModelWithCorners.prod 𝓘(Real, TensorModel)) ∞
      (fun point =>
        TotalSpace.mk' TensorModel point
          (smoothMetricCartanFiber period hPeriod acting tensor point)) := by
  intro point
  obtain ⟨patch, hPatchBound⟩ :=
    exists_finiteTangentGeneratorWeight_ge_inv_card
      period hPeriod point
  letI : Nonempty (FiniteTangentGeneratorPatch period hPeriod) :=
    ⟨patch⟩
  have hCard :
      0 < Fintype.card (FiniteTangentGeneratorPatch period hPeriod) :=
    Fintype.card_pos
  have hInvCard :
      0 < 1 / (Fintype.card
        (FiniteTangentGeneratorPatch period hPeriod) : Real) :=
    one_div_pos.mpr (by exact_mod_cast hCard)
  have hWeightPos :
      0 < finiteTangentGeneratorWeight period hPeriod patch point :=
    hInvCard.trans_le hPatchBound
  have hWeight :
      finiteTangentGeneratorWeight period hPeriod patch point ≠ 0 :=
    ne_of_gt hWeightPos
  have hPoint :
      point ∈ finiteTangentGeneratorOpenPatch period hPeriod patch := by
    apply finiteTangentGeneratorClosedPatch_subset_openPatch
      period hPeriod patch
    exact subset_closure hWeight
  let tensorTrivialization :=
    trivializationAt TensorModel (TensorFiber period hPeriod) patch.1
  have hTensorBase : point ∈ tensorTrivialization.baseSet := by
    simp only [tensorTrivialization, hom_trivializationAt_baseSet]
    exact ⟨hPoint, hPoint, by simp⟩
  apply (tensorTrivialization.contMDiffAt_section_iff hTensorBase).2
  exact metricCartanCoordinate_contMDiffAt period hPeriod acting tensor patch
    point hPoint hWeight

/-- The fiberwise metric Cartan residual assembled as a genuine smooth
symmetric covariant two-tensor. -/
def smoothMetricCartanAction
    (acting : Ghost period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    SmoothSymmetricCovariantTwoTensor period hPeriod where
  tensor :=
    { toFun := smoothMetricCartanFiber period hPeriod acting tensor
      contMDiff_toFun :=
        smoothMetricCartanFiber_contMDiff period hPeriod acting tensor }
  symmetric :=
    smoothMetricCartanFiber_symm period hPeriod acting tensor

@[simp]
theorem smoothMetricCartanAction_apply
    (acting : Ghost period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (first second : Ghost period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    (smoothMetricCartanAction period hPeriod acting tensor).tensor point
        (first point) (second point) =
      metricCartanResidualAt coverModelWithCorners acting tensor.tensor
        point first second := by
  exact smoothMetricCartanFiber_apply period hPeriod acting tensor point
    first second

/-- The global action realizes the intrinsic Cartan formula after contraction
with any two smooth tangent ghosts. -/
theorem smoothMetricCartanAction_cartan
    (acting : Ghost period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (first second : Ghost period hPeriod) :
    symmetricTensorGhostContraction period hPeriod first second
        (smoothMetricCartanAction period hPeriod acting tensor) =
      cInfinityScalarLieDerivative period hPeriod acting
          (symmetricTensorGhostContraction period hPeriod first second tensor) -
        symmetricTensorGhostContraction period hPeriod
          (smoothGhostLieBracket period hPeriod acting first) second tensor -
        symmetricTensorGhostContraction period hPeriod first
          (smoothGhostLieBracket period hPeriod acting second) tensor := by
  apply ContMDiffMap.ext
  intro point
  change
    (smoothMetricCartanAction period hPeriod acting tensor).tensor point
        (first point) (second point) =
      metricCartanResidualAt coverModelWithCorners acting tensor.tensor
        point first second
  exact smoothMetricCartanAction_apply period hPeriod acting tensor first second
    point

theorem smoothMetricCartanAction_add_acting
    (first second : Ghost period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    smoothMetricCartanAction period hPeriod (first + second) tensor =
      smoothMetricCartanAction period hPeriod first tensor +
        smoothMetricCartanAction period hPeriod second tensor := by
  apply symmetricTensor_eq_of_ghostContraction_eq period hPeriod
  intro left right
  rw [symmetricTensorGhostContraction_addTensor]
  rw [smoothMetricCartanAction_cartan]
  rw [smoothMetricCartanAction_cartan, smoothMetricCartanAction_cartan]
  rw [cInfinityScalarLieDerivative_addGhost]
  rw [smoothGhostLieBracket_add_left, smoothGhostLieBracket_add_left]
  rw [symmetricTensorGhostContraction_addFirstGhost,
    symmetricTensorGhostContraction_addSecondGhost]
  abel

theorem smoothMetricCartanAction_smul_acting
    (coefficient : Real)
    (acting : Ghost period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    smoothMetricCartanAction period hPeriod (coefficient • acting) tensor =
      coefficient •
        smoothMetricCartanAction period hPeriod acting tensor := by
  apply symmetricTensor_eq_of_ghostContraction_eq period hPeriod
  intro first second
  rw [symmetricTensorGhostContraction_smulTensor]
  rw [smoothMetricCartanAction_cartan]
  rw [smoothMetricCartanAction_cartan]
  rw [cInfinityScalarLieDerivative_smulGhost]
  rw [smoothGhostLieBracket_smul_left, smoothGhostLieBracket_smul_left]
  rw [symmetricTensorGhostContraction_smulFirstGhost,
    symmetricTensorGhostContraction_smulSecondGhost]
  module

theorem smoothMetricCartanAction_add_tensor
    (acting : Ghost period hPeriod)
    (first second : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    smoothMetricCartanAction period hPeriod acting (first + second) =
      smoothMetricCartanAction period hPeriod acting first +
        smoothMetricCartanAction period hPeriod acting second := by
  apply symmetricTensor_eq_of_ghostContraction_eq period hPeriod
  intro left right
  rw [symmetricTensorGhostContraction_addTensor]
  rw [smoothMetricCartanAction_cartan]
  rw [smoothMetricCartanAction_cartan, smoothMetricCartanAction_cartan]
  rw [symmetricTensorGhostContraction_addTensor,
    symmetricTensorGhostContraction_addTensor,
    symmetricTensorGhostContraction_addTensor]
  rw [cInfinityScalarLieDerivative_addScalar]
  abel

theorem smoothMetricCartanAction_smul_tensor
    (acting : Ghost period hPeriod)
    (coefficient : Real)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    smoothMetricCartanAction period hPeriod acting (coefficient • tensor) =
      coefficient •
        smoothMetricCartanAction period hPeriod acting tensor := by
  apply symmetricTensor_eq_of_ghostContraction_eq period hPeriod
  intro first second
  rw [symmetricTensorGhostContraction_smulTensor]
  rw [smoothMetricCartanAction_cartan]
  rw [smoothMetricCartanAction_cartan]
  rw [symmetricTensorGhostContraction_smulTensor,
    symmetricTensorGhostContraction_smulTensor,
    symmetricTensorGhostContraction_smulTensor]
  rw [cInfinityScalarLieDerivative_smulScalar]
  module

/-- The unconditional smooth metric Cartan operation is bilinear in the
acting ghost and symmetric tensor. -/
def smoothMetricCartanActionBilinear :
    Ghost period hPeriod →ₗ[Real]
      SmoothSymmetricCovariantTwoTensor period hPeriod →ₗ[Real]
        SmoothSymmetricCovariantTwoTensor period hPeriod where
  toFun acting :=
    { toFun := smoothMetricCartanAction period hPeriod acting
      map_add' :=
        smoothMetricCartanAction_add_tensor period hPeriod acting
      map_smul' := fun coefficient tensor =>
        smoothMetricCartanAction_smul_tensor
          period hPeriod acting coefficient tensor }
  map_add' := fun first second => by
    apply LinearMap.ext
    intro tensor
    exact smoothMetricCartanAction_add_acting
      period hPeriod first second tensor
  map_smul' := fun coefficient acting => by
    apply LinearMap.ext
    intro tensor
    exact smoothMetricCartanAction_smul_acting
      period hPeriod coefficient acting tensor

/-- Canonical Cartan-action data for smooth symmetric covariant tensors. -/
def symmetricTensorCartanActionData :
    SymmetricTensorCartanActionData period hPeriod where
  action := smoothMetricCartanActionBilinear period hPeriod
  cartan := by
    intro acting tensor first second
    exact smoothMetricCartanAction_cartan period hPeriod acting tensor
      first second

/-- Unconditional Lie representation of smooth D8 diffeomorphism ghosts on
intrinsic symmetric covariant tensors. -/
def smoothMetricCartanLieRepresentation :
    SmoothGhostLieRepresentation period hPeriod
      (SmoothSymmetricCovariantTwoTensor period hPeriod) :=
  (symmetricTensorCartanActionData period hPeriod)
    |>.toSmoothGhostLieRepresentation period hPeriod

theorem smoothMetricCartanAction_bracket
    (first second : Ghost period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    smoothMetricCartanAction period hPeriod
        (smoothGhostLieBracket period hPeriod first second) tensor =
      smoothMetricCartanAction period hPeriod first
          (smoothMetricCartanAction period hPeriod second tensor) -
        smoothMetricCartanAction period hPeriod second
          (smoothMetricCartanAction period hPeriod first tensor) :=
  (symmetricTensorCartanActionData period hPeriod).bracket_action
    period hPeriod first second tensor

end

end P0EFTJanusMappingTorusMetricCartanGlobalAction4D
end JanusFormal
