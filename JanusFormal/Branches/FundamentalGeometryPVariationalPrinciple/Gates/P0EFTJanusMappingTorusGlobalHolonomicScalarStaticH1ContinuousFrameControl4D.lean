import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGlobalHolonomicScalarStaticH1FrameControl4D

/-!
# Continuous finite-frame coefficients in holonomic coordinates

The model tangent space is the fixed four-dimensional space
`CoverCoordinates`, so every genuine smooth tangent generator has explicit
global holonomic coefficients algebraically.  For a nontrivial tangent
bundle, smoothness of the section does not expose those raw model-space
coefficients as one globally continuous function.  This gate therefore uses
the minimal replacement: continuous coefficients on a finite closed cover.
Compactness then gives one uniform matrix bound and closes the geometric
frame-control reduction.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusGlobalHolonomicScalarStaticH1ContinuousFrameControl4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff BigOperators Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarAction4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarWeakJacobiRiesz4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarStaticH1UniformEllipticity4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarStaticH1FrameControl4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

/-- Coefficients in the time-first ordering of `tangentCoordinate`. -/
def holonomicVectorCoefficient
    (vector : CoverCoordinates) (index : Fin 4) : Real :=
  Fin.cases vector.2 (fun spatial : Fin 3 => vector.1 spatial) index

theorem holonomicVectorCoefficient_zero (vector : CoverCoordinates) :
    holonomicVectorCoefficient vector 0 = vector.2 := by
  rfl

theorem holonomicVectorCoefficient_succ
    (vector : CoverCoordinates) (index : Fin 3) :
    holonomicVectorCoefficient vector index.succ = vector.1 index := by
  rfl

/-- The four fixed holonomic vectors are an explicit spanning basis of the
model tangent space. -/
theorem holonomic_vector_decomposition (vector : CoverCoordinates) :
    ∑ index : Fin 4,
        holonomicVectorCoefficient vector index • tangentCoordinate index =
      vector := by
  rw [Fin.sum_univ_succ]
  apply Prod.ext
  · ext spatial
    simp [tangentCoordinate, holonomicVectorCoefficient, Prod.fst_sum]
    simpa only [Fin.ext_iff] using
      (Fintype.sum_ite_eq' spatial
        (fun index : Fin 3 => vector.1 index))
  · simp [tangentCoordinate, holonomicVectorCoefficient, Prod.snd_sum]

/-- Global coefficient matrix of a genuine smooth tangent generating family. -/
def smoothFrameHolonomicCoefficient
    (frame : SmoothD8Frame period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (frameIndex : Fin frame.count) (holonomicIndex : Fin 4) : Real :=
  holonomicVectorCoefficient (frame.vectorAt point frameIndex) holonomicIndex

theorem smoothFrameHolonomicCoefficient_vector_decomposition
    (frame : SmoothD8Frame period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (frameIndex : Fin frame.count) :
    ∑ holonomicIndex : Fin 4,
        smoothFrameHolonomicCoefficient period hPeriod frame point frameIndex
            holonomicIndex • tangentCoordinate holonomicIndex =
      frame.vectorAt point frameIndex :=
  holonomic_vector_decomposition (frame.vectorAt point frameIndex)

set_option backward.isDefEq.respectTransparency false in
theorem smoothFrameHolonomicCoefficient_covector_decomposition
    (frame : SmoothD8Frame period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (frameIndex : Fin frame.count)
    (covector : TangentSpace coverModelWithCorners point →ₗ[Real] Real) :
    covector (frame.vectorAt point frameIndex) =
      ∑ holonomicIndex : Fin 4,
        smoothFrameHolonomicCoefficient period hPeriod frame point frameIndex
            holonomicIndex * covector (tangentCoordinate holonomicIndex) := by
  rw [← smoothFrameHolonomicCoefficient_vector_decomposition period hPeriod frame
    point frameIndex, map_sum]
  apply Finset.sum_congr rfl
  intro holonomicIndex _
  rw [map_smul]
  rfl

/-- Minimal local-finite replacement for unavailable global continuity of raw
model-space coefficients.  Closed patches cover the compact quotient; on
each patch the same finite-frame vectors have continuous holonomic
coefficients. -/
structure LocalFiniteHolonomicFrameCoefficients
    (frame : SmoothD8Frame period hPeriod) where
  patchCount : Nat
  closedPatch : Fin patchCount → Set (EffectiveQuotient period hPeriod)
  closedPatch_isClosed : ∀ patch, IsClosed (closedPatch patch)
  covers : ∀ point, ∃ patch, point ∈ closedPatch patch
  coefficients : Fin patchCount → EffectiveQuotient period hPeriod →
    Fin frame.count → Fin 4 → Real
  continuousOn_coefficients : ∀ patch frameIndex holonomicIndex,
    ContinuousOn
      (fun point => coefficients patch point frameIndex holonomicIndex)
      (closedPatch patch)
  covector_decomposition : ∀ patch point, point ∈ closedPatch patch →
      ∀ frameIndex
        (covector : TangentSpace coverModelWithCorners point →ₗ[Real] Real),
        covector (frame.vectorAt point frameIndex) =
          ∑ holonomicIndex : Fin 4,
            coefficients patch point frameIndex holonomicIndex *
              covector (tangentCoordinate holonomicIndex)

/-- A deterministic patch choice turns local coefficients into one global
algebraic coefficient matrix; continuity is only used before this choice. -/
def LocalFiniteHolonomicFrameCoefficients.chosenPatch
    {frame : SmoothD8Frame period hPeriod}
    (patchData : LocalFiniteHolonomicFrameCoefficients period hPeriod frame)
    (point : EffectiveQuotient period hPeriod) : Fin patchData.patchCount :=
  (patchData.covers point).choose

theorem LocalFiniteHolonomicFrameCoefficients.chosenPatch_mem
    {frame : SmoothD8Frame period hPeriod}
    (patchData : LocalFiniteHolonomicFrameCoefficients period hPeriod frame)
    (point : EffectiveQuotient period hPeriod) :
    point ∈ patchData.closedPatch
      (LocalFiniteHolonomicFrameCoefficients.chosenPatch period hPeriod
        patchData point) :=
  (patchData.covers point).choose_spec

def LocalFiniteHolonomicFrameCoefficients.globalCoefficient
    {frame : SmoothD8Frame period hPeriod}
    (patchData : LocalFiniteHolonomicFrameCoefficients period hPeriod frame)
    (point : EffectiveQuotient period hPeriod)
    (frameIndex : Fin frame.count) (holonomicIndex : Fin 4) : Real :=
  patchData.coefficients
    (LocalFiniteHolonomicFrameCoefficients.chosenPatch period hPeriod
      patchData point) point frameIndex holonomicIndex

theorem LocalFiniteHolonomicFrameCoefficients.globalCoefficient_decomposition
    {frame : SmoothD8Frame period hPeriod}
    (patchData : LocalFiniteHolonomicFrameCoefficients period hPeriod frame)
    (point : EffectiveQuotient period hPeriod)
    (frameIndex : Fin frame.count)
    (covector : TangentSpace coverModelWithCorners point →ₗ[Real] Real) :
    covector (frame.vectorAt point frameIndex) =
      ∑ holonomicIndex : Fin 4,
        LocalFiniteHolonomicFrameCoefficients.globalCoefficient period hPeriod
          patchData point frameIndex holonomicIndex *
          covector (tangentCoordinate holonomicIndex) :=
  patchData.covector_decomposition
    (LocalFiniteHolonomicFrameCoefficients.chosenPatch period hPeriod
      patchData point) point
    (LocalFiniteHolonomicFrameCoefficients.chosenPatch_mem period hPeriod
      patchData point) frameIndex covector

/-- Finiteness of the patch cover and compactness of each closed patch give a
single positive square bound for all chosen coefficients. -/
theorem LocalFiniteHolonomicFrameCoefficients.exists_uniform_square_bound
    {frame : SmoothD8Frame period hPeriod}
    (patchData : LocalFiniteHolonomicFrameCoefficients period hPeriod frame) :
    ∃ bound : Real, 0 < bound ∧ ∀ point frameIndex holonomicIndex,
      LocalFiniteHolonomicFrameCoefficients.globalCoefficient period hPeriod
        patchData point frameIndex holonomicIndex ^ 2 ≤ bound := by
  have hContinuousOn (patch : Fin patchData.patchCount) :
      ContinuousOn
        (fun point : EffectiveQuotient period hPeriod =>
          ‖fun frameIndex holonomicIndex =>
            patchData.coefficients patch point frameIndex holonomicIndex‖)
        (patchData.closedPatch patch) := by
    apply ContinuousOn.norm
    apply continuousOn_pi.2
    intro frameIndex
    apply continuousOn_pi.2
    intro holonomicIndex
    exact patchData.continuousOn_coefficients patch frameIndex holonomicIndex
  have hPatchBound (patch : Fin patchData.patchCount) :
      ∃ upper : Real, ∀ point ∈ patchData.closedPatch patch,
        ‖fun frameIndex holonomicIndex =>
          patchData.coefficients patch point frameIndex holonomicIndex‖ ≤ upper := by
    rcases (patchData.closedPatch_isClosed patch).isCompact.bddAbove_image
        (hContinuousOn patch) with ⟨upper, hUpper⟩
    exact ⟨upper, fun point hPoint =>
      hUpper ⟨point, hPoint, rfl⟩⟩
  let upper : Fin patchData.patchCount → Real :=
    fun patch => (hPatchBound patch).choose
  have hUpper (patch : Fin patchData.patchCount) point
      (hPoint : point ∈ patchData.closedPatch patch) :
      ‖fun frameIndex holonomicIndex =>
        patchData.coefficients patch point frameIndex holonomicIndex‖ ≤ upper patch :=
    (hPatchBound patch).choose_spec point hPoint
  let normBound := ∑ patch : Fin patchData.patchCount, |upper patch| + 1
  refine ⟨normBound ^ 2, sq_pos_of_pos ?_, ?_⟩
  · dsimp only [normBound]
    positivity
  · intro point frameIndex holonomicIndex
    let patch := LocalFiniteHolonomicFrameCoefficients.chosenPatch period hPeriod
      patchData point
    have hEntry : ‖LocalFiniteHolonomicFrameCoefficients.globalCoefficient
        period hPeriod patchData point frameIndex holonomicIndex‖ ≤
        normBound := by
      calc
        _ ≤ ‖fun frameIndex holonomicIndex =>
            patchData.coefficients patch point frameIndex holonomicIndex‖ :=
          (norm_le_pi_norm
            (fun holonomicIndex =>
              patchData.coefficients patch point frameIndex holonomicIndex)
              holonomicIndex).trans
            (norm_le_pi_norm
              (fun frameIndex holonomicIndex =>
                patchData.coefficients patch point frameIndex holonomicIndex)
              frameIndex)
        _ ≤ upper patch := hUpper patch point
          (LocalFiniteHolonomicFrameCoefficients.chosenPatch_mem period hPeriod
            patchData point)
        _ ≤ |upper patch| := le_abs_self _
        _ ≤ ∑ patch : Fin patchData.patchCount, |upper patch| := by
          exact Finset.single_le_sum (fun index _ => abs_nonneg (upper index))
            (Finset.mem_univ patch)
        _ ≤ normBound := by dsimp only [normBound]; linarith
    have hSquare := mul_self_le_mul_self (norm_nonneg _) hEntry
    simpa [Real.norm_eq_abs, sq_abs, pow_two] using hSquare

private theorem four_coordinate_linear_combination_sq_le
    (coefficients covector : Fin 4 → Real) (bound : Real)
    (_hBound : 0 ≤ bound)
    (hCoefficient : ∀ index, coefficients index ^ 2 ≤ bound) :
    (∑ index : Fin 4, coefficients index * covector index) ^ 2 ≤
      4 * bound * ∑ index : Fin 4, covector index ^ 2 := by
  have hCauchy :
      (∑ index : Fin 4, coefficients index * covector index) ^ 2 ≤
        (∑ index : Fin 4, coefficients index ^ 2) *
          ∑ index : Fin 4, covector index ^ 2 := by
    simpa using
      (Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin 4))
        coefficients covector)
  have hCoefficientSum :
      (∑ index : Fin 4, coefficients index ^ 2) ≤ 4 * bound := by
    calc
      _ ≤ ∑ _index : Fin 4, bound :=
        Finset.sum_le_sum fun index _ => hCoefficient index
      _ = 4 * bound := by simp
  have hCovectorSum : 0 ≤ ∑ index : Fin 4, covector index ^ 2 :=
    Finset.sum_nonneg fun index _ => sq_nonneg (covector index)
  exact hCauchy.trans
    (mul_le_mul_of_nonneg_right hCoefficientSum hCovectorSum)

private theorem finite_frame_coordinate_bound_of_square_bound
    (frame : SmoothD8Frame period hPeriod)
    (coefficients : EffectiveQuotient period hPeriod →
      Fin frame.count → Fin 4 → Real)
    (bound : Real) (hBound : 0 ≤ bound)
    (hCoefficient : ∀ point frameIndex holonomicIndex,
      coefficients point frameIndex holonomicIndex ^ 2 ≤ bound) :
    ∀ point (value : Real) (covector : Fin 4 → Real),
      ‖(value, fun frameIndex =>
        ∑ holonomicIndex : Fin 4,
          coefficients point frameIndex holonomicIndex *
            covector holonomicIndex)‖ ^ 2 ≤
        (2 + 8 * (frame.count : Real) ^ 2 * bound) *
          (value ^ 2 + ∑ holonomicIndex : Fin 4,
            covector holonomicIndex ^ 2) := by
  intro point value covector
  let transformed : Fin frame.count → Real := fun frameIndex =>
    ∑ holonomicIndex : Fin 4,
      coefficients point frameIndex holonomicIndex * covector holonomicIndex
  let covectorSquare := ∑ holonomicIndex : Fin 4,
    covector holonomicIndex ^ 2
  let derivativeAbsSum := ∑ frameIndex : Fin frame.count,
    |transformed frameIndex|
  have hCovectorSquare : 0 ≤ covectorSquare :=
    Finset.sum_nonneg fun index _ => sq_nonneg (covector index)
  have hComponent (frameIndex : Fin frame.count) :
      transformed frameIndex ^ 2 ≤ 4 * bound * covectorSquare := by
    exact four_coordinate_linear_combination_sq_le
      (fun holonomicIndex =>
        coefficients point frameIndex holonomicIndex)
      covector bound hBound (hCoefficient point frameIndex)
  have hComponentSum :
      (∑ frameIndex : Fin frame.count, transformed frameIndex ^ 2) ≤
        (frame.count : Real) * (4 * bound * covectorSquare) := by
    calc
      _ ≤ ∑ _frameIndex : Fin frame.count, 4 * bound * covectorSquare :=
        Finset.sum_le_sum fun frameIndex _ => hComponent frameIndex
      _ = (frame.count : Real) * (4 * bound * covectorSquare) := by simp
  have hAbsCauchy :
      derivativeAbsSum ^ 2 ≤
        (frame.count : Real) *
          ∑ frameIndex : Fin frame.count, transformed frameIndex ^ 2 := by
    dsimp only [derivativeAbsSum]
    simpa [sq_abs] using
      (sq_sum_le_card_mul_sum_sq
        (s := (Finset.univ : Finset (Fin frame.count)))
        (f := fun frameIndex => |transformed frameIndex|))
  have hCount : 0 ≤ (frame.count : Real) := Nat.cast_nonneg _
  have hAbsSumSquare :
      derivativeAbsSum ^ 2 ≤
        4 * (frame.count : Real) ^ 2 * bound * covectorSquare := by
    calc
      derivativeAbsSum ^ 2 ≤
          (frame.count : Real) *
            ∑ frameIndex : Fin frame.count, transformed frameIndex ^ 2 :=
        hAbsCauchy
      _ ≤ (frame.count : Real) *
          ((frame.count : Real) * (4 * bound * covectorSquare)) :=
        mul_le_mul_of_nonneg_left hComponentSum hCount
      _ = 4 * (frame.count : Real) ^ 2 * bound * covectorSquare := by ring
  have hDerivativeAbsSum : 0 ≤ derivativeAbsSum :=
    Finset.sum_nonneg fun frameIndex _ => abs_nonneg (transformed frameIndex)
  have hDerivativeNorm : ‖transformed‖ ≤ derivativeAbsSum := by
    apply (pi_norm_le_iff_of_nonneg hDerivativeAbsSum).2
    intro frameIndex
    rw [Real.norm_eq_abs]
    dsimp only [derivativeAbsSum]
    exact Finset.single_le_sum
      (fun index _ => abs_nonneg (transformed index))
      (Finset.mem_univ frameIndex)
  have hJetNorm : ‖(value, transformed)‖ ≤ |value| + derivativeAbsSum := by
    rw [Prod.norm_mk]
    apply max_le
    · rw [Real.norm_eq_abs]
      exact le_add_of_nonneg_right hDerivativeAbsSum
    · exact hDerivativeNorm.trans
        (le_add_of_nonneg_left (abs_nonneg value))
  have hJetSquare :
      ‖(value, transformed)‖ ^ 2 ≤
        (|value| + derivativeAbsSum) ^ 2 := by
    simpa [pow_two] using
      (mul_self_le_mul_self (norm_nonneg (value, transformed)) hJetNorm)
  have hAddSquare :
      (|value| + derivativeAbsSum) ^ 2 ≤
        2 * value ^ 2 + 2 * derivativeAbsSum ^ 2 := by
    nlinarith [sq_nonneg (|value| - derivativeAbsSum), sq_abs value]
  let coefficient := 8 * (frame.count : Real) ^ 2 * bound
  have hCoefficientNonneg : 0 ≤ coefficient := by
    dsimp only [coefficient]
    positivity
  change ‖(value, transformed)‖ ^ 2 ≤
    (2 + coefficient) * (value ^ 2 + covectorSquare)
  calc
    ‖(value, transformed)‖ ^ 2 ≤
        (|value| + derivativeAbsSum) ^ 2 := hJetSquare
    _ ≤ 2 * value ^ 2 + 2 * derivativeAbsSum ^ 2 := hAddSquare
    _ ≤ 2 * value ^ 2 + coefficient * covectorSquare := by
      apply add_le_add_right
      dsimp only [coefficient]
      nlinarith
    _ ≤ 2 * (value ^ 2 + covectorSquare) +
        coefficient * (value ^ 2 + covectorSquare) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left
          (le_add_of_nonneg_right hCovectorSquare) (by norm_num)
      · exact mul_le_mul_of_nonneg_left
          (le_add_of_nonneg_left (sq_nonneg value)) hCoefficientNonneg
    _ = (2 + coefficient) * (value ^ 2 + covectorSquare) := by ring

/-- The local-finite continuous transition contract supplies the exact
field-independent global control required by the static graph bridge. -/
def LocalFiniteHolonomicFrameCoefficients.toStaticScalarHolonomicFrameControl
    {frame : SmoothD8Frame period hPeriod}
    (patchData : LocalFiniteHolonomicFrameCoefficients period hPeriod frame) :
    StaticScalarHolonomicFrameControl period hPeriod frame := by
  let bound :=
    (LocalFiniteHolonomicFrameCoefficients.exists_uniform_square_bound
      period hPeriod patchData).choose
  have hBound : 0 < bound :=
    (LocalFiniteHolonomicFrameCoefficients.exists_uniform_square_bound
      period hPeriod patchData).choose_spec.1
  have hCoefficient :=
    (LocalFiniteHolonomicFrameCoefficients.exists_uniform_square_bound
      period hPeriod patchData).choose_spec.2
  let coefficients := fun point frameIndex holonomicIndex =>
    LocalFiniteHolonomicFrameCoefficients.globalCoefficient period hPeriod
      patchData point frameIndex holonomicIndex
  refine
    { coefficients := coefficients
      covector_decomposition := ?_
      constant := 2 + 8 * (frame.count : Real) ^ 2 * bound
      constant_nonneg := by positivity
      coordinate_bound := ?_ }
  · intro point frameIndex covector
    exact LocalFiniteHolonomicFrameCoefficients.globalCoefficient_decomposition
      period hPeriod patchData point frameIndex covector
  · exact finite_frame_coordinate_bound_of_square_bound period hPeriod frame
      coefficients bound hBound.le hCoefficient

/-- Specialization to the actual unconditional finite smooth tangent family.
Only the local transition-coefficient contract remains as geometric input. -/
def finiteSmoothTangentFrameHolonomicControl
    (patchData : LocalFiniteHolonomicFrameCoefficients period hPeriod
      (finiteSmoothTangentFrame period hPeriod)) :
    StaticScalarHolonomicFrameControl period hPeriod
      (finiteSmoothTangentFrame period hPeriod) :=
  LocalFiniteHolonomicFrameCoefficients.toStaticScalarHolonomicFrameControl
    period hPeriod patchData

/-- The local-finite transition contract therefore closes the pointwise H¹
ellipticity input for the constructed smooth tangent family. -/
def finiteSmoothTangentFrameUniformGraphEllipticity
    (data : PositiveStaticGlobalScalarData period hPeriod)
    (patchData : LocalFiniteHolonomicFrameCoefficients period hPeriod
      (finiteSmoothTangentFrame period hPeriod)) :
    StaticScalarUniformGraphEllipticity period hPeriod data
      (finiteSmoothTangentFrame period hPeriod) :=
  StaticScalarHolonomicFrameControl.toUniformGraphEllipticity period hPeriod
    data (finiteSmoothTangentFrame period hPeriod)
      (finiteSmoothTangentFrameHolonomicControl period hPeriod patchData)

end

end P0EFTJanusMappingTorusGlobalHolonomicScalarStaticH1ContinuousFrameControl4D
end JanusFormal
