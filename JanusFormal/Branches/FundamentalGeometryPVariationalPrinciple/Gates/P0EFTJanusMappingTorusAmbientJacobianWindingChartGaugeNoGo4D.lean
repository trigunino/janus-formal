import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusAmbientPinMinusReferenceWindingFrontier4D
import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusAmbientSpinSO4Surjectivity4D
import Mathlib.Algebra.Quaternion
import Mathlib.Analysis.Quaternion

/-!
# Chart-gauge no-go for ambient Jacobian parity

The deck winding is intrinsic, whereas the sign of a coordinate Jacobian also
depends on the chosen orientation of the source and target charts.  Reversing
one chart by the already constructed reference reflection leaves every deck
winding unchanged and flips the determinant sign.  Consequently no function
of the winding alone can equal both coordinate parities until a compatible
orientation gauge for the atlas has been fixed.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusAmbientJacobianWindingChartGaugeNoGo4D

set_option autoImplicit false

noncomputable section

open scoped ContDiff

open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusAmbientTangentQuadraticReduction
open P0EFTJanusMappingTorusAmbientPinMinusProjection4D
open P0EFTJanusMappingTorusAmbientPinMinusCechExtension4D
open P0EFTJanusMappingTorusAmbientSpinSO4Surjectivity4D
open P0EFTJanusNormalBundleOrientationCover

/-- Reversing one coordinate chart changes the determinant by exactly a
minus sign. -/
theorem ambientChartOrientationFlip_det
    (transition : CoverCoordinates ≃ₗ[Real] CoverCoordinates) :
    (((LinearEquiv.det
      (transition.trans ambientPinMinusReferenceReflection) : Realˣ) : Real)) =
      -(((LinearEquiv.det transition : Realˣ) : Real)) := by
  rw [LinearEquiv.det_trans, ambientPinMinusReferenceReflection_det]
  norm_num

/-- The two coordinate orientation parities differ after reversing exactly
one chart. -/
theorem ambientLinearOrientationParity_chartFlip_ne
    (transition : CoverCoordinates ≃ₗ[Real] CoverCoordinates) :
    ambientLinearOrientationParity
        (transition.trans ambientPinMinusReferenceReflection) ≠
      ambientLinearOrientationParity transition := by
  let determinant : Real :=
    (((LinearEquiv.det transition : Realˣ) : Real))
  have hDeterminant : determinant ≠ 0 := by
    exact_mod_cast (LinearEquiv.det transition).ne_zero
  have hFlip :
      (((LinearEquiv.det
        (transition.trans ambientPinMinusReferenceReflection) : Realˣ) : Real)) =
        -determinant := by
    exact ambientChartOrientationFlip_det transition
  unfold ambientLinearOrientationParity
  rw [hFlip]
  change (if 0 < -determinant then (0 : ZMod 2) else 1) ≠
    (if 0 < determinant then 0 else 1)
  by_cases hPositive : 0 < determinant
  · have hFlipNotPositive : ¬ 0 < -determinant :=
      not_lt_of_ge (neg_nonpos.mpr (le_of_lt hPositive))
    simp [hPositive, hFlipNotPositive]
  · have hNegative : determinant < 0 :=
      lt_of_le_of_ne (le_of_not_gt hPositive) hDeterminant
    have hFlipPositive : 0 < -determinant := neg_pos.mpr hNegative
    simp [hPositive, hFlipPositive]

/-- No winding-only parity value can describe both choices of orientation for
one chart.  A chart-orientation gauge is therefore genuine input to any exact
Jacobian/winding comparison theorem. -/
theorem no_windingOnlyParity_without_chartOrientation
    (transition : CoverCoordinates ≃ₗ[Real] CoverCoordinates)
    (windingParity : ZMod 2) :
    ¬ (ambientLinearOrientationParity transition = windingParity ∧
      ambientLinearOrientationParity
        (transition.trans ambientPinMinusReferenceReflection) =
          windingParity) := by
  rintro ⟨hTransition, hFlipped⟩
  apply ambientLinearOrientationParity_chartFlip_ne transition
  exact hFlipped.trans hTransition.symm

/-- Central change of orthonormal frame.  In four dimensions it preserves the
quadratic form and does not alter the orientation component. -/
def ambientCentralOrthonormalFrameGauge :
    CoverCoordinates ≃ₗ[Real] CoverCoordinates :=
  LinearEquiv.neg Real

@[simp] theorem ambientCentralOrthonormalFrameGauge_apply
    (vector : CoverCoordinates) :
    ambientCentralOrthonormalFrameGauge vector = -vector := by
  rfl

theorem ambientCentralOrthonormalFrameGauge_isometry
    (vector : CoverCoordinates) :
    ambientCoverEuclideanQuadraticForm
        (ambientCentralOrthonormalFrameGauge vector) =
      ambientCoverEuclideanQuadraticForm vector := by
  simp only [ambientCentralOrthonormalFrameGauge_apply]
  exact QuadraticMap.map_neg ambientCoverEuclideanQuadraticForm vector

/-- Changing the target orthonormal frame by `-id` changes every transition,
even though it preserves the same Euclidean form. -/
theorem ambientOrthogonalTransition_centralFrameGauge_ne
    (transition : CoverCoordinates ≃ₗ[Real] CoverCoordinates) :
    transition.trans ambientCentralOrthonormalFrameGauge ≠ transition := by
  intro hEqual
  have hReference : ambientPinMinusReferenceVector ≠ 0 := by
    intro hZero
    have hSecond := congrArg Prod.snd hZero
    norm_num [ambientPinMinusReferenceVector] at hSecond
  have hImage : transition ambientPinMinusReferenceVector ≠ 0 :=
    by
      intro hZero
      apply hReference
      apply transition.injective
      simpa using hZero
  have hNeg :
      -(transition ambientPinMinusReferenceVector) =
        transition ambientPinMinusReferenceVector := by
    simpa [ambientCentralOrthonormalFrameGauge] using
      LinearEquiv.congr_fun hEqual ambientPinMinusReferenceVector
  have hAdd : transition ambientPinMinusReferenceVector +
      transition ambientPinMinusReferenceVector = 0 := by
    have hCongruence := congrArg
      (fun vector => vector + transition ambientPinMinusReferenceVector) hNeg
    simpa using hCongruence.symm
  have hSmul : (2 : Real) • transition ambientPinMinusReferenceVector = 0 := by
    simpa [two_smul Real] using hAdd
  exact hImage ((smul_eq_zero.mp hSmul).resolve_left (by norm_num))

/-- Consequently a winding (even together with its parity) cannot select one
exact `O(4)` transition until the local orthonormal-frame gauge is fixed. -/
theorem no_uniqueOrthogonalTransition_without_frameGauge
    (transition expected : CoverCoordinates ≃ₗ[Real] CoverCoordinates) :
    ¬ (transition = expected ∧
      transition.trans ambientCentralOrthonormalFrameGauge = expected) := by
  rintro ⟨hTransition, hGauged⟩
  apply ambientOrthogonalTransition_centralFrameGauge_ne transition
  exact hGauged.trans hTransition.symm

abbrev AmbientOrthogonalIsometry :=
  ambientCoverEuclideanQuadraticForm.IsometryEquiv
    ambientCoverEuclideanQuadraticForm

/-- Linear identification of the project's `(ℝ³, ℝ)` coordinates with
quaternions, with the last coordinate as the real component. -/
def ambientQuaternionLinearEquiv :
    CoverCoordinates ≃ₗ[Real] Quaternion Real where
  toFun vector :=
    ⟨vector.2, vector.1 0, vector.1 1, vector.1 2⟩
  invFun quaternion :=
    (WithLp.toLp 2 ![quaternion.imI, quaternion.imJ, quaternion.imK],
      quaternion.re)
  left_inv vector := by
    apply Prod.ext
    · ext index
      fin_cases index <;> rfl
    · rfl
  right_inv quaternion := by
    apply Quaternion.ext <;> rfl
  map_add' first second := by
    apply Quaternion.ext <;> rfl
  map_smul' scalar vector := by
    apply Quaternion.ext <;> rfl

@[simp] theorem ambientQuaternionLinearEquiv_referenceVector :
  ambientQuaternionLinearEquiv ambientPinMinusReferenceVector = 1 := by
  apply Quaternion.ext <;> rfl

theorem ambientQuaternionLinearEquiv_normSq
    (vector : CoverCoordinates) :
    Quaternion.normSq (ambientQuaternionLinearEquiv vector) =
      ambientCoverEuclideanQuadraticForm vector := by
  rw [Quaternion.normSq_def', ambientCoverEuclideanQuadraticForm_apply,
    EuclideanSpace.real_norm_sq_eq]
  simp only [ambientQuaternionLinearEquiv, Fin.sum_univ_succ]
  norm_num
  ring

@[simp] theorem ambientQuaternionLinearEquiv_neg
    (vector : CoverCoordinates) :
    ambientQuaternionLinearEquiv (-vector) =
      -ambientQuaternionLinearEquiv vector := by
  exact ambientQuaternionLinearEquiv.map_neg vector

/-- A unit normal, viewed as a unit quaternion. -/
def ambientUnitQuaternion
    (normal : CoverCoordinates)
    (hNormal : ambientCoverEuclideanQuadraticForm normal = 1) :
    Units (Quaternion Real) where
  val := ambientQuaternionLinearEquiv normal
  inv := star (ambientQuaternionLinearEquiv normal)
  val_inv := by
    rw [Quaternion.self_mul_star,
      ambientQuaternionLinearEquiv_normSq, hNormal]
    rfl
  inv_val := by
    rw [Quaternion.star_mul_self,
      ambientQuaternionLinearEquiv_normSq, hNormal]
    rfl

/-- Canonical global quaternionic orthogonal frame attached polynomially to a
unit normal.  It sends the reference real quaternion to that normal. -/
def ambientQuaternionFrame
    (normal : CoverCoordinates)
    (hNormal : ambientCoverEuclideanQuadraticForm normal = 1) :
    AmbientOrthogonalIsometry where
  __ := ambientQuaternionLinearEquiv.trans
    (((ambientUnitQuaternion normal hNormal).mulLeftLinearEquiv
      Real (Quaternion Real)).trans
        ambientQuaternionLinearEquiv.symm)
  map_app' vector := by
    rw [← ambientQuaternionLinearEquiv_normSq,
      ← ambientQuaternionLinearEquiv_normSq]
    change Quaternion.normSq
        (ambientQuaternionLinearEquiv normal *
          ambientQuaternionLinearEquiv vector) =
      Quaternion.normSq (ambientQuaternionLinearEquiv vector)
    rw [map_mul, ambientQuaternionLinearEquiv_normSq, hNormal, one_mul]

/-- Proof-independent joint application formula for the quaternionic frame. -/
def ambientQuaternionFrameApplication
    (input : CoverCoordinates × CoverCoordinates) : CoverCoordinates :=
  ambientQuaternionLinearEquiv.symm
    (ambientQuaternionLinearEquiv input.1 *
      ambientQuaternionLinearEquiv input.2)

theorem ambientQuaternionFrame_apply
    (normal vector : CoverCoordinates)
    (hNormal : ambientCoverEuclideanQuadraticForm normal = 1) :
    ambientQuaternionFrame normal hNormal vector =
      ambientQuaternionFrameApplication (normal, vector) := by
  rfl

/-- Reversing the local normal multiplies the whole quaternionic frame by the
central frame gauge `-id`; this is the exact overlap law required by the
one-sided normal bundle. -/
theorem ambientQuaternionFrameApplication_neg_normal
    (normal vector : CoverCoordinates) :
    ambientQuaternionFrameApplication (-normal, vector) =
      -ambientQuaternionFrameApplication (normal, vector) := by
  unfold ambientQuaternionFrameApplication
  rw [ambientQuaternionLinearEquiv_neg, neg_mul]
  exact ambientQuaternionLinearEquiv.symm.map_neg _

/-- All-winding version of the signed frame law, using the actual normal-line
orientation representation. -/
theorem ambientQuaternionFrameApplication_normalSign
    (winding : Int) (normal vector : CoverCoordinates) :
    ambientQuaternionFrameApplication
        ((normalSignRepresentation winding : Real) • normal, vector) =
      (normalSignRepresentation winding : Real) •
        ambientQuaternionFrameApplication (normal, vector) := by
  by_cases hEven : Even winding
  · rw [normal_sign_even winding hEven]
    simp
  · rw [normal_sign_odd winding hEven]
    simp only [Units.val_neg, Units.val_one, neg_smul, one_smul]
    exact ambientQuaternionFrameApplication_neg_normal normal vector

/-- The canonical frame application is globally polynomial, hence jointly
`C∞` in the unit normal and tangent vector. -/
theorem ambientQuaternionFrameApplication_contDiff :
    ContDiff Real ∞ ambientQuaternionFrameApplication := by
  let equivalence := ambientQuaternionLinearEquiv.toContinuousLinearEquiv
  change ContDiff Real ∞ (fun input : CoverCoordinates × CoverCoordinates =>
    equivalence.symm (equivalence input.1 * equivalence input.2))
  exact equivalence.symm.contDiff.comp
    ((equivalence.contDiff.comp contDiff_fst).mul
      (equivalence.contDiff.comp contDiff_snd))

/-- Any smooth unit-normal field therefore produces a jointly smooth aligned
frame application, with no local choices or pole singularity. -/
theorem ambientQuaternionFrameApplication_comp_contDiff
    {Parameter : Type*}
    [NormedAddCommGroup Parameter] [NormedSpace Real Parameter]
    (normal : Parameter → CoverCoordinates)
    (hNormal : ContDiff Real ∞ normal) :
    ContDiff Real ∞ (fun input : Parameter × CoverCoordinates =>
      ambientQuaternionFrameApplication (normal input.1, input.2)) := by
  exact ambientQuaternionFrameApplication_contDiff.comp
    ((hNormal.comp contDiff_fst).prodMk contDiff_snd)

/-- Euclidean normalization used to turn any nonzero atlas normal coordinate
into the unit input required by the quaternionic frame. -/
def ambientNormalizeNormal (normal : CoverCoordinates) : CoverCoordinates :=
  (Real.sqrt (ambientCoverEuclideanQuadraticForm normal))⁻¹ • normal

theorem ambientNormalizeNormal_unit
    (normal : CoverCoordinates) (hNormal : normal ≠ 0) :
    ambientCoverEuclideanQuadraticForm (ambientNormalizeNormal normal) = 1 := by
  have hPositive := ambientCoverEuclideanQuadraticForm_posDef normal hNormal
  have hSqrtPositive : 0 < Real.sqrt
      (ambientCoverEuclideanQuadraticForm normal) := Real.sqrt_pos.2 hPositive
  rw [ambientNormalizeNormal, QuadraticMap.map_smul]
  change (Real.sqrt (ambientCoverEuclideanQuadraticForm normal))⁻¹ *
      (Real.sqrt (ambientCoverEuclideanQuadraticForm normal))⁻¹ *
        ambientCoverEuclideanQuadraticForm normal = 1
  field_simp [ne_of_gt hSqrtPositive]
  nlinarith [Real.sq_sqrt hPositive.le]

@[simp] theorem ambientNormalizeNormal_neg
    (normal : CoverCoordinates) :
    ambientNormalizeNormal (-normal) = -ambientNormalizeNormal normal := by
  have hQuadratic : ambientCoverEuclideanQuadraticForm (-normal) =
      ambientCoverEuclideanQuadraticForm normal :=
    QuadraticMap.map_neg ambientCoverEuclideanQuadraticForm normal
  simp only [ambientNormalizeNormal, hQuadratic, smul_neg]

theorem ambientNormalizeNormal_normalSign
    (winding : Int) (normal : CoverCoordinates) :
    ambientNormalizeNormal
        ((normalSignRepresentation winding : Real) • normal) =
      (normalSignRepresentation winding : Real) •
        ambientNormalizeNormal normal := by
  by_cases hEven : Even winding
  · rw [normal_sign_even winding hEven]
    simp
  · rw [normal_sign_odd winding hEven]
    simp only [Units.val_neg, Units.val_one, neg_smul, one_smul,
      ambientNormalizeNormal_neg]

private theorem ambientCoverEuclideanQuadraticForm_contDiff :
    ContDiff Real ∞ ambientCoverEuclideanQuadraticForm := by
  rw [show (ambientCoverEuclideanQuadraticForm : CoverCoordinates → Real) =
      fun normal => ‖normal.1‖ ^ 2 + normal.2 ^ 2 by
    funext normal
    exact ambientCoverEuclideanQuadraticForm_apply normal]
  have hFirst : ContDiff Real ∞ (fun normal : CoverCoordinates =>
      ‖normal.1‖ ^ 2) :=
    (contDiff_norm_sq Real).comp contDiff_fst
  have hSecond : ContDiff Real ∞ (fun normal : CoverCoordinates =>
      normal.2 ^ 2) := contDiff_snd.pow 2
  exact hFirst.add hSecond

theorem ambientNormalizeNormal_contDiffAt
    (normal : CoverCoordinates) (hNormal : normal ≠ 0) :
    ContDiffAt Real ∞ ambientNormalizeNormal normal := by
  have hPositive := ambientCoverEuclideanQuadraticForm_posDef normal hNormal
  have hQuadratic : ContDiffAt Real ∞ ambientCoverEuclideanQuadraticForm normal :=
    ambientCoverEuclideanQuadraticForm_contDiff.contDiffAt
  have hSqrt := hQuadratic.sqrt (ne_of_gt hPositive)
  have hSqrtNe : Real.sqrt (ambientCoverEuclideanQuadraticForm normal) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hPositive)
  exact (hSqrt.inv hSqrtNe).smul contDiffAt_id

/-- Smooth nonvanishing normal fields normalize smoothly. -/
theorem ambientNormalizeNormal_comp_contDiff
    {Parameter : Type*}
    [NormedAddCommGroup Parameter] [NormedSpace Real Parameter]
    (normal : Parameter → CoverCoordinates)
    (hSmooth : ContDiff Real ∞ normal)
    (hNonzero : ∀ point, normal point ≠ 0) :
    ContDiff Real ∞ (fun point => ambientNormalizeNormal (normal point)) := by
  rw [contDiff_iff_contDiffAt]
  intro point
  exact (ambientNormalizeNormal_contDiffAt (normal point) (hNonzero point)).comp
    point hSmooth.contDiffAt

/-- Complete smooth pipeline from an arbitrary smooth nonvanishing normal
field to its canonical normalized quaternionic frame application. -/
theorem ambientQuaternionNormalizedFrameApplication_comp_contDiff
    {Parameter : Type*}
    [NormedAddCommGroup Parameter] [NormedSpace Real Parameter]
    (normal : Parameter → CoverCoordinates)
    (hSmooth : ContDiff Real ∞ normal)
    (hNonzero : ∀ point, normal point ≠ 0) :
    ContDiff Real ∞ (fun input : Parameter × CoverCoordinates =>
      ambientQuaternionFrameApplication
        (ambientNormalizeNormal (normal input.1), input.2)) :=
  ambientQuaternionFrameApplication_comp_contDiff
    (fun point => ambientNormalizeNormal (normal point))
    (ambientNormalizeNormal_comp_contDiff normal hSmooth hNonzero)

/-- Exact signed-overlap law for normalized quaternionic frames. -/
theorem ambientQuaternionNormalizedFrameApplication_sign_law
    {Parameter : Type*}
    (normal : Parameter → CoverCoordinates)
    (transition : Parameter → Parameter)
    (hSign : ∀ point, normal (transition point) = -normal point)
    (point : Parameter) (vector : CoverCoordinates) :
    ambientQuaternionFrameApplication
        (ambientNormalizeNormal (normal (transition point)), vector) =
      -ambientQuaternionFrameApplication
        (ambientNormalizeNormal (normal point), vector) := by
  rw [hSign point, ambientNormalizeNormal_neg,
    ambientQuaternionFrameApplication_neg_normal]

/-- Exact all-winding overlap law after normalization, expressed with the
already constructed normal-line deck character. -/
theorem ambientQuaternionNormalizedFrameApplication_normalSign
    (winding : Int) (normal vector : CoverCoordinates) :
    ambientQuaternionFrameApplication
        (ambientNormalizeNormal
          ((normalSignRepresentation winding : Real) • normal), vector) =
      (normalSignRepresentation winding : Real) •
        ambientQuaternionFrameApplication
          (ambientNormalizeNormal normal, vector) := by
  rw [ambientNormalizeNormal_normalSign,
    ambientQuaternionFrameApplication_normalSign]

/-- Pin-minus lift obtained from any nonzero local normal after Euclidean
normalization. -/
def ambientNormalizedPinMinusGenerator
    (normal : CoverCoordinates) (hNormal : normal ≠ 0) :
    AmbientCoordinatePinMinusGroup :=
  ambientPinMinusUnitNormalGenerator (ambientNormalizeNormal normal)
    (ambientNormalizeNormal_unit normal hNormal)

theorem ambientNormalizedPinMinusGenerator_square
    (normal : CoverCoordinates) (hNormal : normal ≠ 0) :
    ambientNormalizedPinMinusGenerator normal hNormal *
        ambientNormalizedPinMinusGenerator normal hNormal =
      ambientPinMinusCentralSign := by
  exact ambientPinMinusUnitNormalGenerator_square
    (ambientNormalizeNormal normal)
    (ambientNormalizeNormal_unit normal hNormal)

/-- Reversing a nonzero local normal changes its normalized Pin-minus lift by
the nontrivial central sign. -/
theorem ambientNormalizedPinMinusGenerator_neg
    (normal : CoverCoordinates)
    (hNormal : normal ≠ 0) (hNegNormal : -normal ≠ 0) :
    ambientNormalizedPinMinusGenerator (-normal) hNegNormal =
      ambientPinMinusCentralSign *
        ambientNormalizedPinMinusGenerator normal hNormal := by
  unfold ambientNormalizedPinMinusGenerator
  have hUnit := ambientNormalizeNormal_unit normal hNormal
  have hNegUnit : ambientCoverEuclideanQuadraticForm
      (-ambientNormalizeNormal normal) = 1 := by
    rw [← ambientNormalizeNormal_neg]
    exact ambientNormalizeNormal_unit (-normal) hNegNormal
  simpa only [ambientNormalizeNormal_neg] using
    ambientPinMinusUnitNormalGenerator_neg
      (ambientNormalizeNormal normal) hUnit hNegUnit

/-- Exact all-winding cocycle for the normalized Pin-minus lift. -/
theorem ambientNormalizedPinMinusGenerator_normalSign
    (winding : Int) (normal : CoverCoordinates)
    (hNormal : normal ≠ 0)
    (hSignedNormal :
      (normalSignRepresentation winding : Real) • normal ≠ 0) :
    ambientNormalizedPinMinusGenerator
        ((normalSignRepresentation winding : Real) • normal) hSignedNormal =
      if Even winding then ambientNormalizedPinMinusGenerator normal hNormal
      else ambientPinMinusCentralSign *
        ambientNormalizedPinMinusGenerator normal hNormal := by
  by_cases hEven : Even winding
  · simp only [if_pos hEven, normal_sign_even winding hEven,
      Units.val_one, one_smul]
  · simp only [if_neg hEven, normal_sign_odd winding hEven,
      Units.val_neg, Units.val_one, neg_smul, one_smul]
    exact ambientNormalizedPinMinusGenerator_neg normal hNormal
      (neg_ne_zero.mpr hNormal)

/-- The orthogonal projection of the normalized Pin-minus lift descends
through every normal-line deck winding. -/
theorem ambientNormalizedPinMinusProjection_normalSign
    (winding : Int) (normal : CoverCoordinates)
    (hNormal : normal ≠ 0)
    (hSignedNormal :
      (normalSignRepresentation winding : Real) • normal ≠ 0) :
    ambientPinMinusProjection
        (ambientNormalizedPinMinusGenerator
          ((normalSignRepresentation winding : Real) • normal)
          hSignedNormal) =
      ambientPinMinusProjection
        (ambientNormalizedPinMinusGenerator normal hNormal) := by
  rw [ambientNormalizedPinMinusGenerator_normalSign winding normal hNormal
    hSignedNormal]
  split_ifs
  · rfl
  · rw [map_mul, ambientPinMinusProjection_centralSign, one_mul]

/-- The full integer cyclic Pin-minus lift generated by a nonzero local
normal. -/
def ambientNormalizedPinMinusWindingLift
    (normal : CoverCoordinates) (hNormal : normal ≠ 0)
    (winding : Int) : AmbientCoordinatePinMinusGroup :=
  ambientPinMinusUnitNormalWindingLift (ambientNormalizeNormal normal)
    (ambientNormalizeNormal_unit normal hNormal) winding

@[simp] theorem ambientNormalizedPinMinusWindingLift_zero
    (normal : CoverCoordinates) (hNormal : normal ≠ 0) :
    ambientNormalizedPinMinusWindingLift normal hNormal 0 = 1 := by
  simp [ambientNormalizedPinMinusWindingLift]

/-- The local integer lift satisfies the strict cyclic cocycle law. -/
theorem ambientNormalizedPinMinusWindingLift_add
    (normal : CoverCoordinates) (hNormal : normal ≠ 0)
    (first second : Int) :
    ambientNormalizedPinMinusWindingLift normal hNormal (first + second) =
      ambientNormalizedPinMinusWindingLift normal hNormal first *
        ambientNormalizedPinMinusWindingLift normal hNormal second := by
  exact ambientPinMinusUnitNormalWindingLift_add
    (ambientNormalizeNormal normal)
    (ambientNormalizeNormal_unit normal hNormal) first second

/-- Reversing the local normal gauges every integer lift by the corresponding
power of the central Pin-minus sign. -/
theorem ambientNormalizedPinMinusWindingLift_neg
    (normal : CoverCoordinates)
    (hNormal : normal ≠ 0) (hNegNormal : -normal ≠ 0)
    (winding : Int) :
    ambientNormalizedPinMinusWindingLift (-normal) hNegNormal winding =
      ambientPinMinusCentralSign ^ winding *
        ambientNormalizedPinMinusWindingLift normal hNormal winding := by
  unfold ambientNormalizedPinMinusWindingLift
  have hUnit := ambientNormalizeNormal_unit normal hNormal
  have hNegUnit : ambientCoverEuclideanQuadraticForm
      (-ambientNormalizeNormal normal) = 1 := by
    rw [← ambientNormalizeNormal_neg]
    exact ambientNormalizeNormal_unit (-normal) hNegNormal
  simpa only [ambientNormalizeNormal_neg] using
    ambientPinMinusUnitNormalWindingLift_neg
      (ambientNormalizeNormal normal) hUnit hNegUnit winding

/-- Two-winding overlap law: one winding controls the normal-line chart sign,
while the other is the cyclic Pin-minus phase being lifted. -/
theorem ambientNormalizedPinMinusWindingLift_normalSign
    (overlapWinding liftWinding : Int) (normal : CoverCoordinates)
    (hNormal : normal ≠ 0)
    (hSignedNormal :
      (normalSignRepresentation overlapWinding : Real) • normal ≠ 0) :
    ambientNormalizedPinMinusWindingLift
        ((normalSignRepresentation overlapWinding : Real) • normal)
        hSignedNormal liftWinding =
      if Even overlapWinding then
        ambientNormalizedPinMinusWindingLift normal hNormal liftWinding
      else ambientPinMinusCentralSign ^ liftWinding *
        ambientNormalizedPinMinusWindingLift normal hNormal liftWinding := by
  by_cases hEven : Even overlapWinding
  · simp only [if_pos hEven,
      normal_sign_even overlapWinding hEven, Units.val_one, one_smul]
  · simp only [if_neg hEven,
      normal_sign_odd overlapWinding hEven, Units.val_neg, Units.val_one,
      neg_smul, one_smul]
    exact ambientNormalizedPinMinusWindingLift_neg normal hNormal
      (neg_ne_zero.mpr hNormal) liftWinding

/-- Projection of the cyclic lift is exactly the corresponding integer power
of the unit-normal reflection. -/
theorem ambientNormalizedPinMinusProjection_windingLift
    (normal : CoverCoordinates) (hNormal : normal ≠ 0)
    (winding : Int) :
    ambientPinMinusProjection
        (ambientNormalizedPinMinusWindingLift normal hNormal winding) =
      ambientPinMinusProjection
          (ambientNormalizedPinMinusGenerator normal hNormal) ^ winding := by
  exact ambientPinMinusProjection_unitNormalWindingLift
    (ambientNormalizeNormal normal)
    (ambientNormalizeNormal_unit normal hNormal) winding

@[simp] theorem ambientQuaternionFrame_apply_referenceVector
    (normal : CoverCoordinates)
    (hNormal : ambientCoverEuclideanQuadraticForm normal = 1) :
    ambientQuaternionFrame normal hNormal ambientPinMinusReferenceVector = normal := by
  change ambientQuaternionLinearEquiv.symm
      (ambientQuaternionLinearEquiv normal *
        ambientQuaternionLinearEquiv ambientPinMinusReferenceVector) = normal
  rw [ambientQuaternionLinearEquiv_referenceVector, mul_one,
    ambientQuaternionLinearEquiv.symm_apply_apply]

/-- The reference Pin-minus reflection regarded as an element of the actual
ambient orthogonal group. -/
def ambientPinMinusReferenceOrthogonalIsometry : AmbientOrthogonalIsometry where
  __ := ambientPinMinusReferenceReflection
  map_app' vector := by
    simp [ambientCoverEuclideanQuadraticForm_apply,
      ambientPinMinusReferenceReflection_apply]

/-- Reflection obtained after aligning the reference axis by an orthogonal
frame. -/
def ambientAlignedNormalReflection
    (frame : AmbientOrthogonalIsometry) : AmbientOrthogonalIsometry :=
  (frame.symm.trans ambientPinMinusReferenceOrthogonalIsometry).trans frame

/-- The Clifford generator of an aligned unit normal projects exactly to the
conjugated reference reflection. -/
theorem ambientPinMinusProjection_alignedUnitNormal
    (frame : AmbientOrthogonalIsometry)
    (hAligned : ambientCoverEuclideanQuadraticForm
      (frame ambientPinMinusReferenceVector) = 1) :
    ambientPinMinusProjection
        (ambientPinMinusUnitNormalGenerator
          (frame ambientPinMinusReferenceVector) hAligned) =
      (ambientAlignedNormalReflection frame).toLinearEquiv := by
  apply LinearEquiv.ext
  intro tangent
  have hReferenceGenerator :
      ambientPinMinusUnitNormalGenerator ambientPinMinusReferenceVector
          ambientPinMinusReferenceVector_positive_unit =
        ambientPinMinusReferenceGenerator := by
    apply Subtype.ext
    rfl
  have hReferenceFormula (vector : CoverCoordinates) :
      ambientPinMinusReferenceReflection vector =
        vector + QuadraticMap.polar ambientCoverPinMinusQuadraticForm
          ambientPinMinusReferenceVector vector •
            ambientPinMinusReferenceVector := by
    rw [← ambientPinMinusProjection_referenceGenerator,
      ← hReferenceGenerator]
    exact ambientPinMinusProjection_unitNormalGenerator_apply
      ambientPinMinusReferenceVector
      ambientPinMinusReferenceVector_positive_unit vector
  have hQuadratic (vector : CoverCoordinates) :
      ambientCoverPinMinusQuadraticForm (frame vector) =
        ambientCoverPinMinusQuadraticForm vector := by
    simp [ambientCoverPinMinusQuadraticForm, frame.map_app]
  have hPolar :
      QuadraticMap.polar ambientCoverPinMinusQuadraticForm
          (frame ambientPinMinusReferenceVector) tangent =
        QuadraticMap.polar ambientCoverPinMinusQuadraticForm
          ambientPinMinusReferenceVector (frame.symm tangent) := by
    let vector := frame.symm tangent
    have hTangent : tangent = frame vector := by
      exact (frame.apply_symm_apply tangent).symm
    rw [hTangent]
    simp only [QuadraticMap.polar]
    have hAdd : frame ambientPinMinusReferenceVector + frame vector =
        frame (ambientPinMinusReferenceVector + vector) :=
      (frame.toLinearEquiv.map_add _ _).symm
    rw [hAdd, hQuadratic, hQuadratic, hQuadratic]
    simp
  rw [ambientPinMinusProjection_unitNormalGenerator_apply]
  change tangent +
      QuadraticMap.polar ambientCoverPinMinusQuadraticForm
          (frame ambientPinMinusReferenceVector) tangent •
            frame ambientPinMinusReferenceVector =
    frame (ambientPinMinusReferenceReflection (frame.symm tangent))
  rw [hReferenceFormula, hPolar]
  simp

/-- For the canonical quaternionic aligning frame, the direct Clifford lift
projects to exactly the aligned reflection. -/
theorem ambientPinMinusProjection_quaternionUnitNormal
    (normal : CoverCoordinates)
    (hNormal : ambientCoverEuclideanQuadraticForm normal = 1) :
    ambientPinMinusProjection
        (ambientPinMinusUnitNormalGenerator normal hNormal) =
      (ambientAlignedNormalReflection
        (ambientQuaternionFrame normal hNormal)).toLinearEquiv := by
  have hAligned : ambientCoverEuclideanQuadraticForm
      (ambientQuaternionFrame normal hNormal
        ambientPinMinusReferenceVector) = 1 := by
    rw [ambientQuaternionFrame_apply_referenceVector]
    exact hNormal
  simpa only [ambientQuaternionFrame_apply_referenceVector] using
    ambientPinMinusProjection_alignedUnitNormal
      (ambientQuaternionFrame normal hNormal) hAligned

/-- Central `-id` as an element of the ambient quadratic isometry group. -/
def ambientCentralOrthogonalIsometry : AmbientOrthogonalIsometry where
  __ := ambientCentralOrthonormalFrameGauge
  map_app' vector := ambientCentralOrthonormalFrameGauge_isometry vector

/-- Conjugated reflections are insensitive to the central sign of the chosen
orthonormal frame. -/
theorem ambientAlignedNormalReflection_centralGauge
    (frame : AmbientOrthogonalIsometry) :
    ambientAlignedNormalReflection
        (frame.trans ambientCentralOrthogonalIsometry) =
      ambientAlignedNormalReflection frame := by
  apply DFunLike.coe_injective
  funext vector
  change -frame (ambientPinMinusReferenceOrthogonalIsometry
      (frame.symm (-vector))) =
    frame (ambientPinMinusReferenceOrthogonalIsometry (frame.symm vector))
  have hSymm : frame.symm (-vector) = -(frame.symm vector) :=
    frame.symm.toLinearEquiv.map_neg vector
  rw [hSymm]
  have hReference : ambientPinMinusReferenceOrthogonalIsometry
      (-(frame.symm vector)) =
        -ambientPinMinusReferenceOrthogonalIsometry (frame.symm vector) :=
    ambientPinMinusReferenceOrthogonalIsometry.toLinearEquiv.map_neg _
  rw [hReference]
  have hFrame : frame
      (-ambientPinMinusReferenceOrthogonalIsometry (frame.symm vector)) =
        -frame (ambientPinMinusReferenceOrthogonalIsometry (frame.symm vector)) :=
    frame.toLinearEquiv.map_neg _
  rw [hFrame]
  simp

theorem ambientQuaternionFrame_neg
    (normal : CoverCoordinates)
    (hNormal : ambientCoverEuclideanQuadraticForm normal = 1)
    (hNegNormal : ambientCoverEuclideanQuadraticForm (-normal) = 1) :
    ambientQuaternionFrame (-normal) hNegNormal =
      (ambientQuaternionFrame normal hNormal).trans
        ambientCentralOrthogonalIsometry := by
  apply DFunLike.coe_injective
  funext vector
  rw [ambientQuaternionFrame_apply]
  change ambientQuaternionFrameApplication (-normal, vector) =
    -ambientQuaternionFrame normal hNormal vector
  rw [ambientQuaternionFrame_apply]
  exact ambientQuaternionFrameApplication_neg_normal normal vector

/-- The aligned reflection is independent of the local sign chosen for the
one-sided normal. -/
theorem ambientQuaternionAlignedReflection_neg
    (normal : CoverCoordinates)
    (hNormal : ambientCoverEuclideanQuadraticForm normal = 1)
    (hNegNormal : ambientCoverEuclideanQuadraticForm (-normal) = 1) :
    ambientAlignedNormalReflection
        (ambientQuaternionFrame (-normal) hNegNormal) =
      ambientAlignedNormalReflection
        (ambientQuaternionFrame normal hNormal) := by
  rw [ambientQuaternionFrame_neg normal hNormal hNegNormal,
    ambientAlignedNormalReflection_centralGauge]

/-- Aligned reflection attached directly to an arbitrary nonzero local normal. -/
def ambientNormalizedQuaternionAlignedReflection
    (normal : CoverCoordinates) (hNormal : normal ≠ 0) :
    AmbientOrthogonalIsometry :=
  ambientAlignedNormalReflection
    (ambientQuaternionFrame (ambientNormalizeNormal normal)
      (ambientNormalizeNormal_unit normal hNormal))

/-- The normalized direct Clifford generator and the independently constructed
quaternionic aligned reflection have exactly the same orthogonal projection. -/
theorem ambientPinMinusProjection_normalizedGenerator_eq_alignedReflection
    (normal : CoverCoordinates) (hNormal : normal ≠ 0) :
    ambientPinMinusProjection
        (ambientNormalizedPinMinusGenerator normal hNormal) =
      (ambientNormalizedQuaternionAlignedReflection normal hNormal).toLinearEquiv := by
  exact ambientPinMinusProjection_quaternionUnitNormal
    (ambientNormalizeNormal normal)
    (ambientNormalizeNormal_unit normal hNormal)

/-- Every integer power of the normalized Clifford lift projects to the same
power of the sign-independent aligned reflection. -/
theorem ambientPinMinusProjection_normalizedWindingLift_eq_alignedReflection
    (normal : CoverCoordinates) (hNormal : normal ≠ 0)
    (winding : Int) :
    ambientPinMinusProjection
        (ambientNormalizedPinMinusWindingLift normal hNormal winding) =
      (ambientNormalizedQuaternionAlignedReflection normal hNormal).toLinearEquiv ^
        winding := by
  rw [ambientNormalizedPinMinusProjection_windingLift,
    ambientPinMinusProjection_normalizedGenerator_eq_alignedReflection]

/-- The normalized aligned reflection is a sign-independent local formula and
therefore descends through the one-sided normal overlap. -/
theorem ambientNormalizedQuaternionAlignedReflection_neg
    (normal : CoverCoordinates)
    (hNormal : normal ≠ 0)
    (hNegNormal : -normal ≠ 0) :
    ambientNormalizedQuaternionAlignedReflection (-normal) hNegNormal =
      ambientNormalizedQuaternionAlignedReflection normal hNormal := by
  unfold ambientNormalizedQuaternionAlignedReflection
  have hUnit := ambientNormalizeNormal_unit normal hNormal
  have hNegUnit : ambientCoverEuclideanQuadraticForm
      (-ambientNormalizeNormal normal) = 1 := by
    rw [← ambientNormalizeNormal_neg]
    exact ambientNormalizeNormal_unit (-normal) hNegNormal
  simpa only [ambientNormalizeNormal_neg] using
    ambientQuaternionAlignedReflection_neg
      (ambientNormalizeNormal normal) hUnit hNegUnit

/-- Full normal-cocycle descent of the aligned reflection for arbitrary deck
winding. -/
theorem ambientNormalizedQuaternionAlignedReflection_normalSign
    (winding : Int) (normal : CoverCoordinates)
    (hNormal : normal ≠ 0)
    (hSignedNormal :
      (normalSignRepresentation winding : Real) • normal ≠ 0) :
    ambientNormalizedQuaternionAlignedReflection
        ((normalSignRepresentation winding : Real) • normal) hSignedNormal =
      ambientNormalizedQuaternionAlignedReflection normal hNormal := by
  by_cases hEven : Even winding
  · simpa only [normal_sign_even winding hEven, Units.val_one, one_smul]
  · simpa only [normal_sign_odd winding hEven, Units.val_neg, Units.val_one,
      neg_smul, one_smul] using
      ambientNormalizedQuaternionAlignedReflection_neg
        normal hNormal (neg_ne_zero.mpr hNormal)

/-- The aligned reflection reverses exactly the aligned reference normal. -/
theorem ambientAlignedNormalReflection_apply_alignedNormal
    (frame : AmbientOrthogonalIsometry) :
    ambientAlignedNormalReflection frame
        (frame ambientPinMinusReferenceVector) =
      -(frame ambientPinMinusReferenceVector) := by
  change frame (ambientPinMinusReferenceOrthogonalIsometry
    (frame.symm (frame ambientPinMinusReferenceVector))) = _
  rw [QuadraticMap.IsometryEquiv.symm_apply_apply]
  change frame (ambientPinMinusReferenceReflection
    ambientPinMinusReferenceVector) = _
  rw [ambientPinMinusReferenceReflection_apply]
  simpa [ambientPinMinusReferenceVector] using
    frame.map_neg ambientPinMinusReferenceVector

/-- The aligning frame intertwines the aligned geometric reflection with the
fixed Pin-minus reference generator. -/
theorem ambientAlignedNormalReflection_intertwines
    (frame : AmbientOrthogonalIsometry) :
    frame.trans (ambientAlignedNormalReflection frame) =
      ambientPinMinusReferenceOrthogonalIsometry.trans frame := by
  apply DFunLike.coe_injective
  funext vector
  change frame (ambientPinMinusReferenceOrthogonalIsometry
      (frame.symm (frame vector))) =
    frame (ambientPinMinusReferenceOrthogonalIsometry vector)
  rw [QuadraticMap.IsometryEquiv.symm_apply_apply]

theorem ambientAlignedNormalReflection_linearEquiv_mul
    (frame : AmbientOrthogonalIsometry) :
    (ambientAlignedNormalReflection frame).toLinearEquiv * frame.toLinearEquiv =
      frame.toLinearEquiv *
        ambientPinMinusReferenceOrthogonalIsometry.toLinearEquiv := by
  apply LinearEquiv.ext
  intro vector
  exact congrArg (fun current : AmbientOrthogonalIsometry => current vector)
    (ambientAlignedNormalReflection_intertwines frame)

/-- Every unit ambient normal admits an honest orthogonal frame aligning the
fixed reference axis with that normal. -/
theorem exists_ambientNormalAligningFrame
    (normal : CoverCoordinates)
    (hNormal : ambientCoverEuclideanQuadraticForm normal = 1) :
    ∃ frame : AmbientOrthogonalIsometry,
      frame ambientPinMinusReferenceVector = normal := by
  apply exists_ambientOrthogonalIsometry_map_of_quadratic_eq
  rw [ambientPinMinusReferenceVector_positive_unit, hNormal]

/-- The exact pointwise frame gauge carrying one orthogonal transition to a
chosen target transition. -/
def ambientPointwiseOrthogonalGauge
    (actual expected : AmbientOrthogonalIsometry) :
    AmbientOrthogonalIsometry :=
  actual.symm.trans expected

/-- Pointwise gauge fixing always reaches the requested orthogonal matrix
exactly.  Smoothness and Cech coherence of this gauge family are separate
global obligations. -/
theorem ambientPointwiseOrthogonalGauge_exact
    (actual expected : AmbientOrthogonalIsometry) :
    actual.trans (ambientPointwiseOrthogonalGauge actual expected) = expected := by
  apply DFunLike.coe_injective
  funext vector
  change expected (actual.symm (actual vector)) = expected vector
  rw [QuadraticMap.IsometryEquiv.symm_apply_apply]

/-- The pointwise gauge is uniquely determined by the exact target equation. -/
theorem ambientPointwiseOrthogonalGauge_unique
    (actual expected gauge : AmbientOrthogonalIsometry)
    (hGauge : actual.trans gauge = expected) :
    gauge = ambientPointwiseOrthogonalGauge actual expected := by
  apply DFunLike.coe_injective
  funext vector
  have hApply := congrArg
    (fun current : AmbientOrthogonalIsometry => current (actual.symm vector))
    hGauge
  change gauge vector = expected (actual.symm vector)
  change gauge (actual (actual.symm vector)) =
    expected (actual.symm vector) at hApply
  rw [QuadraticMap.IsometryEquiv.apply_symm_apply] at hApply
  exact hApply

section CechGauge

variable {GaugeGroup : Type*} [Group GaugeGroup]

/-- Edge gauge carrying an actual transition to a target transition. -/
def cechEdgeGauge (actual expected : GaugeGroup) : GaugeGroup :=
  actual⁻¹ * expected

theorem actual_mul_cechEdgeGauge
    (actual expected : GaugeGroup) :
    actual * cechEdgeGauge actual expected = expected := by
  simp [cechEdgeGauge]

/-- If both transition systems obey their Cech laws, their edge gauges obey
the corresponding conjugation-twisted cocycle law. -/
theorem cechEdgeGauge_twisted_cocycle
    (actual₁₂ actual₂₃ actual₁₃ expected₁₂ expected₂₃ expected₁₃ : GaugeGroup)
    (hActual : actual₂₃ * actual₁₂ = actual₁₃)
    (hExpected : expected₂₃ * expected₁₂ = expected₁₃) :
    cechEdgeGauge actual₁₃ expected₁₃ =
      actual₁₂⁻¹ * cechEdgeGauge actual₂₃ expected₂₃ * actual₁₂ *
        cechEdgeGauge actual₁₂ expected₁₂ := by
  subst actual₁₃
  subst expected₁₃
  simp only [cechEdgeGauge, mul_inv_rev]
  group

/-- Conversely, the twisted edge-gauge law is exactly what is required for
the gauged target transitions to satisfy the Cech cocycle. -/
theorem expected_cocycle_of_cechEdgeGauge_twisted
    (actual₁₂ actual₂₃ actual₁₃ expected₁₂ expected₂₃ expected₁₃ : GaugeGroup)
    (hActual : actual₂₃ * actual₁₂ = actual₁₃)
    (hGauge : cechEdgeGauge actual₁₃ expected₁₃ =
      actual₁₂⁻¹ * cechEdgeGauge actual₂₃ expected₂₃ * actual₁₂ *
        cechEdgeGauge actual₁₂ expected₁₂) :
    expected₂₃ * expected₁₂ = expected₁₃ := by
  have hExpected₁₂ := actual_mul_cechEdgeGauge actual₁₂ expected₁₂
  have hExpected₂₃ := actual_mul_cechEdgeGauge actual₂₃ expected₂₃
  have hExpected₁₃ := actual_mul_cechEdgeGauge actual₁₃ expected₁₃
  rw [← hExpected₁₂, ← hExpected₂₃, ← hExpected₁₃, hGauge, ← hActual]
  group

/-- Change of an overlap transition induced by gauges on its source and target
frames.  This is the atlas-level notion needed to turn edge gauges into an
actual change of local orthonormal frames. -/
def vertexGaugedTransition
    (actual sourceGauge targetGauge : GaugeGroup) : GaugeGroup :=
  targetGauge⁻¹ * actual * sourceGauge

/-- Vertex frame gauges preserve the strict Cech law automatically. -/
theorem vertexGaugedTransition_cocycle
    (actual₁₂ actual₂₃ actual₁₃ gauge₁ gauge₂ gauge₃ : GaugeGroup)
    (hActual : actual₂₃ * actual₁₂ = actual₁₃) :
    vertexGaugedTransition actual₂₃ gauge₂ gauge₃ *
        vertexGaugedTransition actual₁₂ gauge₁ gauge₂ =
      vertexGaugedTransition actual₁₃ gauge₁ gauge₃ := by
  simp only [vertexGaugedTransition]
  rw [← hActual]
  group

/-- Exact form of the edge gauge produced by a pair of vertex frame gauges. -/
theorem cechEdgeGauge_vertexGaugedTransition
    (actual sourceGauge targetGauge : GaugeGroup) :
    cechEdgeGauge actual
        (vertexGaugedTransition actual sourceGauge targetGauge) =
      actual⁻¹ * targetGauge⁻¹ * actual * sourceGauge := by
  simp only [cechEdgeGauge, vertexGaugedTransition]
  group

/-- Once the target-chart gauge is fixed, the source-chart gauge realizing a
requested transition exists and is unique. -/
theorem vertexGauge_source_existsUnique
    (actual expected targetGauge : GaugeGroup) :
    ∃! sourceGauge,
      vertexGaugedTransition actual sourceGauge targetGauge = expected := by
  refine ⟨actual⁻¹ * targetGauge * expected, ?_, ?_⟩
  · simp only [vertexGaugedTransition]
    group
  · intro sourceGauge hSource
    simp only [vertexGaugedTransition] at hSource
    calc
      sourceGauge = actual⁻¹ * targetGauge *
          (targetGauge⁻¹ * actual * sourceGauge) := by group
      _ = actual⁻¹ * targetGauge * expected := by rw [hSource]

/-- Gauge propagated from a root chart along one overlap. -/
def propagatedVertexGauge
    (actualFromRoot expectedFromRoot rootGauge : GaugeGroup) : GaugeGroup :=
  actualFromRoot * rootGauge * expectedFromRoot⁻¹

/-- On any star-shaped Cech subatlas, the gauges propagated from one root
chart transform every actual transition into the requested target transition.
Thus the remaining obstruction is global path independence/regularity, not
local algebra on a common-root overlap. -/
theorem vertexGaugedTransition_propagated
    (actualRootFirst actualRootSecond actualFirstSecond : GaugeGroup)
    (expectedRootFirst expectedRootSecond expectedFirstSecond : GaugeGroup)
    (rootGauge : GaugeGroup)
    (hActual : actualFirstSecond * actualRootFirst = actualRootSecond)
    (hExpected : expectedFirstSecond * expectedRootFirst = expectedRootSecond) :
    vertexGaugedTransition actualFirstSecond
        (propagatedVertexGauge actualRootFirst expectedRootFirst rootGauge)
        (propagatedVertexGauge actualRootSecond expectedRootSecond rootGauge) =
      expectedFirstSecond := by
  subst actualRootSecond
  subst expectedRootSecond
  simp only [vertexGaugedTransition, propagatedVertexGauge, mul_inv_rev]
  group

/-- Exact holonomy obstruction to path-independent propagation around a loop:
the propagated gauge returns to its root value precisely when actual and
target loop holonomies are intertwined by the root gauge. -/
theorem propagatedVertexGauge_loop_eq_root_iff
    (actualHolonomy expectedHolonomy rootGauge : GaugeGroup) :
    propagatedVertexGauge actualHolonomy expectedHolonomy rootGauge = rootGauge ↔
      actualHolonomy * rootGauge = rootGauge * expectedHolonomy := by
  constructor
  · intro hLoop
    calc
      actualHolonomy * rootGauge =
          (actualHolonomy * rootGauge * expectedHolonomy⁻¹) *
            expectedHolonomy := by group
      _ = rootGauge * expectedHolonomy := by
        rw [show actualHolonomy * rootGauge * expectedHolonomy⁻¹ = rootGauge by
          exact hLoop]
  · intro hHolonomy
    change actualHolonomy * rootGauge * expectedHolonomy⁻¹ = rootGauge
    rw [hHolonomy]
    group

/-- Equal actual and target transports along two paths give identical
propagated vertex gauges. -/
theorem propagatedVertexGauge_path_independent
    (actualFirst actualSecond expectedFirst expectedSecond rootGauge : GaugeGroup)
    (hActual : actualFirst = actualSecond)
    (hExpected : expectedFirst = expectedSecond) :
    propagatedVertexGauge actualFirst expectedFirst rootGauge =
      propagatedVertexGauge actualSecond expectedSecond rootGauge := by
  rw [hActual, hExpected]

/-- For the cyclic mapping-torus holonomy, intertwining the single generator
intertwines every positive or negative winding. -/
theorem integerHolonomy_intertwined_of_generator
    (actualGenerator expectedGenerator rootGauge : GaugeGroup)
    (hGenerator : actualGenerator * rootGauge = rootGauge * expectedGenerator)
    (winding : Int) :
    actualGenerator ^ winding * rootGauge =
      rootGauge * expectedGenerator ^ winding := by
  have hSemiconj : SemiconjBy rootGauge expectedGenerator actualGenerator :=
    hGenerator.symm
  exact (hSemiconj.zpow_right winding).symm

/-- Consequently the propagated gauge closes around every integer winding as
soon as the two mapping-torus generators are intertwined once. -/
theorem propagatedVertexGauge_integerHolonomy_eq_root
    (actualGenerator expectedGenerator rootGauge : GaugeGroup)
    (hGenerator : actualGenerator * rootGauge = rootGauge * expectedGenerator)
    (winding : Int) :
    propagatedVertexGauge (actualGenerator ^ winding)
        (expectedGenerator ^ winding) rootGauge = rootGauge :=
  (propagatedVertexGauge_loop_eq_root_iff
    (actualGenerator ^ winding) (expectedGenerator ^ winding) rootGauge).2
      (integerHolonomy_intertwined_of_generator actualGenerator
        expectedGenerator rootGauge hGenerator winding)

/-- The normal-aligned orthogonal model therefore has exactly the reference
Pin-minus holonomy for every mapping-torus winding. -/
theorem ambientAlignedNormalReflection_integerHolonomy_eq_root
    (frame : AmbientOrthogonalIsometry)
    (winding : Int) :
    propagatedVertexGauge
        ((ambientAlignedNormalReflection frame).toLinearEquiv ^ winding)
        (ambientPinMinusReferenceOrthogonalIsometry.toLinearEquiv ^ winding)
        frame.toLinearEquiv = frame.toLinearEquiv :=
  propagatedVertexGauge_integerHolonomy_eq_root
    (ambientAlignedNormalReflection frame).toLinearEquiv
    ambientPinMinusReferenceOrthogonalIsometry.toLinearEquiv
    frame.toLinearEquiv
    (ambientAlignedNormalReflection_linearEquiv_mul frame)
    winding

/-- Pointwise closure of the normal-aligned model: for every unit normal there
is a frame whose aligned reflection reverses it and whose gauge closes for all
integer windings.  Smooth dependence of this choice is deliberately separate. -/
theorem exists_ambientNormalAlignedAllWindingGauge
    (normal : CoverCoordinates)
    (hNormal : ambientCoverEuclideanQuadraticForm normal = 1)
    (winding : Int) :
    ∃ frame : AmbientOrthogonalIsometry,
      frame ambientPinMinusReferenceVector = normal ∧
      ambientAlignedNormalReflection frame normal = -normal ∧
      propagatedVertexGauge
          ((ambientAlignedNormalReflection frame).toLinearEquiv ^ winding)
          (ambientPinMinusReferenceOrthogonalIsometry.toLinearEquiv ^ winding)
          frame.toLinearEquiv = frame.toLinearEquiv := by
  obtain ⟨frame, hFrame⟩ := exists_ambientNormalAligningFrame normal hNormal
  refine ⟨frame, hFrame, ?_,
    ambientAlignedNormalReflection_integerHolonomy_eq_root frame winding⟩
  rw [← hFrame]
  exact ambientAlignedNormalReflection_apply_alignedNormal frame

end CechGauge

end

end P0EFTJanusMappingTorusAmbientJacobianWindingChartGaugeNoGo4D
end JanusFormal
