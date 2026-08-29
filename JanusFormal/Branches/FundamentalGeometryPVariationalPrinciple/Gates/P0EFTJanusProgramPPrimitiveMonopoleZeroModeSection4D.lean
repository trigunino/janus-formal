import Mathlib.Analysis.SpecialFunctions.Sqrt
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionDescent4D

/-!
# Explicit primitive monopole zero-mode section

The charge-one clutching line has a canonical smooth section obtained from
the first Hopf coordinate.  Its north and south representatives are
`sqrt (1 + z)` and `(x + i y) / sqrt (1 - z)`.  They obey the exact installed
clutching law and therefore can be tensored with normal-root spinor lifts.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPPrimitiveMonopoleZeroModeSection4D

set_option autoImplicit false
noncomputable section

open Set Metric Topology
open scoped Manifold ContDiff
open P0EFTJanusProgramPPrimitiveMonopoleClutchingConnection4D
open P0EFTJanusProgramPPrimitiveMonopoleSmoothClutching4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionDescent4D

local instance monopoleSphereChartedSpace :
    ChartedSpace (EuclideanSpace Real (Fin 2)) MonopoleSphere :=
  inferInstance

local instance euclideanR3Finrank :
    Fact (Module.finrank Real (EuclideanSpace Real (Fin 3)) = 2 + 1) :=
  ⟨by simp⟩

local instance complexRealFinrank :
    Fact (Module.finrank Real Complex = 1 + 1) :=
  finrank_real_complex_fact'

/-- Cartesian equation of the unit monopole sphere. -/
theorem monopoleSphereCoordinate_sq_sum (point : MonopoleSphere) :
    monopoleSphereCoordinate point 0 ^ 2 +
        monopoleSphereCoordinate point 1 ^ 2 +
      monopoleSphereCoordinate point 2 ^ 2 = 1 := by
  have hNorm :
      ‖(point.1 : EuclideanSpace Real (Fin 3))‖ = 1 := by
    simpa [mem_sphere_zero_iff_norm] using point.2
  have hNormSq := congrArg (fun value : Real => value ^ 2) hNorm
  rw [EuclideanSpace.real_norm_sq_eq] at hNormSq
  simp [Fin.sum_univ_succ] at hNormSq
  change
    monopoleSphereCoordinate point 0 ^ 2 +
        (monopoleSphereCoordinate point 1 ^ 2 +
          monopoleSphereCoordinate point 2 ^ 2) = 1 at hNormSq
  nlinarith

theorem monopoleSphereCoordinate_two_mem_Icc (point : MonopoleSphere) :
    monopoleSphereCoordinate point 2 ∈ Set.Icc (-1 : Real) 1 := by
  have hSphere := monopoleSphereCoordinate_sq_sum point
  constructor <;>
    nlinarith [sq_nonneg (monopoleSphereCoordinate point 0),
      sq_nonneg (monopoleSphereCoordinate point 1)]

theorem one_add_monopoleSphereCoordinate_two_nonnegative
    (point : MonopoleSphere) :
    0 ≤ 1 + monopoleSphereCoordinate point 2 := by
  linarith [monopoleSphereCoordinate_two_mem_Icc point |>.1]

theorem one_sub_monopoleSphereCoordinate_two_nonnegative
    (point : MonopoleSphere) :
    0 ≤ 1 - monopoleSphereCoordinate point 2 := by
  linarith [monopoleSphereCoordinate_two_mem_Icc point |>.2]

theorem one_add_monopoleSphereCoordinate_two_pos_of_mem_north
    (point : MonopoleSphere)
    (hPoint : point ∈ monopoleChartDomain .north) :
    0 < 1 + monopoleSphereCoordinate point 2 := by
  change monopoleSphereCoordinate point 2 ≠ -1 at hPoint
  have hLower := monopoleSphereCoordinate_two_mem_Icc point |>.1
  have hStrict :
      (-1 : Real) < monopoleSphereCoordinate point 2 :=
    lt_of_le_of_ne hLower hPoint.symm
  linarith

theorem one_sub_monopoleSphereCoordinate_two_pos_of_mem_south
    (point : MonopoleSphere)
    (hPoint : point ∈ monopoleChartDomain .south) :
    0 < 1 - monopoleSphereCoordinate point 2 := by
  change monopoleSphereCoordinate point 2 ≠ 1 at hPoint
  have hUpper := monopoleSphereCoordinate_two_mem_Icc point |>.2
  have hStrict :
      monopoleSphereCoordinate point 2 < 1 :=
    lt_of_le_of_ne hUpper hPoint
  linarith

/-- North representative of the primitive monopole zero mode. -/
def primitiveMonopoleZeroNorthValue (point : MonopoleSphere) : Complex :=
  Complex.ofReal
    (Real.sqrt (1 + monopoleSphereCoordinate point 2))

/-- South representative of the same primitive monopole zero mode. -/
def primitiveMonopoleZeroSouthValue (point : MonopoleSphere) : Complex :=
  (Real.sqrt (1 - monopoleSphereCoordinate point 2))⁻¹ •
    monopoleSphereXY point

/-- The two chart representatives as one local family. -/
def primitiveMonopoleZeroLocalValue :
    MonopoleChart → MonopoleSphere → Complex
  | .north => primitiveMonopoleZeroNorthValue
  | .south => primitiveMonopoleZeroSouthValue

theorem primitiveMonopoleZeroNorthValue_contMDiffOn :
    ContMDiffOn (𝓡 2) 𝓘(Real, Complex) ∞
      primitiveMonopoleZeroNorthValue
      (monopoleChartDomain .north) := by
  have hRadicand :
      ContMDiff (𝓡 2) 𝓘(Real, Real) ∞
        (fun point : MonopoleSphere =>
          1 + monopoleSphereCoordinate point 2) :=
    contMDiff_const.add (monopoleSphereCoordinate_contMDiff 2)
  have hSqrt :
      ContMDiffOn (𝓡 2) 𝓘(Real, Real) ∞
        (fun point : MonopoleSphere =>
          Real.sqrt (1 + monopoleSphereCoordinate point 2))
        (monopoleChartDomain .north) := by
    intro point hPoint
    exact
      ((Real.contDiffAt_sqrt
          (ne_of_gt
            (one_add_monopoleSphereCoordinate_two_pos_of_mem_north
              point hPoint))).contMDiffAt.comp point
        hRadicand.contMDiffAt).contMDiffWithinAt
  exact
    Complex.ofRealCLM.contDiff.contMDiff.comp_contMDiffOn hSqrt

theorem primitiveMonopoleZeroSouthValue_contMDiffOn :
    ContMDiffOn (𝓡 2) 𝓘(Real, Complex) ∞
      primitiveMonopoleZeroSouthValue
      (monopoleChartDomain .south) := by
  have hRadicand :
      ContMDiff (𝓡 2) 𝓘(Real, Real) ∞
        (fun point : MonopoleSphere =>
          1 - monopoleSphereCoordinate point 2) :=
    contMDiff_const.sub (monopoleSphereCoordinate_contMDiff 2)
  have hSqrt :
      ContMDiffOn (𝓡 2) 𝓘(Real, Real) ∞
        (fun point : MonopoleSphere =>
          Real.sqrt (1 - monopoleSphereCoordinate point 2))
        (monopoleChartDomain .south) := by
    intro point hPoint
    exact
      ((Real.contDiffAt_sqrt
          (ne_of_gt
            (one_sub_monopoleSphereCoordinate_two_pos_of_mem_south
              point hPoint))).contMDiffAt.comp point
        hRadicand.contMDiffAt).contMDiffWithinAt
  have hInverse :
      ContMDiffOn (𝓡 2) 𝓘(Real, Real) ∞
        (fun point : MonopoleSphere =>
          (Real.sqrt
            (1 - monopoleSphereCoordinate point 2))⁻¹)
        (monopoleChartDomain .south) :=
    hSqrt.inv₀
      (fun point hPoint =>
        Real.sqrt_ne_zero'.mpr
          (one_sub_monopoleSphereCoordinate_two_pos_of_mem_south
            point hPoint))
  exact
    hInverse.smul monopoleSphereXY_contMDiff.contMDiffOn

theorem monopoleSphereXY_norm
    (point : MonopoleSphere) :
    ‖monopoleSphereXY point‖ =
      Real.sqrt (1 + monopoleSphereCoordinate point 2) *
        Real.sqrt (1 - monopoleSphereCoordinate point 2) := by
  have hNormSq :
      Complex.normSq (monopoleSphereXY point) =
        (1 + monopoleSphereCoordinate point 2) *
          (1 - monopoleSphereCoordinate point 2) := by
    rw [Complex.normSq_apply]
    simp only [monopoleSphereXY, monopoleSphereCoordinate,
      Complex.mul_re, Complex.mul_im]
    have hSphere := monopoleSphereCoordinate_sq_sum point
    change
      monopoleSphereCoordinate point 0 *
            monopoleSphereCoordinate point 0 +
          monopoleSphereCoordinate point 1 *
            monopoleSphereCoordinate point 1 =
        (1 + monopoleSphereCoordinate point 2) *
          (1 - monopoleSphereCoordinate point 2)
    nlinarith
  rw [Complex.norm_def, hNormSq,
    Real.sqrt_mul
      (one_add_monopoleSphereCoordinate_two_nonnegative point)]

theorem primitiveMonopoleZero_north_south
    (point : MonopoleSphere)
    (hNorth : point ∈ monopoleChartDomain .north)
    (hSouth : point ∈ monopoleChartDomain .south) :
    (primitiveMonopoleTransition 1 .north .south point : Complex) *
        primitiveMonopoleZeroNorthValue point =
      primitiveMonopoleZeroSouthValue point := by
  have hXY :
      monopoleSphereXY point ≠ 0 :=
    monopoleSphereXY_ne_zero_of_mem_overlap point hNorth hSouth
  have hNorthSqrt :
      Real.sqrt (1 + monopoleSphereCoordinate point 2) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr
      (one_add_monopoleSphereCoordinate_two_pos_of_mem_north
        point hNorth)
  have hSouthSqrt :
      Real.sqrt (1 - monopoleSphereCoordinate point 2) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr
      (one_sub_monopoleSphereCoordinate_two_pos_of_mem_south
        point hSouth)
  have hScalar :
      ‖monopoleSphereXY point‖⁻¹ *
          Real.sqrt (1 + monopoleSphereCoordinate point 2) =
        (Real.sqrt
          (1 - monopoleSphereCoordinate point 2))⁻¹ := by
    rw [monopoleSphereXY_norm]
    field_simp
  rw [show
      primitiveMonopoleTransition 1 .north .south point =
        monopoleSphereXYPhase point by
      simp [primitiveMonopoleTransition]]
  rw [monopoleSphereXYPhase_coe_of_ne_zero point hXY]
  unfold primitiveMonopoleZeroNorthValue
    primitiveMonopoleZeroSouthValue
  calc
    (‖monopoleSphereXY point‖⁻¹ • monopoleSphereXY point) *
          Complex.ofReal
            (Real.sqrt
              (1 + monopoleSphereCoordinate point 2)) =
        Complex.ofReal
            (‖monopoleSphereXY point‖⁻¹ *
              Real.sqrt
                (1 + monopoleSphereCoordinate point 2)) *
          monopoleSphereXY point := by
      rw [Complex.real_smul, Complex.ofReal_mul]
      ring
    _ =
        Complex.ofReal
            (Real.sqrt
              (1 - monopoleSphereCoordinate point 2))⁻¹ *
          monopoleSphereXY point := by
      rw [hScalar]
    _ =
        (Real.sqrt
          (1 - monopoleSphereCoordinate point 2))⁻¹ •
            monopoleSphereXY point := by
      rw [Complex.real_smul]

theorem primitiveMonopoleZero_coordChange
    (first second : MonopoleChart)
    (point : MonopoleSphere)
    (hPoint :
      point ∈ monopoleChartDomain first ∩
        monopoleChartDomain second) :
    (primitiveMonopoleTransition 1 first second point : Complex) *
        primitiveMonopoleZeroLocalValue first point =
      primitiveMonopoleZeroLocalValue second point := by
  cases first <;> cases second
  · simp [primitiveMonopoleTransition,
      primitiveMonopoleZeroLocalValue]
  · exact primitiveMonopoleZero_north_south point hPoint.1 hPoint.2
  · have hForward :=
      primitiveMonopoleZero_north_south point hPoint.2 hPoint.1
    have hForwardPhase :
        (monopoleSphereXYPhase point : Complex) *
            primitiveMonopoleZeroNorthValue point =
          primitiveMonopoleZeroSouthValue point := by
      simpa [primitiveMonopoleTransition] using hForward
    have hPhase :
        (monopoleSphereXYPhase point : Complex) ≠ 0 :=
      Circle.coe_ne_zero _
    simp only [primitiveMonopoleTransition,
      primitiveMonopoleZeroLocalValue, zpow_one, Circle.coe_inv]
    rw [← hForwardPhase]
    rw [← mul_assoc, inv_mul_cancel₀ hPhase, one_mul]
  · simp [primitiveMonopoleTransition,
      primitiveMonopoleZeroLocalValue]

/-- Smooth charge-one local family represented by the Hopf zero mode. -/
def primitiveMonopoleZeroLocalScalarFamily :
    SmoothPrimitiveMonopoleLocalScalarFamily where
  localValue := primitiveMonopoleZeroLocalValue
  contMDiffOn_localValue chart := by
    cases chart
    · exact primitiveMonopoleZeroNorthValue_contMDiffOn
    · exact primitiveMonopoleZeroSouthValue_contMDiffOn
  coordChange_localValue :=
    primitiveMonopoleZero_coordChange

/-- Complementary Hopf coordinate in the north gauge.  Together with
`primitiveMonopoleZeroNorthValue` it forms the positive radial Clifford
eigenspinor. -/
def primitiveMonopoleZeroComplementNorthValue
  (point : MonopoleSphere) : Complex :=
  (Real.sqrt (1 + monopoleSphereCoordinate point 2))⁻¹ •
    star (monopoleSphereXY point)

/-- Complementary Hopf coordinate in the south gauge. -/
def primitiveMonopoleZeroComplementSouthValue
    (point : MonopoleSphere) : Complex :=
  Complex.ofReal
    (Real.sqrt (1 - monopoleSphereCoordinate point 2))

/-- The complementary Hopf coordinate in both monopole gauges. -/
def primitiveMonopoleZeroComplementLocalValue :
    MonopoleChart → MonopoleSphere → Complex
  | .north => primitiveMonopoleZeroComplementNorthValue
  | .south => primitiveMonopoleZeroComplementSouthValue

theorem primitiveMonopoleZeroComplementNorthValue_contMDiffOn :
    ContMDiffOn (𝓡 2) 𝓘(Real, Complex) ∞
      primitiveMonopoleZeroComplementNorthValue
      (monopoleChartDomain .north) := by
  have hRadicand :
      ContMDiff (𝓡 2) 𝓘(Real, Real) ∞
        (fun point : MonopoleSphere =>
          1 + monopoleSphereCoordinate point 2) :=
    contMDiff_const.add (monopoleSphereCoordinate_contMDiff 2)
  have hSqrt :
      ContMDiffOn (𝓡 2) 𝓘(Real, Real) ∞
        (fun point : MonopoleSphere =>
          Real.sqrt (1 + monopoleSphereCoordinate point 2))
        (monopoleChartDomain .north) := by
    intro point hPoint
    exact
      ((Real.contDiffAt_sqrt
          (ne_of_gt
            (one_add_monopoleSphereCoordinate_two_pos_of_mem_north
              point hPoint))).contMDiffAt.comp point
        hRadicand.contMDiffAt).contMDiffWithinAt
  have hInverse :
      ContMDiffOn (𝓡 2) 𝓘(Real, Real) ∞
        (fun point : MonopoleSphere =>
          (Real.sqrt
            (1 + monopoleSphereCoordinate point 2))⁻¹)
        (monopoleChartDomain .north) :=
    hSqrt.inv₀
      (fun point hPoint =>
        Real.sqrt_ne_zero'.mpr
          (one_add_monopoleSphereCoordinate_two_pos_of_mem_north
            point hPoint))
  have hConj :
      ContMDiff (𝓡 2) 𝓘(Real, Complex) ∞
        (fun point : MonopoleSphere =>
          star (monopoleSphereXY point)) := by
    simpa only [Function.comp_def, Complex.conjCLE_apply,
      ← Complex.star_def] using
      Complex.conjCLE.contDiff.contMDiff.comp
        monopoleSphereXY_contMDiff
  exact hInverse.smul hConj.contMDiffOn

theorem primitiveMonopoleZeroComplementSouthValue_contMDiffOn :
    ContMDiffOn (𝓡 2) 𝓘(Real, Complex) ∞
      primitiveMonopoleZeroComplementSouthValue
      (monopoleChartDomain .south) := by
  have hRadicand :
      ContMDiff (𝓡 2) 𝓘(Real, Real) ∞
        (fun point : MonopoleSphere =>
          1 - monopoleSphereCoordinate point 2) :=
    contMDiff_const.sub (monopoleSphereCoordinate_contMDiff 2)
  have hSqrt :
      ContMDiffOn (𝓡 2) 𝓘(Real, Real) ∞
        (fun point : MonopoleSphere =>
          Real.sqrt (1 - monopoleSphereCoordinate point 2))
        (monopoleChartDomain .south) := by
    intro point hPoint
    exact
      ((Real.contDiffAt_sqrt
          (ne_of_gt
            (one_sub_monopoleSphereCoordinate_two_pos_of_mem_south
              point hPoint))).contMDiffAt.comp point
        hRadicand.contMDiffAt).contMDiffWithinAt
  exact
    Complex.ofRealCLM.contDiff.contMDiff.comp_contMDiffOn hSqrt

theorem primitiveMonopoleZeroComplement_north_south
    (point : MonopoleSphere)
    (hNorth : point ∈ monopoleChartDomain .north)
    (hSouth : point ∈ monopoleChartDomain .south) :
    (primitiveMonopoleTransition 1 .north .south point : Complex) *
        primitiveMonopoleZeroComplementNorthValue point =
      primitiveMonopoleZeroComplementSouthValue point := by
  have hXY :
      monopoleSphereXY point ≠ 0 :=
    monopoleSphereXY_ne_zero_of_mem_overlap point hNorth hSouth
  have hNorthSqrt :
      Real.sqrt (1 + monopoleSphereCoordinate point 2) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr
      (one_add_monopoleSphereCoordinate_two_pos_of_mem_north
        point hNorth)
  have hNorm :
      ‖monopoleSphereXY point‖ =
        Real.sqrt (1 + monopoleSphereCoordinate point 2) *
          Real.sqrt (1 - monopoleSphereCoordinate point 2) :=
    monopoleSphereXY_norm point
  rw [show
      primitiveMonopoleTransition 1 .north .south point =
        monopoleSphereXYPhase point by
      simp [primitiveMonopoleTransition]]
  rw [monopoleSphereXYPhase_coe_of_ne_zero point hXY]
  unfold primitiveMonopoleZeroComplementNorthValue
    primitiveMonopoleZeroComplementSouthValue
  rw [Complex.real_smul]
  have hNormNe : ‖monopoleSphereXY point‖ ≠ 0 := norm_ne_zero_iff.mpr hXY
  have hMulStar :
      monopoleSphereXY point * star (monopoleSphereXY point) =
        Complex.normSq (monopoleSphereXY point) := by
    simpa only [← Complex.star_def] using
      Complex.mul_conj (monopoleSphereXY point)
  rw [Complex.real_smul]
  calc
    (↑‖monopoleSphereXY point‖⁻¹ *
          monopoleSphereXY point) *
        (↑(Real.sqrt
            (1 + monopoleSphereCoordinate point 2))⁻¹ *
          star (monopoleSphereXY point)) =
        (↑(‖monopoleSphereXY point‖⁻¹ *
            (Real.sqrt
              (1 + monopoleSphereCoordinate point 2))⁻¹) : Complex) *
          (monopoleSphereXY point *
            star (monopoleSphereXY point)) := by
      push_cast
      ring
    _ =
        (↑(‖monopoleSphereXY point‖⁻¹ *
            (Real.sqrt
              (1 + monopoleSphereCoordinate point 2))⁻¹ *
            Complex.normSq (monopoleSphereXY point)) : Complex) := by
      rw [hMulStar]
      push_cast
      ring
    _ =
        Complex.ofReal
          (Real.sqrt
            (1 - monopoleSphereCoordinate point 2)) := by
      rw [Complex.normSq_eq_norm_sq, hNorm]
      congr 1
      field_simp

theorem primitiveMonopoleZeroComplement_coordChange
    (first second : MonopoleChart)
    (point : MonopoleSphere)
    (hPoint :
      point ∈ monopoleChartDomain first ∩
        monopoleChartDomain second) :
    (primitiveMonopoleTransition 1 first second point : Complex) *
        primitiveMonopoleZeroComplementLocalValue first point =
      primitiveMonopoleZeroComplementLocalValue second point := by
  cases first <;> cases second
  · simp [primitiveMonopoleTransition,
      primitiveMonopoleZeroComplementLocalValue]
  · exact primitiveMonopoleZeroComplement_north_south
      point hPoint.1 hPoint.2
  · have hForward :=
      primitiveMonopoleZeroComplement_north_south
        point hPoint.2 hPoint.1
    have hPhase :
        (monopoleSphereXYPhase point : Complex) ≠ 0 :=
      Circle.coe_ne_zero _
    simp only [primitiveMonopoleTransition,
      primitiveMonopoleZeroComplementLocalValue, zpow_one,
      Circle.coe_inv] at hForward ⊢
    rw [← hForward, ← mul_assoc, inv_mul_cancel₀ hPhase, one_mul]
  · simp [primitiveMonopoleTransition,
      primitiveMonopoleZeroComplementLocalValue]

/-- Smooth complementary charge-one Hopf coordinate. -/
def primitiveMonopoleZeroComplementLocalScalarFamily :
    SmoothPrimitiveMonopoleLocalScalarFamily where
  localValue := primitiveMonopoleZeroComplementLocalValue
  contMDiffOn_localValue chart := by
    cases chart
    · exact primitiveMonopoleZeroComplementNorthValue_contMDiffOn
    · exact primitiveMonopoleZeroComplementSouthValue_contMDiffOn
  coordChange_localValue :=
    primitiveMonopoleZeroComplement_coordChange

theorem monopoleSphereXY_mul_star
    (point : MonopoleSphere) :
    monopoleSphereXY point * star (monopoleSphereXY point) =
      Complex.ofReal
        ((1 - monopoleSphereCoordinate point 2) *
          (1 + monopoleSphereCoordinate point 2)) := by
  apply Complex.ext
  · simp [monopoleSphereXY]
    nlinarith [monopoleSphereCoordinate_sq_sum point]
  · simp [monopoleSphereXY]
    ring

private theorem sqrt_eq_mul_inv_sqrt
    {value : Real} (hValue : 0 < value) :
    Real.sqrt value = value * (Real.sqrt value)⁻¹ := by
  have hSqrt : Real.sqrt value ≠ 0 :=
    Real.sqrt_ne_zero'.mpr hValue
  field_simp
  nlinarith [Real.sq_sqrt (le_of_lt hValue)]

theorem primitiveMonopoleHopfNorth_star_mul_first
    (point : MonopoleSphere)
    (hPoint : point ∈ monopoleChartDomain .north) :
    star (monopoleSphereXY point) *
        primitiveMonopoleZeroNorthValue point =
      Complex.ofReal (1 + monopoleSphereCoordinate point 2) *
        primitiveMonopoleZeroComplementNorthValue point := by
  have hFactor :=
    sqrt_eq_mul_inv_sqrt
      (one_add_monopoleSphereCoordinate_two_pos_of_mem_north
        point hPoint)
  have hComplexFactor :
      Complex.ofReal
          (Real.sqrt (1 + monopoleSphereCoordinate point 2)) =
        Complex.ofReal (1 + monopoleSphereCoordinate point 2) *
          (Complex.ofReal
            (Real.sqrt (1 + monopoleSphereCoordinate point 2)))⁻¹ := by
    simpa using congrArg Complex.ofReal hFactor
  unfold primitiveMonopoleZeroNorthValue
    primitiveMonopoleZeroComplementNorthValue
  rw [Complex.real_smul]
  push_cast
  calc
    star (monopoleSphereXY point) *
        Complex.ofReal
          (Real.sqrt (1 + monopoleSphereCoordinate point 2)) =
      star (monopoleSphereXY point) *
        (Complex.ofReal (1 + monopoleSphereCoordinate point 2) *
          (Complex.ofReal
            (Real.sqrt (1 + monopoleSphereCoordinate point 2)))⁻¹) :=
      congrArg (fun scalar => star (monopoleSphereXY point) * scalar)
        hComplexFactor
    _ = _ := by
      push_cast
      ring

theorem primitiveMonopoleHopfNorth_xy_mul_complement
    (point : MonopoleSphere)
    (hPoint : point ∈ monopoleChartDomain .north) :
    monopoleSphereXY point *
        primitiveMonopoleZeroComplementNorthValue point =
      Complex.ofReal (1 - monopoleSphereCoordinate point 2) *
        primitiveMonopoleZeroNorthValue point := by
  have hFactor :=
    sqrt_eq_mul_inv_sqrt
      (one_add_monopoleSphereCoordinate_two_pos_of_mem_north
        point hPoint)
  have hComplexFactor :
      Complex.ofReal
          (Real.sqrt (1 + monopoleSphereCoordinate point 2)) =
        Complex.ofReal (1 + monopoleSphereCoordinate point 2) *
          (Complex.ofReal
            (Real.sqrt (1 + monopoleSphereCoordinate point 2)))⁻¹ := by
    simpa using congrArg Complex.ofReal hFactor
  unfold primitiveMonopoleZeroNorthValue
    primitiveMonopoleZeroComplementNorthValue
  rw [Complex.real_smul]
  push_cast
  calc
    monopoleSphereXY point *
        ((Complex.ofReal
          (Real.sqrt (1 + monopoleSphereCoordinate point 2)))⁻¹ *
            star (monopoleSphereXY point)) =
      (Complex.ofReal
        (Real.sqrt (1 + monopoleSphereCoordinate point 2)))⁻¹ *
          (monopoleSphereXY point * star (monopoleSphereXY point)) := by
      ring
    _ = (Complex.ofReal
          (Real.sqrt (1 + monopoleSphereCoordinate point 2)))⁻¹ *
        Complex.ofReal
          ((1 - monopoleSphereCoordinate point 2) *
            (1 + monopoleSphereCoordinate point 2)) := by
      rw [monopoleSphereXY_mul_star]
    _ = Complex.ofReal (1 - monopoleSphereCoordinate point 2) *
        (Complex.ofReal (1 + monopoleSphereCoordinate point 2) *
          (Complex.ofReal
            (Real.sqrt (1 + monopoleSphereCoordinate point 2)))⁻¹) := by
      push_cast
      ring
    _ = _ := by
      simpa using
        congrArg
          (fun scalar =>
            Complex.ofReal (1 - monopoleSphereCoordinate point 2) * scalar)
          hComplexFactor.symm

theorem primitiveMonopoleHopfSouth_xy_mul_second
    (point : MonopoleSphere)
    (hPoint : point ∈ monopoleChartDomain .south) :
    monopoleSphereXY point *
        primitiveMonopoleZeroComplementSouthValue point =
      Complex.ofReal (1 - monopoleSphereCoordinate point 2) *
        primitiveMonopoleZeroSouthValue point := by
  have hFactor :=
    sqrt_eq_mul_inv_sqrt
      (one_sub_monopoleSphereCoordinate_two_pos_of_mem_south
        point hPoint)
  have hComplexFactor :
      Complex.ofReal
          (Real.sqrt (1 - monopoleSphereCoordinate point 2)) =
        Complex.ofReal (1 - monopoleSphereCoordinate point 2) *
          (Complex.ofReal
            (Real.sqrt (1 - monopoleSphereCoordinate point 2)))⁻¹ := by
    simpa using congrArg Complex.ofReal hFactor
  unfold primitiveMonopoleZeroSouthValue
    primitiveMonopoleZeroComplementSouthValue
  rw [Complex.real_smul]
  push_cast
  calc
    monopoleSphereXY point *
        Complex.ofReal
          (Real.sqrt (1 - monopoleSphereCoordinate point 2)) =
      monopoleSphereXY point *
        (Complex.ofReal (1 - monopoleSphereCoordinate point 2) *
          (Complex.ofReal
            (Real.sqrt (1 - monopoleSphereCoordinate point 2)))⁻¹) :=
      congrArg (fun scalar => monopoleSphereXY point * scalar)
        hComplexFactor
    _ = _ := by
      push_cast
      ring

theorem primitiveMonopoleHopfSouth_star_mul_first
    (point : MonopoleSphere)
    (hPoint : point ∈ monopoleChartDomain .south) :
    star (monopoleSphereXY point) *
        primitiveMonopoleZeroSouthValue point =
      Complex.ofReal (1 + monopoleSphereCoordinate point 2) *
        primitiveMonopoleZeroComplementSouthValue point := by
  have hFactor :=
    sqrt_eq_mul_inv_sqrt
      (one_sub_monopoleSphereCoordinate_two_pos_of_mem_south
        point hPoint)
  have hComplexFactor :
      Complex.ofReal
          (Real.sqrt (1 - monopoleSphereCoordinate point 2)) =
        Complex.ofReal (1 - monopoleSphereCoordinate point 2) *
          (Complex.ofReal
            (Real.sqrt (1 - monopoleSphereCoordinate point 2)))⁻¹ := by
    simpa using congrArg Complex.ofReal hFactor
  unfold primitiveMonopoleZeroSouthValue
    primitiveMonopoleZeroComplementSouthValue
  rw [Complex.real_smul]
  push_cast
  calc
    star (monopoleSphereXY point) *
        ((Complex.ofReal
          (Real.sqrt (1 - monopoleSphereCoordinate point 2)))⁻¹ *
            monopoleSphereXY point) =
      (Complex.ofReal
        (Real.sqrt (1 - monopoleSphereCoordinate point 2)))⁻¹ *
          (monopoleSphereXY point * star (monopoleSphereXY point)) := by
      ring
    _ = (Complex.ofReal
          (Real.sqrt (1 - monopoleSphereCoordinate point 2)))⁻¹ *
        Complex.ofReal
          ((1 - monopoleSphereCoordinate point 2) *
            (1 + monopoleSphereCoordinate point 2)) := by
      rw [monopoleSphereXY_mul_star]
    _ = Complex.ofReal (1 + monopoleSphereCoordinate point 2) *
        (Complex.ofReal (1 - monopoleSphereCoordinate point 2) *
          (Complex.ofReal
            (Real.sqrt (1 - monopoleSphereCoordinate point 2)))⁻¹) := by
      push_cast
      ring
    _ = _ := by
      simpa using
        congrArg
          (fun scalar =>
            Complex.ofReal (1 + monopoleSphereCoordinate point 2) * scalar)
          hComplexFactor.symm

end
end P0EFTJanusProgramPPrimitiveMonopoleZeroModeSection4D
end JanusFormal
