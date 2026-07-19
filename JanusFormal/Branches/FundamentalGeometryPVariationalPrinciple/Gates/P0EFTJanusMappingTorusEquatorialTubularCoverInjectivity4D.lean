import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D

namespace JanusFormal
namespace P0EFTJanusMappingTorusEquatorialTubularCoverInjectivity4D
set_option autoImplicit false
noncomputable section
open scoped ContDiff
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusReflectionFixedThroat
open P0EFTJanusMappingTorusSmoothAtlasFrontier

def EquatorialTubularParameter :=
  EquatorialTwoSphere × Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)

def equatorialTubularMap (parameter : EquatorialTubularParameter) : UnitThreeSphere :=
  equatorialLatitude parameter.1 parameter.2.1

theorem equatorialTubularMap_normal_inverse
    (parameter : EquatorialTubularParameter) :
    Real.arcsin ((equatorialTubularMap parameter).1 0) = parameter.2.1 := by
  change Real.arcsin (Real.sin parameter.2.1) = parameter.2.1
  exact Real.arcsin_sin parameter.2.2.1.le parameter.2.2.2.le

theorem equatorialTubularMap_injective : Function.Injective equatorialTubularMap := by
  rintro ⟨first, firstNormal, hFirstNormal⟩
    ⟨second, secondNormal, hSecondNormal⟩ hEqual
  have hNormal : firstNormal = secondNormal := by
    have hCoordinate := congrArg (fun point : UnitThreeSphere => point.1 0) hEqual
    have hArcsin := congrArg Real.arcsin hCoordinate
    simpa [equatorialTubularMap, equatorialLatitude,
      Real.arcsin_sin hFirstNormal.1.le hFirstNormal.2.le,
      Real.arcsin_sin hSecondNormal.1.le hSecondNormal.2.le] using hArcsin
  subst secondNormal
  have hCos : Real.cos firstNormal ≠ 0 :=
    (Real.cos_pos_of_mem_Ioo ⟨hFirstNormal.1, hFirstNormal.2⟩).ne'
  have hBase : first = second := by
    apply Subtype.ext
    funext index
    refine Fin.cases ?_ (fun tail => ?_) index
    · exact first.2.2.trans second.2.2.symm
    · have hCoordinate := congrArg
        (fun point : UnitThreeSphere => point.1 (Fin.succ tail)) hEqual
      change Real.cos firstNormal * first.1 (Fin.succ tail) =
        Real.cos firstNormal * second.1 (Fin.succ tail) at hCoordinate
      exact (mul_left_cancel₀ hCos hCoordinate)
  subst second
  rfl

theorem equatorialTubularMap_deck_reflection
    (point : EquatorialTwoSphere)
    (normal : Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) :
    sphereReflection (equatorialTubularMap (point, normal)) =
      equatorialLatitude point (-normal.1) :=
  sphereReflection_equatorialLatitude point normal.1

/-- Explicit normal coordinate on the spherical band. -/
def equatorialTubularNormalInverse (point : UnitThreeSphere) : Real :=
  Real.arcsin (point.1 0)

/-- Explicit tangential inverse before repackaging it as an equatorial
two-sphere point. -/
def equatorialTubularTailInverse (point : UnitThreeSphere) : EuclideanR3 :=
  (EuclideanSpace.equiv (Fin 3) Real).symm
    (fun index => point.1 index.succ /
      Real.cos (equatorialTubularNormalInverse point))

theorem equatorialTubularNormalInverse_map
    (parameter : EquatorialTubularParameter) :
    equatorialTubularNormalInverse (equatorialTubularMap parameter) =
      parameter.2.1 :=
  equatorialTubularMap_normal_inverse parameter

theorem equatorialTubularTailInverse_map
    (parameter : EquatorialTubularParameter) :
    equatorialTubularTailInverse (equatorialTubularMap parameter) =
      (EuclideanSpace.equiv (Fin 3) Real).symm
        (fun index => parameter.1.1 index.succ) := by
  apply (EuclideanSpace.equiv (Fin 3) Real).injective
  funext index
  change (Real.cos parameter.2.1 * parameter.1.1 index.succ) /
      Real.cos (Real.arcsin (Real.sin parameter.2.1)) =
    parameter.1.1 index.succ
  rw [Real.arcsin_sin parameter.2.2.1.le parameter.2.2.2.le]
  exact mul_div_cancel_left₀ _
    (Real.cos_pos_of_mem_Ioo parameter.2.2).ne'

/-- Coordinate reconstruction from the explicit inverse data. -/
def equatorialTubularReconstructCoordinates (point : UnitThreeSphere) : Fin 4 → Real :=
  Fin.cases (Real.sin (equatorialTubularNormalInverse point))
    (fun index =>
      Real.cos (equatorialTubularNormalInverse point) *
        (EuclideanSpace.equiv (Fin 3) Real
          (equatorialTubularTailInverse point)) index)

theorem equatorialTubularReconstructCoordinates_map
    (parameter : EquatorialTubularParameter) :
    equatorialTubularReconstructCoordinates (equatorialTubularMap parameter) =
      (equatorialTubularMap parameter).1 := by
  funext index
  refine Fin.cases ?_ (fun tail => ?_) index
  · change Real.sin (Real.arcsin (Real.sin parameter.2.1)) = Real.sin parameter.2.1
    rw [Real.arcsin_sin parameter.2.2.1.le parameter.2.2.2.le]
  · rw [equatorialTubularReconstructCoordinates,
      equatorialTubularNormalInverse_map, equatorialTubularTailInverse_map]
    rfl

theorem equatorialTubularNormalInverse_reflection (point : UnitThreeSphere) :
    equatorialTubularNormalInverse (sphereReflection point) =
      -equatorialTubularNormalInverse point := by
  simp [equatorialTubularNormalInverse, sphereReflection, reflectPoint,
    Real.arcsin_neg]

def RawSphericalTubularBand : Set (Fin 4 → Real) :=
  {point | |point 0| < 1}

def rawEquatorialTubularNormalInverse (point : Fin 4 → Real) : Real :=
  Real.arcsin (point 0)

theorem rawEquatorialTubularNormalInverse_contDiffOn :
    ContDiffOn Real ∞ rawEquatorialTubularNormalInverse RawSphericalTubularBand := by
  intro point hPoint
  change |point 0| < 1 at hPoint
  have hLower : point 0 ≠ -1 := by
    have := (abs_lt.mp hPoint).1
    exact ne_of_gt this
  have hUpper : point 0 ≠ 1 := by
    have := (abs_lt.mp hPoint).2
    exact ne_of_lt this
  exact ((Real.contDiffAt_arcsin hLower hUpper).comp point
    (contDiffAt_apply (𝕜 := Real) (E := Real) (n := ∞) 0 point)).contDiffWithinAt

theorem rawEquatorialTubularNormalInverse_continuousOn :
    ContinuousOn rawEquatorialTubularNormalInverse RawSphericalTubularBand :=
  (rawEquatorialTubularNormalInverse_contDiffOn).continuousOn

theorem equatorialTubularNormalInverse_continuous :
    Continuous equatorialTubularNormalInverse := by
  unfold equatorialTubularNormalInverse
  exact Real.continuous_arcsin.comp
    ((continuous_apply 0).comp continuous_subtype_val)

end
end P0EFTJanusMappingTorusEquatorialTubularCoverInjectivity4D
end JanusFormal
