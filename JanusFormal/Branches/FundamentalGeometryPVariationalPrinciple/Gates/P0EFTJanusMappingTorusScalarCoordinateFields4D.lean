import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusShiftedSobolevMappingTorusFiniteTemporalFourierBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhasedNormalRotationFlow4D

/-! Seven genuine smooth coordinates, including the half-frequency reflection twist. -/
namespace JanusFormal.P0EFTJanusMappingTorusScalarCoordinateFields4D
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 600000
noncomputable section
open scoped Manifold ContDiff
open P0EFTJanusReflectionFixedThroat
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothDeckInvariantFields4D
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusShiftedSobolevMappingTorusFiniteTemporalFourierBridge4D
open P0EFTJanusMappingTorusCanonicalPhasedNormalRotationFlow4D

variable (period : Real) [hPos : Fact (0 < period)]
private abbrev Cover := MappingTorusCover (reflectedSphereData period hPos.out.ne')
private abbrev Base := MappingTorus (reflectedSphereData period hPos.out.ne')
local instance : ChartedSpace CoverModel (Cover period) :=
  reflectedSphereCoverChartedSpace period hPos.out.ne'
local instance : IsManifold coverModelWithCorners ω (Cover period) :=
  reflectedSphereCover_isManifold period hPos.out.ne'
local instance : ChartedSpace CoverModel (Base period) :=
  reflectedSphereQuotientChartedSpace period hPos.out.ne'
local instance : IsManifold coverModelWithCorners ω (Base period) :=
  reflectedSphereQuotient_isManifold period hPos.out.ne'

private theorem reflection_zpow_coordinates (n : Int) (point : UnitThreeSphere) (i : Fin 4) :
    ((sphereReflection ^ n) point).val i =
      if i = 0 then (-1 : Real) ^ n * point.val i else point.val i := by
  have hSquare : sphereReflection ^ (2 : Int) = 1 := by
    rw [zpow_two]
    apply Homeomorph.ext
    intro x
    apply Subtype.ext
    exact reflect_point_involutive x.val
  have hParity : (sphereReflection ^ n) point =
      if Even n then point else sphereReflection point := by
    rcases Int.even_or_odd' n with ⟨k, rfl | rfl⟩
    · rw [zpow_mul, hSquare, one_zpow]
      simp
    · rw [zpow_add_one, zpow_mul, hSquare, one_zpow, one_mul]
      simp
  rw [hParity, neg_one_zpow_eq_ite]
  by_cases hn : Even n <;> by_cases hi : i = 0 <;>
    simp [hn, hi, sphereReflection, reflectPoint]

private theorem coverCoordinate_smooth (i : Fin 4) :
    ContMDiff coverModelWithCorners 𝓘(Real, Real) ∞ (fun point : Cover period => point.fiber.val i) := by
  letI : Fact (Module.finrank Real EuclideanR4 = 3 + 1) := ⟨by simp⟩
  have hCover := chartedSpacePullback_toFun_contMDiff coverModelWithCorners ∞
    (coverHomeomorphProd (reflectedSphereData period hPos.out.ne'))
  have hSphere := chartedSpacePullback_toFun_contMDiff (𝓡 3) ∞ unitThreeSphereHomeomorph
  have hAmbient := (EuclideanSpace.equiv (Fin 4) Real).contDiff.contMDiff.comp
    (contMDiff_coe_sphere.comp (hSphere.comp (contMDiff_fst.comp hCover)))
  exact (ContinuousLinearMap.proj i).contMDiff.comp hAmbient

def spatialCoordinateCover (axis : Fin 3) : SmoothDeckInvariantField period hPos.out.ne' Real where
  toFun point := point.fiber.val axis.succ
  contMDiff_toFun := coverCoordinate_smooth period axis.succ
  deck_invariant n point := by
    change ((sphereReflection ^ n) point.fiber).val axis.succ = _
    rw [reflection_zpow_coordinates, if_neg (Fin.succ_ne_zero axis)]

def twistedCoordinateCover (phase : Fin 2) : SmoothDeckInvariantField period hPos.out.ne' Real where
  toFun point := point.fiber.val 0 * canonicalNormalRotationPhase period phase point.time
  contMDiff_toFun := by
    have hCover := chartedSpacePullback_toFun_contMDiff coverModelWithCorners ∞
      (coverHomeomorphProd (reflectedSphereData period hPos.out.ne'))
    exact (coverCoordinate_smooth period 0).mul
      ((canonicalNormalRotationPhase_contDiff period phase).contMDiff.comp (contMDiff_snd.comp hCover))
  deck_invariant n point := by
    change ((sphereReflection ^ n) point.fiber).val 0 *
      canonicalNormalRotationPhase period phase (point.time + (n : Real) * period) = _
    rw [reflection_zpow_coordinates, if_pos rfl,
      canonicalNormalRotationPhase_add_winding period hPos.out.ne', neg_one_zpow_eq_ite]
    by_cases hn : Even n <;> simp [hn]

/-- Three ordinary spatial coordinates, two twisted normal coordinates, and two time coordinates. -/
abbrev ScalarCoordinateIndex := Fin 3 ⊕ Fin 2 ⊕ Fin 2

def scalarCoordinate (index : ScalarCoordinateIndex) : SmoothQuotientField period hPos.out.ne' Real :=
  match index with
  | .inl axis => descendSmooth period hPos.out.ne' Real (spatialCoordinateCover period axis)
  | .inr (.inl phase) => descendSmooth period hPos.out.ne' Real (twistedCoordinateCover period phase)
  | .inr (.inr phase) =>
    let projection : Complex →L[Real] Real := if phase = 0 then Complex.reCLM else Complex.imCLM
    { toFun := fun point => projection (temporalComplexFourierQuotientField period 1 point)
      contMDiff_toFun := projection.contMDiff.comp (temporalComplexFourierQuotientField period 1).contMDiff_toFun }

@[simp] theorem scalarCoordinate_spatial_mk (axis : Fin 3) (point : Cover period) :
    scalarCoordinate period (.inl axis) (mappingTorusMk _ point) = point.fiber.val axis.succ := rfl

@[simp] theorem scalarCoordinate_twisted_mk (phase : Fin 2) (point : Cover period) :
    scalarCoordinate period (.inr (.inl phase)) (mappingTorusMk _ point) =
      point.fiber.val 0 * canonicalNormalRotationPhase period phase point.time := rfl

@[simp] theorem scalarCoordinate_time_re_mk (point : Cover period) :
    scalarCoordinate period (.inr (.inr 0)) (mappingTorusMk _ point) =
      (fourier 1 (point.time : AddCircle period)).re := by
  change (temporalComplexFourierQuotientField period 1 (mappingTorusMk _ point)).re = _
  rw [temporalComplexFourierQuotientField_mk]

@[simp] theorem scalarCoordinate_time_im_mk (point : Cover period) :
    scalarCoordinate period (.inr (.inr 1)) (mappingTorusMk _ point) =
      (fourier 1 (point.time : AddCircle period)).im := by
  change (temporalComplexFourierQuotientField period 1 (mappingTorusMk _ point)).im = _
  rw [temporalComplexFourierQuotientField_mk]

end
end JanusFormal.P0EFTJanusMappingTorusScalarCoordinateFields4D
