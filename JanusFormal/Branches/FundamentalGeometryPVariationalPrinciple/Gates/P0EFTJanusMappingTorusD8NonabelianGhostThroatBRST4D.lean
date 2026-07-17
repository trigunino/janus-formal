import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusD8NonabelianGhostLinearFullFieldBRST4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusDifferentialLLWeakEquation4D

/-!
# The fixed-throat `so(3)` ghosts and the LL BRST completion

All three spatial rotations preserve the fixed equator.  Their flows restrict
to the equatorial mapping-torus cover, commute with its identity deck action,
and descend to the actual compact throat quotient.  Polar coordinates prove
the exact `so(3)` bracket table.  The induced scalar Lie derivatives then give
the square-zero BRST differential used by all three LL blocks.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusD8NonabelianGhostThroatBRST4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 800000

noncomputable section

open Set Topology TopologicalSpace
open scoped Manifold ContDiff TensorProduct BigOperators
open Bundle
open P0EFTJanusReflectionFixedThroat
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusExteriorDiffeomorphismGhostBRST4D
open P0EFTJanusMappingTorusThreeGeneratorGlobalKoszulBRST4D
open P0EFTJanusMappingTorusD8NonabelianGhostTriple4D
open P0EFTJanusMappingTorusD8NonabelianGhostKoszul4D
open P0EFTJanusMappingTorusD8NonabelianGhostLinearFullFieldBRST4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev throatData := fixedEquatorData period hPeriod
private abbrev EffectiveThroatCover :=
  MappingTorusCover (throatData period hPeriod)
private abbrev EffectiveThroat := MappingTorus (throatData period hPeriod)
private abbrev EuclideanR3 := EuclideanSpace Real (Fin 3)
private abbrev Coefficient := GhostCoefficientExterior
private abbrev ThroatScalar := CInfinityThroatScalarField period hPeriod
private abbrev ThroatTotal := LLThroatExteriorScalarAlgebra period hPeriod

local instance effectiveThroatCoverChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroatCover period hPeriod) :=
  fixedThroatCoverChartedSpace period hPeriod

local instance effectiveThroatCoverIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroatCover period hPeriod) :=
  fixedThroatCover_isManifold period hPeriod

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

private abbrev ThroatCoverTangent
    (point : EffectiveThroatCover period hPeriod) :=
  TangentSpace throatCoverModelWithCorners point

/-- Genuine smooth tangent ghosts on the compact fixed throat. -/
abbrev CInfinityThroatGhost :=
  ContMDiffSection throatCoverModelWithCorners ThroatCoverCoordinates ∞
    (fun point : EffectiveThroat period hPeriod =>
      TangentSpace throatCoverModelWithCorners point)

private abbrev CInfinityThroatCoverGhost :=
  ContMDiffSection throatCoverModelWithCorners ThroatCoverCoordinates ∞
    (fun point : EffectiveThroatCover period hPeriod =>
      ThroatCoverTangent period hPeriod point)

/-- Every ambient spatial rotation preserves the defining equator `x₀ = 0`.
Thus the maximal preserving rotation algebra is the full three-dimensional
`so(3)` triple; no axis is lost. -/
theorem ambientSpatialRotationFlow_preserves_equator
    (axis : Fin 3) (input : Real × R4Point)
    (hEquator : OnEquatorialTwoSphere input.2) :
    OnEquatorialTwoSphere (ambientSpatialRotationFlow axis input) := by
  constructor
  · simpa [OnUnitThreeSphere] using
      (ambientSpatialRotationFlow_preserves_radius axis input).trans hEquator.1
  · fin_cases axis <;>
      simp [ambientSpatialRotationFlow, hEquator.2]

private abbrev ThroatCoordinatePoint := Fin 3 → Real

private def throatRotationOneLinear :
    ThroatCoordinatePoint →ₗ[Real] ThroatCoordinatePoint where
  toFun point := ![0, -point 2, point 1]
  map_add' first second := by
    funext index
    fin_cases index <;> simp <;> abel
  map_smul' scalar point := by
    funext index
    fin_cases index <;> simp

private def throatRotationTwoLinear :
    ThroatCoordinatePoint →ₗ[Real] ThroatCoordinatePoint where
  toFun point := ![point 2, 0, -point 0]
  map_add' first second := by
    funext index
    fin_cases index <;> simp <;> abel
  map_smul' scalar point := by
    funext index
    fin_cases index <;> simp

private def throatRotationThreeLinear :
    ThroatCoordinatePoint →ₗ[Real] ThroatCoordinatePoint where
  toFun point := ![-point 1, point 0, 0]
  map_add' first second := by
    funext index
    fin_cases index <;> simp <;> abel
  map_smul' scalar point := by
    funext index
    fin_cases index <;> simp

private def throatCoordinateRotation (axis : Fin 3) :
    ThroatCoordinatePoint →L[Real] ThroatCoordinatePoint :=
  (![throatRotationOneLinear, throatRotationTwoLinear,
      throatRotationThreeLinear] axis).toContinuousLinearMap

private theorem throatCoordinateRotation_lieBracket
    (first second : Fin 3) :
    VectorField.lieBracket Real
        (throatCoordinateRotation first)
        (throatCoordinateRotation second) =
      fun point => ∑ output : Fin 3,
        spatialRotationStructureConstant first second output •
          throatCoordinateRotation output point := by
  funext point
  simp only [VectorField.lieBracket, ContinuousLinearMap.fderiv]
  fin_cases first <;> fin_cases second <;>
    funext index <;> fin_cases index <;>
    simp [throatCoordinateRotation,
      throatRotationOneLinear, throatRotationTwoLinear,
      throatRotationThreeLinear, spatialRotationStructureConstant,
      Fin.sum_univ_succ]

/-- The infinitesimal rotations in the three Euclidean equator coordinates. -/
def euclideanThroatRotation (axis : Fin 3) :
    EuclideanR3 →L[Real] EuclideanR3 :=
  (EuclideanSpace.equiv (Fin 3) Real).symm.toContinuousLinearMap.comp
    ((throatCoordinateRotation axis).comp
      (EuclideanSpace.equiv (Fin 3) Real).toContinuousLinearMap)

@[simp]
private theorem euclideanThroatRotation_conjugates
    (axis : Fin 3) (point : EuclideanR3) :
    (EuclideanSpace.equiv (Fin 3) Real)
        (euclideanThroatRotation axis point) =
      throatCoordinateRotation axis
        ((EuclideanSpace.equiv (Fin 3) Real) point) := by
  change WithLp.ofLp (WithLp.toLp 2
      (throatCoordinateRotation axis
        ((EuclideanSpace.equiv (Fin 3) Real) point))) = _
  rfl

private def euclideanThroatRotationSection (axis : Fin 3) :
    ContMDiffSection 𝓘(Real, EuclideanR3) EuclideanR3 ∞
      (fun point : EuclideanR3 =>
        TangentSpace 𝓘(Real, EuclideanR3) point) where
  toFun := euclideanThroatRotation axis
  contMDiff_toFun := by
    rw [contMDiff_vectorSpace_iff_contDiff]
    exact (euclideanThroatRotation axis).contDiff

private theorem euclideanThroatRotation_lieBracket
    (first second : Fin 3) :
    VectorField.mlieBracket 𝓘(Real, EuclideanR3)
        (euclideanThroatRotationSection first)
        (euclideanThroatRotationSection second) =
      fun point => ∑ output : Fin 3,
        spatialRotationStructureConstant first second output •
          euclideanThroatRotationSection output point := by
  rw [← VectorField.mlieBracketWithin_univ,
    VectorField.mlieBracketWithin_eq_lieBracketWithin,
    VectorField.lieBracketWithin_univ]
  funext point
  change VectorField.lieBracket Real
      (euclideanThroatRotation first) (euclideanThroatRotation second) point =
    ∑ output : Fin 3,
      spatialRotationStructureConstant first second output •
        euclideanThroatRotation output point
  apply (EuclideanSpace.equiv (Fin 3) Real).injective
  have hCoordinate := congrFun
    (throatCoordinateRotation_lieBracket first second)
    ((EuclideanSpace.equiv (Fin 3) Real) point)
  simpa only [euclideanThroatRotationSection, VectorField.lieBracket,
    ContinuousLinearMap.fderiv, map_sub,
    euclideanThroatRotation_conjugates, map_sum, map_smul] using hCoordinate

private def throatCoordinateRotationFlow
    (axis : Fin 3) (input : Real × ThroatCoordinatePoint) :
    ThroatCoordinatePoint :=
  match axis with
  | 0 => ![input.2 0,
      Real.cos input.1 * input.2 1 - Real.sin input.1 * input.2 2,
      Real.sin input.1 * input.2 1 + Real.cos input.1 * input.2 2]
  | 1 => ![Real.cos input.1 * input.2 0 + Real.sin input.1 * input.2 2,
      input.2 1,
      -Real.sin input.1 * input.2 0 + Real.cos input.1 * input.2 2]
  | 2 => ![Real.cos input.1 * input.2 0 - Real.sin input.1 * input.2 1,
      Real.sin input.1 * input.2 0 + Real.cos input.1 * input.2 1,
      input.2 2]

private def euclideanThroatRotationFlow
    (axis : Fin 3) (input : Real × EuclideanR3) : EuclideanR3 :=
  (EuclideanSpace.equiv (Fin 3) Real).symm
    (throatCoordinateRotationFlow axis
      (input.1, (EuclideanSpace.equiv (Fin 3) Real) input.2))

private theorem euclideanThroatRotationFlow_contDiff (axis : Fin 3) :
    ContDiff Real ∞ (euclideanThroatRotationFlow axis) := by
  exact (EuclideanSpace.equiv (Fin 3) Real).symm.contDiff.comp
    (by
      rw [contDiff_pi]
      intro index
      fin_cases axis <;> fin_cases index <;>
        simp [throatCoordinateRotationFlow] <;> fun_prop)

@[simp]
private theorem euclideanThroatRotationFlow_zero
    (axis : Fin 3) (point : EuclideanR3) :
    euclideanThroatRotationFlow axis (0, point) = point := by
  fin_cases axis <;> ext index <;> fin_cases index <;>
    simp [euclideanThroatRotationFlow, throatCoordinateRotationFlow]

private theorem euclideanThroatRotationFlow_hasDerivAt_zero
    (axis : Fin 3) (point : EuclideanR3) :
    HasDerivAt
      (fun time : Real => euclideanThroatRotationFlow axis (time, point))
      (euclideanThroatRotation axis point) 0 := by
  have hCosMul (value : Real) :
      HasDerivAt (fun time : Real => Real.cos time * value) 0 0 := by
    simpa using (Real.hasDerivAt_cos 0).mul_const value
  have hSinMul (value : Real) :
      HasDerivAt (fun time : Real => Real.sin time * value) value 0 := by
    simpa using (Real.hasDerivAt_sin 0).mul_const value
  have hCosSubSin (first second : Real) :
      HasDerivAt (fun time : Real =>
        Real.cos time * first - Real.sin time * second) (-second) 0 := by
    refine (((hCosMul first).sub (hSinMul second)).congr_deriv (by simp))
      |>.congr_of_eventuallyEq ?_
    exact Filter.Eventually.of_forall fun _ => rfl
  have hSinAddCos (first second : Real) :
      HasDerivAt (fun time : Real =>
        Real.sin time * first + Real.cos time * second) first 0 := by
    refine (((hSinMul first).add (hCosMul second)).congr_deriv (by simp))
      |>.congr_of_eventuallyEq ?_
    exact Filter.Eventually.of_forall fun _ => rfl
  have hCosAddSin (first second : Real) :
      HasDerivAt (fun time : Real =>
        Real.cos time * first + Real.sin time * second) second 0 := by
    refine (((hCosMul first).add (hSinMul second)).congr_deriv (by simp))
      |>.congr_of_eventuallyEq ?_
    exact Filter.Eventually.of_forall fun _ => rfl
  have hNegSinAddCos (first second : Real) :
      HasDerivAt (fun time : Real =>
        -(Real.sin time * first) + Real.cos time * second) (-first) 0 := by
    refine ((((hSinMul first).neg).add (hCosMul second)).congr_deriv (by simp))
      |>.congr_of_eventuallyEq ?_
    exact Filter.Eventually.of_forall fun _ => rfl
  apply (EuclideanSpace.equiv (Fin 3) Real).symm.hasFDerivAt.comp_hasDerivAt
  rw [hasDerivAt_pi]
  intro index
  fin_cases axis
  · fin_cases index
    · simpa [euclideanThroatRotationFlow, throatCoordinateRotationFlow,
        euclideanThroatRotation, throatCoordinateRotation,
        throatRotationOneLinear] using
        (hasDerivAt_const (x := (0 : Real))
          (c := (EuclideanSpace.equiv (Fin 3) Real point) 0))
    · simpa [euclideanThroatRotationFlow, throatCoordinateRotationFlow,
        euclideanThroatRotation, throatCoordinateRotation,
        throatRotationOneLinear] using
        hCosSubSin ((EuclideanSpace.equiv (Fin 3) Real point) 1)
          ((EuclideanSpace.equiv (Fin 3) Real point) 2)
    · simpa [euclideanThroatRotationFlow, throatCoordinateRotationFlow,
        euclideanThroatRotation, throatCoordinateRotation,
        throatRotationOneLinear] using
        hSinAddCos ((EuclideanSpace.equiv (Fin 3) Real point) 1)
          ((EuclideanSpace.equiv (Fin 3) Real point) 2)
  · fin_cases index
    · simpa [euclideanThroatRotationFlow, throatCoordinateRotationFlow,
        euclideanThroatRotation, throatCoordinateRotation,
        throatRotationTwoLinear] using
        hCosAddSin ((EuclideanSpace.equiv (Fin 3) Real point) 0)
          ((EuclideanSpace.equiv (Fin 3) Real point) 2)
    · simpa [euclideanThroatRotationFlow, throatCoordinateRotationFlow,
        euclideanThroatRotation, throatCoordinateRotation,
        throatRotationTwoLinear] using
        (hasDerivAt_const (x := (0 : Real))
          (c := (EuclideanSpace.equiv (Fin 3) Real point) 1))
    · simpa [euclideanThroatRotationFlow, throatCoordinateRotationFlow,
        euclideanThroatRotation, throatCoordinateRotation,
        throatRotationTwoLinear] using
        hNegSinAddCos ((EuclideanSpace.equiv (Fin 3) Real point) 0)
          ((EuclideanSpace.equiv (Fin 3) Real point) 2)
  · fin_cases index
    · simpa [euclideanThroatRotationFlow, throatCoordinateRotationFlow,
        euclideanThroatRotation, throatCoordinateRotation,
        throatRotationThreeLinear] using
        hCosSubSin ((EuclideanSpace.equiv (Fin 3) Real point) 0)
          ((EuclideanSpace.equiv (Fin 3) Real point) 1)
    · simpa [euclideanThroatRotationFlow, throatCoordinateRotationFlow,
        euclideanThroatRotation, throatCoordinateRotation,
        throatRotationThreeLinear] using
        hSinAddCos ((EuclideanSpace.equiv (Fin 3) Real point) 0)
          ((EuclideanSpace.equiv (Fin 3) Real point) 1)
    · simpa [euclideanThroatRotationFlow, throatCoordinateRotationFlow,
        euclideanThroatRotation, throatCoordinateRotation,
        throatRotationThreeLinear] using
        (hasDerivAt_const (x := (0 : Real))
          (c := (EuclideanSpace.equiv (Fin 3) Real point) 2))

private theorem euclideanThroatRotationFlow_preserves_norm_sq
    (axis : Fin 3) (input : Real × EuclideanR3) :
    ‖euclideanThroatRotationFlow axis input‖ ^ 2 = ‖input.2‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  fin_cases axis <;>
    simp [euclideanThroatRotationFlow, throatCoordinateRotationFlow,
      Fin.sum_univ_succ] <;>
    nlinarith [Real.sin_sq_add_cos_sq input.1]

private theorem euclideanThroatRotationFlow_mem_sphere
    (axis : Fin 3) (input : Real × StandardEquatorialTwoSphere) :
    euclideanThroatRotationFlow axis (input.1, input.2.1) ∈
      Metric.sphere (0 : EuclideanR3) 1 := by
  rw [Metric.mem_sphere, dist_zero_right]
  have hNorm : ‖input.2.1‖ = 1 := by
    simpa [Metric.mem_sphere, dist_zero_right] using input.2.2
  have hSquare := euclideanThroatRotationFlow_preserves_norm_sq
    axis (input.1, input.2.1)
  rw [hNorm] at hSquare
  nlinarith [norm_nonneg
    (euclideanThroatRotationFlow axis (input.1, input.2.1))]

private def standardEquatorSpatialRotationFlow
    (axis : Fin 3) (input : Real × StandardEquatorialTwoSphere) :
    StandardEquatorialTwoSphere :=
  ⟨euclideanThroatRotationFlow axis (input.1, input.2.1),
    euclideanThroatRotationFlow_mem_sphere axis input⟩

private theorem standardEquatorSpatialRotationFlow_contMDiff
    (axis : Fin 3) :
    ContMDiff (𝓘(Real, Real).prod (𝓡 2)) (𝓡 2) ∞
      (standardEquatorSpatialRotationFlow axis) := by
  letI : Fact (Module.finrank Real EuclideanR3 = 2 + 1) := ⟨by simp⟩
  apply ContMDiff.codRestrict_sphere
  exact (euclideanThroatRotationFlow_contDiff axis).comp_contMDiff
    (contMDiff_fst.prodMk_space (contMDiff_coe_sphere.comp contMDiff_snd))

/-- The restricted rotation flow on the actual algebraic equator. -/
def equatorialSpatialRotationFlow
    (axis : Fin 3) (input : Real × EquatorialTwoSphere) :
    EquatorialTwoSphere :=
  ⟨ambientSpatialRotationFlow axis (input.1, input.2.1),
    ambientSpatialRotationFlow_preserves_equator axis
      (input.1, input.2.1) input.2.2⟩

@[simp]
private theorem equatorialTwoSphereHomeomorph_apply_coordinate
    (point : EquatorialTwoSphere) (index : Fin 3) :
    (EuclideanSpace.equiv (Fin 3) Real
      (equatorialTwoSphereHomeomorph point).1) index =
        point.1 index.succ := by
  rfl

private theorem equatorialTwoSphereHomeomorph_rotationFlow
    (axis : Fin 3) (input : Real × EquatorialTwoSphere) :
    equatorialTwoSphereHomeomorph
        (equatorialSpatialRotationFlow axis input) =
      standardEquatorSpatialRotationFlow axis
        (input.1, equatorialTwoSphereHomeomorph input.2) := by
  apply Subtype.ext
  apply (EuclideanSpace.equiv (Fin 3) Real).injective
  funext index
  rw [equatorialTwoSphereHomeomorph_apply_coordinate]
  change ambientSpatialRotationFlow axis (input.1, input.2.1) index.succ =
    throatCoordinateRotationFlow axis
      (input.1, fun current => input.2.1 current.succ) index
  fin_cases axis <;> fin_cases index <;> rfl

theorem equatorialSpatialRotationFlow_contMDiff (axis : Fin 3) :
    ContMDiff (𝓘(Real, Real).prod (𝓡 2)) (𝓡 2) ∞
      (equatorialSpatialRotationFlow axis) := by
  have hTo := chartedSpacePullback_toFun_contMDiff (𝓡 2) ∞
    equatorialTwoSphereHomeomorph
  have hInv := chartedSpacePullback_invFun_contMDiff (𝓡 2) ∞
    equatorialTwoSphereHomeomorph
  have hTransported : ContMDiff (𝓘(Real, Real).prod (𝓡 2)) (𝓡 2) ∞
      (fun input : Real × EquatorialTwoSphere =>
        equatorialTwoSphereHomeomorph.symm
          (standardEquatorSpatialRotationFlow axis
            (input.1, equatorialTwoSphereHomeomorph input.2))) :=
    hInv.comp ((standardEquatorSpatialRotationFlow_contMDiff axis).comp
      (contMDiff_fst.prodMk (hTo.comp contMDiff_snd)))
  apply hTransported.congr
  intro input
  apply equatorialTwoSphereHomeomorph.injective
  exact equatorialTwoSphereHomeomorph_rotationFlow axis input

@[simp]
theorem equatorialSpatialRotationFlow_zero
    (axis : Fin 3) (point : EquatorialTwoSphere) :
    equatorialSpatialRotationFlow axis (0, point) = point := by
  apply Subtype.ext
  exact ambientSpatialRotationFlow_zero axis point.1

@[simp]
theorem equatorialSpatialRotationFlow_coe
    (axis : Fin 3) (input : Real × EquatorialTwoSphere) :
    (equatorialSpatialRotationFlow axis input).1 =
      ambientSpatialRotationFlow axis (input.1, input.2.1) := by
  rfl

/-- Rotation of the equatorial factor with mapping-torus time fixed. -/
def throatCoverSpatialRotationFlow
    (axis : Fin 3) (input : Real × EffectiveThroatCover period hPeriod) :
    EffectiveThroatCover period hPeriod :=
  ⟨equatorialSpatialRotationFlow axis (input.1, input.2.fiber),
    input.2.time⟩

@[simp]
theorem throatCoverSpatialRotationFlow_zero
    (axis : Fin 3) (point : EffectiveThroatCover period hPeriod) :
    throatCoverSpatialRotationFlow period hPeriod axis (0, point) = point := by
  apply MappingTorusCover.ext
  · simp [throatCoverSpatialRotationFlow]
  · rfl

theorem throatCoverSpatialRotationFlow_deck_commutes
    (axis : Fin 3) (winding : Int)
    (input : Real × EffectiveThroatCover period hPeriod) :
    winding +ᵥ throatCoverSpatialRotationFlow period hPeriod axis input =
      throatCoverSpatialRotationFlow period hPeriod axis
        (input.1, winding +ᵥ input.2) := by
  apply MappingTorusCover.ext
  · change (Homeomorph.refl EquatorialTwoSphere ^ winding)
        (equatorialSpatialRotationFlow axis (input.1, input.2.fiber)) =
      equatorialSpatialRotationFlow axis
        (input.1,
          (Homeomorph.refl EquatorialTwoSphere ^ winding) input.2.fiber)
    have hIdentity :
        (Homeomorph.refl EquatorialTwoSphere ^ winding) =
          (1 : Homeomorph EquatorialTwoSphere EquatorialTwoSphere) := by
      change (1 : Homeomorph EquatorialTwoSphere EquatorialTwoSphere) ^
        winding = 1
      simp
    rw [hIdentity]
    rfl
  · simp [throatCoverSpatialRotationFlow]

theorem throatCoverSpatialRotationFlow_contMDiff (axis : Fin 3) :
    ContMDiff (𝓘(Real, Real).prod throatCoverModelWithCorners)
      throatCoverModelWithCorners ∞
      (throatCoverSpatialRotationFlow period hPeriod axis) := by
  let productEquiv := coverHomeomorphProd (throatData period hPeriod)
  have hTo := chartedSpacePullback_toFun_contMDiff
    throatCoverModelWithCorners ∞ productEquiv
  have hInv := chartedSpacePullback_invFun_contMDiff
    throatCoverModelWithCorners ∞ productEquiv
  have hFiber : ContMDiff throatCoverModelWithCorners (𝓡 2) ∞
      (fun point : EffectiveThroatCover period hPeriod => point.fiber) :=
    contMDiff_fst.comp hTo
  have hTime : ContMDiff throatCoverModelWithCorners 𝓘(Real, Real) ∞
      (fun point : EffectiveThroatCover period hPeriod => point.time) :=
    contMDiff_snd.comp hTo
  have hSphere := (equatorialSpatialRotationFlow_contMDiff axis).comp
    (contMDiff_fst.prodMk (hFiber.comp contMDiff_snd))
  exact hInv.comp (hSphere.prodMk (hTime.comp contMDiff_snd))

private def throatRotationFlowInputBundle
    (point : EffectiveThroatCover period hPeriod) :
    TangentBundle (𝓘(Real, Real).prod throatCoverModelWithCorners)
      (Real × EffectiveThroatCover period hPeriod) :=
  (equivTangentBundleProd 𝓘(Real, Real) Real throatCoverModelWithCorners
      (EffectiveThroatCover period hPeriod)).symm
    (⟨0, 1⟩, ⟨point, 0⟩)

private theorem throatRotationFlowInputBundle_contMDiff :
    ContMDiff throatCoverModelWithCorners
      (𝓘(Real, Real).prod throatCoverModelWithCorners).tangent ∞
      (throatRotationFlowInputBundle period hPeriod) := by
  apply (contMDiff_equivTangentBundleProd_symm
    (I := 𝓘(Real, Real)) (I' := throatCoverModelWithCorners)
    (M := Real) (M' := EffectiveThroatCover period hPeriod)).comp
  exact contMDiff_const.prodMk
    ((Bundle.contMDiff_zeroSection Real
      (TangentSpace throatCoverModelWithCorners :
        EffectiveThroatCover period hPeriod → Type _)).of_le le_top)

private def rawThroatCoverSpatialRotationBundle
    (axis : Fin 3) (point : EffectiveThroatCover period hPeriod) :
    TangentBundle throatCoverModelWithCorners
      (EffectiveThroatCover period hPeriod) :=
  tangentMap (𝓘(Real, Real).prod throatCoverModelWithCorners)
    throatCoverModelWithCorners
    (throatCoverSpatialRotationFlow period hPeriod axis)
    (throatRotationFlowInputBundle period hPeriod point)

private theorem rawThroatCoverSpatialRotationBundle_contMDiff
    (axis : Fin 3) :
    ContMDiff throatCoverModelWithCorners
      throatCoverModelWithCorners.tangent ∞
      (rawThroatCoverSpatialRotationBundle period hPeriod axis) :=
  ((throatCoverSpatialRotationFlow_contMDiff period hPeriod axis)
      |>.contMDiff_tangentMap (m := ∞) (by simp)).comp
    (throatRotationFlowInputBundle_contMDiff period hPeriod)

private theorem rawThroatCoverSpatialRotationBundle_base
    (axis : Fin 3) (point : EffectiveThroatCover period hPeriod) :
    (rawThroatCoverSpatialRotationBundle period hPeriod axis point).1 = point :=
  throatCoverSpatialRotationFlow_zero period hPeriod axis point

/-- Infinitesimal generator of the restricted flow upstairs. -/
def throatCoverSpatialRotationValue
    (axis : Fin 3) (point : EffectiveThroatCover period hPeriod) :
    ThroatCoverTangent period hPeriod point :=
  (rawThroatCoverSpatialRotationBundle_base period hPeriod axis point) ▸
    (rawThroatCoverSpatialRotationBundle period hPeriod axis point).2

private theorem throatCoverSpatialRotationValue_bundle
    (axis : Fin 3) (point : EffectiveThroatCover period hPeriod) :
    (⟨point, throatCoverSpatialRotationValue period hPeriod axis point⟩ :
        TangentBundle throatCoverModelWithCorners
          (EffectiveThroatCover period hPeriod)) =
      rawThroatCoverSpatialRotationBundle period hPeriod axis point := by
  let raw := rawThroatCoverSpatialRotationBundle period hPeriod axis point
  have hBase : raw.1 = point :=
    rawThroatCoverSpatialRotationBundle_base period hPeriod axis point
  change (⟨point, hBase ▸ raw.2⟩ :
      TangentBundle throatCoverModelWithCorners
        (EffectiveThroatCover period hPeriod)) = raw
  rcases raw with ⟨base, vector⟩
  simp only at hBase
  subst base
  rfl

private def throatCoverSpatialRotationSection (axis : Fin 3) :
    CInfinityThroatCoverGhost period hPeriod where
  toFun := throatCoverSpatialRotationValue period hPeriod axis
  contMDiff_toFun :=
    (rawThroatCoverSpatialRotationBundle_contMDiff period hPeriod axis).congr
      (fun point => throatCoverSpatialRotationValue_bundle
        period hPeriod axis point)

private def throatCoverSpatialRotationCurve
    (axis : Fin 3) (point : EffectiveThroatCover period hPeriod)
    (time : Real) : EffectiveThroatCover period hPeriod :=
  throatCoverSpatialRotationFlow period hPeriod axis (time, point)

private theorem throatCoverSpatialRotationCurve_contMDiff
    (axis : Fin 3) (point : EffectiveThroatCover period hPeriod) :
    ContMDiff 𝓘(Real, Real) throatCoverModelWithCorners ∞
      (throatCoverSpatialRotationCurve period hPeriod axis point) :=
  (throatCoverSpatialRotationFlow_contMDiff period hPeriod axis).comp
    (contMDiff_id.prodMk contMDiff_const)

private theorem throatCoverSpatialRotationCurve_deck
    (axis : Fin 3) (winding : Int)
    (point : EffectiveThroatCover period hPeriod) :
    throatCoverSpatialRotationCurve period hPeriod axis (winding +ᵥ point) =
      (winding +ᵥ ·) ∘
        throatCoverSpatialRotationCurve period hPeriod axis point := by
  funext time
  exact (throatCoverSpatialRotationFlow_deck_commutes
    period hPeriod axis winding (time, point)).symm

private theorem rawThroatCoverSpatialRotationBundle_eq_curve
    (axis : Fin 3) (point : EffectiveThroatCover period hPeriod) :
    rawThroatCoverSpatialRotationBundle period hPeriod axis point =
      tangentMap 𝓘(Real, Real) throatCoverModelWithCorners
        (throatCoverSpatialRotationCurve period hPeriod axis point)
        (⟨0, 1⟩ : TangentBundle 𝓘(Real, Real) Real) := by
  let slice : Real → Real × EffectiveThroatCover period hPeriod :=
    fun time => (time, point)
  have hFlowAt : MDifferentiableAt
      (𝓘(Real, Real).prod throatCoverModelWithCorners)
      throatCoverModelWithCorners
      (throatCoverSpatialRotationFlow period hPeriod axis) (0, point) :=
    (throatCoverSpatialRotationFlow_contMDiff period hPeriod axis)
      |>.mdifferentiableAt (by simp)
  have hSliceAt : MDifferentiableAt 𝓘(Real, Real)
      (𝓘(Real, Real).prod throatCoverModelWithCorners) slice 0 :=
    mdifferentiableAt_id.prodMk mdifferentiableAt_const
  have hComp := tangentMap_comp_at
    (I := 𝓘(Real, Real))
    (I' := 𝓘(Real, Real).prod throatCoverModelWithCorners)
    (I'' := throatCoverModelWithCorners)
    (f := slice)
    (g := throatCoverSpatialRotationFlow period hPeriod axis)
    (⟨0, 1⟩ : TangentBundle 𝓘(Real, Real) Real)
    hFlowAt hSliceAt
  rw [tangentMap_prod_left] at hComp
  change tangentMap 𝓘(Real, Real) throatCoverModelWithCorners
      (throatCoverSpatialRotationCurve period hPeriod axis point)
      (⟨0, 1⟩ : TangentBundle 𝓘(Real, Real) Real) =
    rawThroatCoverSpatialRotationBundle period hPeriod axis point at hComp
  exact hComp.symm

theorem throatCoverSpatialRotationValue_eq_curve_mfderiv
    (axis : Fin 3) (point : EffectiveThroatCover period hPeriod) :
    throatCoverSpatialRotationValue period hPeriod axis point =
      mfderiv 𝓘(Real, Real) throatCoverModelWithCorners
        (throatCoverSpatialRotationCurve period hPeriod axis point) 0 1 := by
  apply (TotalSpace.mk_injective
    (F := ThroatCoverCoordinates) (b := point))
  calc
    (⟨point, throatCoverSpatialRotationValue period hPeriod axis point⟩ :
        TangentBundle throatCoverModelWithCorners
          (EffectiveThroatCover period hPeriod)) =
      rawThroatCoverSpatialRotationBundle period hPeriod axis point :=
        throatCoverSpatialRotationValue_bundle period hPeriod axis point
    _ = tangentMap 𝓘(Real, Real) throatCoverModelWithCorners
        (throatCoverSpatialRotationCurve period hPeriod axis point)
        (⟨0, 1⟩ : TangentBundle 𝓘(Real, Real) Real) :=
      rawThroatCoverSpatialRotationBundle_eq_curve
        period hPeriod axis point
    _ = (⟨point,
          mfderiv 𝓘(Real, Real) throatCoverModelWithCorners
            (throatCoverSpatialRotationCurve period hPeriod axis point)
            0 1⟩ :
        TangentBundle throatCoverModelWithCorners
          (EffectiveThroatCover period hPeriod)) := by
      simp [tangentMap, throatCoverSpatialRotationCurve]
      exact HEq.rfl

private theorem rawThroatCoverSpatialRotationBundle_deck
    (axis : Fin 3) (winding : Int)
    (point : EffectiveThroatCover period hPeriod) :
    rawThroatCoverSpatialRotationBundle period hPeriod axis
        (winding +ᵥ point) =
      tangentMap throatCoverModelWithCorners throatCoverModelWithCorners
        (winding +ᵥ ·)
        (rawThroatCoverSpatialRotationBundle period hPeriod axis point) := by
  rw [rawThroatCoverSpatialRotationBundle_eq_curve,
    rawThroatCoverSpatialRotationBundle_eq_curve,
    throatCoverSpatialRotationCurve_deck]
  exact tangentMap_comp_at
    (I := 𝓘(Real, Real)) (I' := throatCoverModelWithCorners)
    (I'' := throatCoverModelWithCorners)
    (f := throatCoverSpatialRotationCurve period hPeriod axis point)
    (g := (winding +ᵥ ·))
    (⟨0, 1⟩ : TangentBundle 𝓘(Real, Real) Real)
    ((fixedThroatCover_deck_contMDiff period hPeriod winding)
      |>.mdifferentiableAt (by simp))
    ((throatCoverSpatialRotationCurve_contMDiff
      period hPeriod axis point).mdifferentiableAt (by simp))

theorem throatCoverSpatialRotationValue_deck_equivariant
    (axis : Fin 3) (winding : Int)
    (point : EffectiveThroatCover period hPeriod) :
    throatCoverSpatialRotationValue period hPeriod axis (winding +ᵥ point) =
      mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
        (winding +ᵥ ·) point
        (throatCoverSpatialRotationValue period hPeriod axis point) := by
  have hTotal :
      (⟨winding +ᵥ point,
          throatCoverSpatialRotationValue period hPeriod axis
            (winding +ᵥ point)⟩ :
        TangentBundle throatCoverModelWithCorners
          (EffectiveThroatCover period hPeriod)) =
      tangentMap throatCoverModelWithCorners throatCoverModelWithCorners
        (winding +ᵥ ·)
        (⟨point, throatCoverSpatialRotationValue period hPeriod axis point⟩ :
          TangentBundle throatCoverModelWithCorners
            (EffectiveThroatCover period hPeriod)) := by
    calc
      _ = rawThroatCoverSpatialRotationBundle period hPeriod axis
          (winding +ᵥ point) :=
        throatCoverSpatialRotationValue_bundle period hPeriod axis _
      _ = tangentMap throatCoverModelWithCorners throatCoverModelWithCorners
          (winding +ᵥ ·)
          (rawThroatCoverSpatialRotationBundle period hPeriod axis point) :=
        rawThroatCoverSpatialRotationBundle_deck
          period hPeriod axis winding point
      _ = _ := congrArg
        (tangentMap throatCoverModelWithCorners throatCoverModelWithCorners
          (winding +ᵥ ·))
        (throatCoverSpatialRotationValue_bundle
          period hPeriod axis point).symm
  apply (TotalSpace.mk_injective
    (F := ThroatCoverCoordinates) (b := winding +ᵥ point))
  simpa [tangentMap] using hTotal

/-- Smooth throat-cover ghost with the derivative cocycle needed for descent. -/
structure SmoothDeckEquivariantThroatCoverGhost where
  field : CInfinityThroatCoverGhost period hPeriod
  deck_equivariant : ∀ (winding : Int)
      (point : EffectiveThroatCover period hPeriod),
    field (winding +ᵥ point) =
      mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
        (winding +ᵥ ·) point (field point)

/-- The restricted rotation generators satisfy the exact deck cocycle. -/
def smoothDeckEquivariantThroatCoverSpatialRotation (axis : Fin 3) :
    SmoothDeckEquivariantThroatCoverGhost period hPeriod where
  field := throatCoverSpatialRotationSection period hPeriod axis
  deck_equivariant :=
    throatCoverSpatialRotationValue_deck_equivariant
      period hPeriod axis

private def throatProjectionDerivativeEquiv
    (point : EffectiveThroatCover period hPeriod) :
    ThroatCoverTangent period hPeriod point ≃L[Real]
      TangentSpace throatCoverModelWithCorners
        (mappingTorusMk (throatData period hPeriod) point) :=
  (fixedThroat_projection_isLocalDiffeomorph period hPeriod)
    |>.mfderivToContinuousLinearEquiv (by simp) point

@[simp]
private theorem throatProjectionDerivativeEquiv_coe
    (point : EffectiveThroatCover period hPeriod) :
    (throatProjectionDerivativeEquiv period hPeriod point :
      ThroatCoverTangent period hPeriod point →L[Real]
        TangentSpace throatCoverModelWithCorners
          (mappingTorusMk (throatData period hPeriod) point)) =
      mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
        (mappingTorusMk (throatData period hPeriod)) point :=
  IsLocalDiffeomorph.mfderivToContinuousLinearEquiv_coe
    (fixedThroat_projection_isLocalDiffeomorph period hPeriod)
      (by simp) point

private def projectedThroatCoverGhostValue
    (ghost : SmoothDeckEquivariantThroatCoverGhost period hPeriod)
    (point : EffectiveThroatCover period hPeriod) :
    TangentSpace throatCoverModelWithCorners
      (mappingTorusMk (throatData period hPeriod) point) :=
  throatProjectionDerivativeEquiv period hPeriod point (ghost.field point)

private def descendedThroatCoverGhostValue
    (ghost : SmoothDeckEquivariantThroatCoverGhost period hPeriod) :
    ∀ point : EffectiveThroat period hPeriod,
      TangentSpace throatCoverModelWithCorners point :=
  fun quotientPoint =>
    Quotient.hrecOn quotientPoint
      (projectedThroatCoverGhostValue period hPeriod ghost)
      (fun firstPoint secondPoint hOrbit => by
        have hProjection :
            mappingTorusMk (throatData period hPeriod) firstPoint =
              mappingTorusMk (throatData period hPeriod) secondPoint :=
          Quotient.sound hOrbit
        obtain ⟨winding, hWinding⟩ :=
          (mappingTorusMk_eq_iff_exists_vadd
            (throatData period hPeriod) firstPoint secondPoint).1 hProjection
        subst firstPoint
        clear hOrbit
        have hTangent :
            TangentSpace throatCoverModelWithCorners
                (mappingTorusMk (throatData period hPeriod)
                  (winding +ᵥ secondPoint)) =
              TangentSpace throatCoverModelWithCorners
                (mappingTorusMk (throatData period hPeriod) secondPoint) :=
          congrArg (TangentSpace throatCoverModelWithCorners) hProjection
        cases hTangent
        apply heq_of_eq
        have hNatural
            (vector : ThroatCoverTangent period hPeriod secondPoint) :
            mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
                (mappingTorusMk (throatData period hPeriod))
                (winding +ᵥ secondPoint)
                (mfderiv throatCoverModelWithCorners
                  throatCoverModelWithCorners
                  (winding +ᵥ ·) secondPoint vector) =
              mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
                (mappingTorusMk (throatData period hPeriod))
                secondPoint vector := by
          have hProjectionAt : MDifferentiableAt throatCoverModelWithCorners
              throatCoverModelWithCorners
              (mappingTorusMk (throatData period hPeriod))
              (winding +ᵥ secondPoint) :=
            (fixedThroat_projection_isLocalDiffeomorph period hPeriod)
              |>.contMDiff.mdifferentiableAt (by simp)
          have hDeckAt : MDifferentiableAt throatCoverModelWithCorners
              throatCoverModelWithCorners (winding +ᵥ ·) secondPoint :=
            (fixedThroatCover_deck_contMDiff period hPeriod winding)
              |>.mdifferentiableAt (by simp)
          have hComposite := mfderiv_comp secondPoint hProjectionAt hDeckAt
          have hMap :
              (mappingTorusMk (throatData period hPeriod)) ∘
                  (winding +ᵥ ·) =
                mappingTorusMk (throatData period hPeriod) := by
            funext point
            exact (mappingTorusMk_eq_iff_exists_vadd
              (throatData period hPeriod) _ _).2 ⟨winding, rfl⟩
          calc
            _ = mfderiv throatCoverModelWithCorners
                  throatCoverModelWithCorners
                  ((mappingTorusMk (throatData period hPeriod)) ∘
                    (winding +ᵥ ·)) secondPoint vector := by
              rw [hComposite]
              rfl
            _ = _ := by rw [hMap]
        change throatProjectionDerivativeEquiv period hPeriod
              (winding +ᵥ secondPoint)
              (ghost.field (winding +ᵥ secondPoint)) =
            throatProjectionDerivativeEquiv period hPeriod secondPoint
              (ghost.field secondPoint)
        rw [ghost.deck_equivariant]
        change mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
              (mappingTorusMk (throatData period hPeriod))
              (winding +ᵥ secondPoint)
              (mfderiv throatCoverModelWithCorners
                throatCoverModelWithCorners
                (winding +ᵥ ·) secondPoint (ghost.field secondPoint)) = _
        exact hNatural (ghost.field secondPoint))

@[simp]
private theorem descendedThroatCoverGhostValue_mk
    (ghost : SmoothDeckEquivariantThroatCoverGhost period hPeriod)
    (point : EffectiveThroatCover period hPeriod) :
    descendedThroatCoverGhostValue period hPeriod ghost
        (mappingTorusMk (throatData period hPeriod) point) =
      projectedThroatCoverGhostValue period hPeriod ghost point :=
  rfl

/-- Smooth descent through the genuine fixed-throat quotient projection. -/
def descendSmoothDeckEquivariantThroatCoverGhost
    (ghost : SmoothDeckEquivariantThroatCoverGhost period hPeriod) :
    CInfinityThroatGhost period hPeriod where
  toFun := descendedThroatCoverGhostValue period hPeriod ghost
  contMDiff_toFun := by
    intro quotientPoint
    obtain ⟨anchor, rfl⟩ :=
      mappingTorusMk_surjective (throatData period hPeriod) quotientPoint
    let projection := mappingTorusMk (throatData period hPeriod)
    let hAt := fixedThroat_projection_isLocalDiffeomorph
      period hPeriod anchor
    have hLocalInverse : ContMDiffAt throatCoverModelWithCorners
        throatCoverModelWithCorners ∞ hAt.localInverse (projection anchor) :=
      hAt.localInverse_contMDiffAt.of_le (by simp)
    have hFieldLocal := ghost.field.contMDiff.contMDiffAt.comp
      (projection anchor) hLocalInverse
    have hProjectionSmooth : ContMDiff throatCoverModelWithCorners
        throatCoverModelWithCorners ∞ projection :=
      (fixedThroat_projection_isLocalDiffeomorph period hPeriod).contMDiff
        |>.of_le (by simp)
    have hTangentMap := hProjectionSmooth.contMDiff_tangentMap
      (m := ∞) (by simp)
    have hLocalSmooth := hTangentMap.contMDiffAt.comp
      (projection anchor) hFieldLocal
    apply hLocalSmooth.congr_of_eventuallyEq
    filter_upwards [hAt.localInverse_eventuallyEq_right] with current hCurrent
    have hRight : projection (hAt.localInverse current) = current := by
      simpa [Function.comp_def] using hCurrent
    calc
      (⟨current, descendedThroatCoverGhostValue
          period hPeriod ghost current⟩ :
          TangentBundle throatCoverModelWithCorners
            (EffectiveThroat period hPeriod)) =
          ⟨projection (hAt.localInverse current),
            descendedThroatCoverGhostValue period hPeriod ghost
              (projection (hAt.localInverse current))⟩ :=
        congrArg (fun point =>
          (⟨point, descendedThroatCoverGhostValue
            period hPeriod ghost point⟩ :
            TangentBundle throatCoverModelWithCorners
              (EffectiveThroat period hPeriod))) hRight.symm
      _ = (tangentMap throatCoverModelWithCorners
            throatCoverModelWithCorners projection ∘
            (fun point =>
              (⟨point, ghost.field point⟩ :
                TangentBundle throatCoverModelWithCorners
                  (EffectiveThroatCover period hPeriod))) ∘
            hAt.localInverse) current := by
        apply TotalSpace.ext rfl
        simp

@[simp]
theorem descendSmoothDeckEquivariantThroatCoverGhost_mk
    (ghost : SmoothDeckEquivariantThroatCoverGhost period hPeriod)
    (point : EffectiveThroatCover period hPeriod) :
    descendSmoothDeckEquivariantThroatCoverGhost period hPeriod ghost
        (mappingTorusMk (throatData period hPeriod) point) =
      throatProjectionDerivativeEquiv period hPeriod point
        (ghost.field point) :=
  rfl

/-- The three quotient ghosts generated by the restricted rotation flows. -/
def throatSpatialRotationGhost (axis : Fin 3) :
    CInfinityThroatGhost period hPeriod :=
  descendSmoothDeckEquivariantThroatCoverGhost period hPeriod
    (smoothDeckEquivariantThroatCoverSpatialRotation
      period hPeriod axis)

/-! ## Polar bracket naturality on the throat cover -/

private def throatPositiveReal : Opens Real := ⟨Ioi 0, isOpen_Ioi⟩

private def nonzeroEuclideanR3 : Opens EuclideanR3 :=
  ⟨({0}ᶜ : Set EuclideanR3), isOpen_compl_singleton⟩

private def equatorDiffeomorph :
    EquatorialTwoSphere ≃ₘ⟮(𝓡 2), (𝓡 2)⟯ StandardEquatorialTwoSphere where
  toEquiv := equatorialTwoSphereHomeomorph.toEquiv
  contMDiff_toFun := chartedSpacePullback_toFun_contMDiff (𝓡 2) ∞
    equatorialTwoSphereHomeomorph
  contMDiff_invFun := chartedSpacePullback_invFun_contMDiff (𝓡 2) ∞
    equatorialTwoSphereHomeomorph

private def throatCoverDiffeomorphProd :
    EffectiveThroatCover period hPeriod ≃ₘ⟮
      throatCoverModelWithCorners, throatCoverModelWithCorners⟯
      (EquatorialTwoSphere × Real) where
  toEquiv := (coverHomeomorphProd (throatData period hPeriod)).toEquiv
  contMDiff_toFun := chartedSpacePullback_toFun_contMDiff
    throatCoverModelWithCorners ∞
      (coverHomeomorphProd (throatData period hPeriod))
  contMDiff_invFun := chartedSpacePullback_invFun_contMDiff
    throatCoverModelWithCorners ∞
      (coverHomeomorphProd (throatData period hPeriod))

private def throatExpToPositive (value : Real) : throatPositiveReal :=
  ⟨Real.exp value, Real.exp_pos value⟩

private def throatPositiveLog (value : throatPositiveReal) : Real :=
  Real.log value

private theorem throatExpToPositive_contMDiff :
    ContMDiff 𝓘(Real, Real) 𝓘(Real, Real) ∞ throatExpToPositive := by
  rw [← ContMDiff.subtypeVal_comp_iff]
  simpa [throatExpToPositive, Function.comp_def] using
    Real.contDiff_exp.contMDiff

private theorem throatPositiveLog_contMDiff :
    ContMDiff 𝓘(Real, Real) 𝓘(Real, Real) ∞ throatPositiveLog := by
  intro value
  change ContMDiffAt 𝓘(Real, Real) 𝓘(Real, Real) ∞
    (fun current : throatPositiveReal => Real.log current) value
  rw [contMDiffAt_subtype_iff]
  exact (Real.contDiffAt_log.2 value.2.ne').contMDiffAt

private def throatExpDiffeomorph :
    Real ≃ₘ⟮𝓘(Real, Real), 𝓘(Real, Real)⟯ throatPositiveReal where
  toEquiv :=
    { toFun := throatExpToPositive
      invFun := throatPositiveLog
      left_inv := Real.log_exp
      right_inv := fun value => Subtype.ext (Real.exp_log value.2) }
  contMDiff_toFun := throatExpToPositive_contMDiff
  contMDiff_invFun := throatPositiveLog_contMDiff

private def normalizedThroatNonzero
    (point : nonzeroEuclideanR3) : EuclideanR3 :=
  ‖(point : EuclideanR3)‖⁻¹ • (point : EuclideanR3)

private theorem normalizedThroatNonzero_mem_sphere
    (point : nonzeroEuclideanR3) :
    normalizedThroatNonzero point ∈ Metric.sphere (0 : EuclideanR3) 1 := by
  rw [Metric.mem_sphere, dist_zero_right, normalizedThroatNonzero,
    norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_nonneg (norm_nonneg _), inv_mul_cancel₀]
  exact norm_ne_zero_iff.mpr point.2

private theorem nonzeroThroatNorm_contMDiff :
    ContMDiff 𝓘(Real, EuclideanR3) 𝓘(Real, Real) ∞
      (fun point : nonzeroEuclideanR3 => ‖(point : EuclideanR3)‖) := by
  intro point
  rw [contMDiffAt_subtype_iff]
  exact (contDiffAt_norm Real point.2).contMDiffAt

private theorem normalizedThroatNonzero_contMDiff :
    ContMDiff 𝓘(Real, EuclideanR3) 𝓘(Real, EuclideanR3) ∞
      normalizedThroatNonzero := by
  exact (nonzeroThroatNorm_contMDiff.inv₀
      (fun point => norm_ne_zero_iff.mpr point.2)).smul
    contMDiff_subtype_val

private def normalizedThroatNonzeroSphere
    (point : nonzeroEuclideanR3) : StandardEquatorialTwoSphere :=
  ⟨normalizedThroatNonzero point,
    normalizedThroatNonzero_mem_sphere point⟩

private theorem normalizedThroatNonzeroSphere_contMDiff :
    ContMDiff 𝓘(Real, EuclideanR3) (𝓡 2) ∞
      normalizedThroatNonzeroSphere := by
  letI : Fact (Module.finrank Real EuclideanR3 = 2 + 1) := ⟨by simp⟩
  exact normalizedThroatNonzero_contMDiff.codRestrict_sphere
    normalizedThroatNonzero_mem_sphere

private def nonzeroThroatRadius
    (point : nonzeroEuclideanR3) : throatPositiveReal :=
  ⟨‖(point : EuclideanR3)‖, norm_pos_iff.mpr point.2⟩

private theorem nonzeroThroatRadius_contMDiff :
    ContMDiff 𝓘(Real, EuclideanR3) 𝓘(Real, Real) ∞
      nonzeroThroatRadius := by
  rw [← ContMDiff.subtypeVal_comp_iff]
  exact nonzeroThroatNorm_contMDiff

private def throatRadialDiffeomorph :
    (StandardEquatorialTwoSphere × throatPositiveReal) ≃ₘ⟮
      throatCoverModelWithCorners, 𝓘(Real, EuclideanR3)⟯
      nonzeroEuclideanR3 where
  toEquiv :=
    { toFun := fun point => (homeomorphUnitSphereProd EuclideanR3).symm point
      invFun := fun point => homeomorphUnitSphereProd EuclideanR3 point
      left_inv := fun point =>
        (homeomorphUnitSphereProd EuclideanR3).apply_symm_apply point
      right_inv := fun point =>
        (homeomorphUnitSphereProd EuclideanR3).symm_apply_apply point }
  contMDiff_toFun := by
    letI : Fact (Module.finrank Real EuclideanR3 = 2 + 1) := ⟨by simp⟩
    rw [← ContMDiff.subtypeVal_comp_iff]
    change ContMDiff throatCoverModelWithCorners
      𝓘(Real, EuclideanR3) ∞
      (fun point : StandardEquatorialTwoSphere × throatPositiveReal =>
        (point.2 : Real) • (point.1 : EuclideanR3))
    exact (contMDiff_subtype_val.comp contMDiff_snd).smul
      (contMDiff_coe_sphere.comp contMDiff_fst)
  contMDiff_invFun := by
    refine (normalizedThroatNonzeroSphere_contMDiff.prodMk
      nonzeroThroatRadius_contMDiff).congr ?_
    intro point
    apply Prod.ext
    · apply Subtype.ext
      simp [normalizedThroatNonzeroSphere, normalizedThroatNonzero]
    · apply Subtype.ext
      simp [nonzeroThroatRadius]

private def throatCoverRadialDiffeomorph :
    EffectiveThroatCover period hPeriod ≃ₘ⟮
      throatCoverModelWithCorners, 𝓘(Real, EuclideanR3)⟯
      nonzeroEuclideanR3 :=
  (throatCoverDiffeomorphProd period hPeriod).trans
    ((equatorDiffeomorph.prodCongr throatExpDiffeomorph).trans
      throatRadialDiffeomorph)

private def nonzeroThroatDefault : nonzeroEuclideanR3 :=
  ⟨EuclideanSpace.single 0 1, by
    show EuclideanSpace.single (0 : Fin 3) (1 : Real) ≠ 0
    exact (EuclideanSpace.single_eq_zero_iff
      (i := (0 : Fin 3)) (a := (1 : Real))).not.mpr one_ne_zero⟩

private def nonzeroThroatRetraction
    (point : EuclideanR3) : nonzeroEuclideanR3 :=
  if hPoint : point ≠ 0 then ⟨point, hPoint⟩ else nonzeroThroatDefault

private def nonzeroThroatInclusionPartialDiffeomorph :
    PartialDiffeomorph 𝓘(Real, EuclideanR3) 𝓘(Real, EuclideanR3)
      nonzeroEuclideanR3 EuclideanR3 ∞ where
  toPartialEquiv :=
    { toFun := Subtype.val
      invFun := nonzeroThroatRetraction
      source := Set.univ
      target := ({0}ᶜ : Set EuclideanR3)
      map_source' := fun point _ => point.2
      map_target' := fun _ _ => Set.mem_univ _
      left_inv' := by
        intro point _
        have hPoint : (point : EuclideanR3) ≠ 0 := point.2
        simp [nonzeroThroatRetraction, hPoint]
      right_inv' := by
        intro point hPoint
        have hPoint' : point ≠ 0 := by
          simpa only [mem_compl_iff, mem_singleton_iff] using hPoint
        simp [nonzeroThroatRetraction, hPoint'] }
  open_source := isOpen_univ
  open_target := isOpen_compl_singleton
  contMDiffOn_toFun := contMDiff_subtype_val.contMDiffOn
  contMDiffOn_invFun := by
    intro point hPoint
    apply (ContMDiffWithinAt.subtypeVal_comp_iff
      nonzeroEuclideanR3 nonzeroThroatRetraction ({0}ᶜ) point).mp
    exact contMDiffWithinAt_id.congr_of_mem (fun current hCurrent => by
      have hCurrent' : current ≠ 0 := by
        simpa only [mem_compl_iff, mem_singleton_iff] using hCurrent
      simp [nonzeroThroatRetraction, hCurrent']) hPoint

private theorem nonzeroThroatInclusion_isLocalDiffeomorph :
    IsLocalDiffeomorph 𝓘(Real, EuclideanR3) 𝓘(Real, EuclideanR3) ∞
      (Subtype.val : nonzeroEuclideanR3 → EuclideanR3) := by
  intro point
  exact PartialDiffeomorph.isLocalDiffeomorphAt
    (I := 𝓘(Real, EuclideanR3)) (J := 𝓘(Real, EuclideanR3))
    (n := ∞) nonzeroThroatInclusionPartialDiffeomorph (Set.mem_univ point)

/-- Polar coordinates identify the fixed-throat cover with punctured `ℝ³`. -/
def throatCoverRadialMap
    (point : EffectiveThroatCover period hPeriod) : EuclideanR3 :=
  (throatCoverRadialDiffeomorph period hPeriod point : nonzeroEuclideanR3)

@[simp]
theorem throatCoverRadialMap_apply
    (point : EffectiveThroatCover period hPeriod) :
    throatCoverRadialMap period hPeriod point =
      Real.exp point.time •
        (equatorialTwoSphereHomeomorph point.fiber).1 := by
  change (throatExpToPositive point.time : Real) •
      (equatorialTwoSphereHomeomorph point.fiber).1 = _
  rfl

theorem throatCoverRadialMap_isLocalDiffeomorph :
    IsLocalDiffeomorph throatCoverModelWithCorners
      𝓘(Real, EuclideanR3) ∞
      (throatCoverRadialMap period hPeriod) := by
  unfold throatCoverRadialMap
  intro point
  exact IsLocalDiffeomorphAt.comp
    (I := throatCoverModelWithCorners) (J := 𝓘(Real, EuclideanR3))
    (K := 𝓘(Real, EuclideanR3))
    (M := EffectiveThroatCover period hPeriod) (N := nonzeroEuclideanR3)
    (P := EuclideanR3) (n := ∞)
    ((throatCoverRadialDiffeomorph period hPeriod).isLocalDiffeomorph point)
    (nonzeroThroatInclusion_isLocalDiffeomorph
      (throatCoverRadialDiffeomorph period hPeriod point))

private theorem throatCoverRadialMap_comp_rotationCurve
    (axis : Fin 3) (point : EffectiveThroatCover period hPeriod) :
    throatCoverRadialMap period hPeriod ∘
        throatCoverSpatialRotationCurve period hPeriod axis point =
      fun time => Real.exp point.time •
        euclideanThroatRotationFlow axis
          (time, (equatorialTwoSphereHomeomorph point.fiber).1) := by
  funext time
  rw [Function.comp_apply, throatCoverRadialMap_apply]
  simp only [throatCoverSpatialRotationCurve,
    throatCoverSpatialRotationFlow]
  rw [equatorialTwoSphereHomeomorph_rotationFlow]
  rfl

private theorem throatCoverRadialMap_mfderiv_rotation
    (axis : Fin 3) (point : EffectiveThroatCover period hPeriod) :
    mfderiv throatCoverModelWithCorners 𝓘(Real, EuclideanR3)
        (throatCoverRadialMap period hPeriod) point
        (throatCoverSpatialRotationValue period hPeriod axis point) =
      euclideanThroatRotation axis
        (throatCoverRadialMap period hPeriod point) := by
  rw [throatCoverSpatialRotationValue_eq_curve_mfderiv]
  have hRadialAt : MDifferentiableAt throatCoverModelWithCorners
      𝓘(Real, EuclideanR3) (throatCoverRadialMap period hPeriod) point :=
    (throatCoverRadialMap_isLocalDiffeomorph period hPeriod point)
      |>.mdifferentiableAt (by simp)
  have hCurveAt : MDifferentiableAt 𝓘(Real, Real)
      throatCoverModelWithCorners
      (throatCoverSpatialRotationCurve period hPeriod axis point) 0 :=
    (throatCoverSpatialRotationCurve_contMDiff period hPeriod axis point)
      |>.mdifferentiableAt (by simp)
  have hCurveZero :
      throatCoverSpatialRotationCurve period hPeriod axis point 0 = point :=
    throatCoverSpatialRotationFlow_zero period hPeriod axis point
  have hComp := mfderiv_comp_apply_of_eq
    (I := 𝓘(Real, Real)) (I' := throatCoverModelWithCorners)
    (I'' := 𝓘(Real, EuclideanR3))
    (f := throatCoverSpatialRotationCurve period hPeriod axis point)
    (g := throatCoverRadialMap period hPeriod)
    (x := (0 : Real)) (y := point)
    hRadialAt hCurveAt hCurveZero (1 : Real)
  have hDerivative : HasDerivAt
      (fun time => Real.exp point.time •
        euclideanThroatRotationFlow axis
          (time, (equatorialTwoSphereHomeomorph point.fiber).1))
      (Real.exp point.time •
        euclideanThroatRotation axis
          (equatorialTwoSphereHomeomorph point.fiber).1) 0 :=
    (euclideanThroatRotationFlow_hasDerivAt_zero axis
      (equatorialTwoSphereHomeomorph point.fiber).1).const_smul
        (Real.exp point.time)
  calc
    _ = mfderiv 𝓘(Real, Real) 𝓘(Real, EuclideanR3)
        (throatCoverRadialMap period hPeriod ∘
          throatCoverSpatialRotationCurve period hPeriod axis point) 0 1 :=
      hComp.symm
    _ = Real.exp point.time •
        euclideanThroatRotation axis
          (equatorialTwoSphereHomeomorph point.fiber).1 := by
      rw [throatCoverRadialMap_comp_rotationCurve, mfderiv_eq_fderiv]
      exact hDerivative.deriv
    _ = _ := by
      rw [throatCoverRadialMap_apply, map_smul]

private theorem throatRadial_mfderiv_isInvertible
    (point : EffectiveThroatCover period hPeriod) :
    (mfderiv throatCoverModelWithCorners 𝓘(Real, EuclideanR3)
      (throatCoverRadialMap period hPeriod) point).IsInvertible := by
  let derivativeEquiv :=
    (throatCoverRadialMap_isLocalDiffeomorph period hPeriod)
      |>.mfderivToContinuousLinearEquiv (by simp) point
  rw [← IsLocalDiffeomorph.mfderivToContinuousLinearEquiv_coe
    (throatCoverRadialMap_isLocalDiffeomorph period hPeriod) (by simp) point]
  exact ⟨derivativeEquiv, rfl⟩

private theorem throatRadial_mpullback_rotation
    (axis : Fin 3) :
    VectorField.mpullback throatCoverModelWithCorners 𝓘(Real, EuclideanR3)
        (throatCoverRadialMap period hPeriod)
        (euclideanThroatRotationSection axis) =
      throatCoverSpatialRotationValue period hPeriod axis := by
  funext point
  rw [VectorField.mpullback_apply,
    (throatRadial_mfderiv_isInvertible period hPeriod point).inverse_apply_eq]
  exact (throatCoverRadialMap_mfderiv_rotation
    period hPeriod axis point).symm

private theorem throatCoverSpatialRotation_lieBracket
    (first second : Fin 3) :
    VectorField.mlieBracket throatCoverModelWithCorners
        (throatCoverSpatialRotationValue period hPeriod first)
        (throatCoverSpatialRotationValue period hPeriod second) =
      fun point => ∑ output : Fin 3,
        spatialRotationStructureConstant first second output •
          throatCoverSpatialRotationValue period hPeriod output point := by
  funext point
  have hSmooth : minSmoothness Real 2 ≤ (∞ : ℕ∞ω) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    change ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
    exact WithTop.coe_le_coe.mpr le_top
  have hNatural := VectorField.mpullback_mlieBracket
    (I := throatCoverModelWithCorners) (I' := 𝓘(Real, EuclideanR3))
    (n := ∞)
    (f := throatCoverRadialMap period hPeriod)
    (V := fun current => euclideanThroatRotationSection first current)
    (W := fun current => euclideanThroatRotationSection second current)
    (x₀ := point)
    ((euclideanThroatRotationSection first).contMDiff.mdifferentiableAt
      (by simp))
    ((euclideanThroatRotationSection second).contMDiff.mdifferentiableAt
      (by simp))
    ((throatCoverRadialMap_isLocalDiffeomorph period hPeriod)
      |>.contMDiff.contMDiffAt)
    hSmooth
  rw [← throatRadial_mpullback_rotation period hPeriod first,
    ← throatRadial_mpullback_rotation period hPeriod second,
    ← hNatural, euclideanThroatRotation_lieBracket]
  simp only [VectorField.mpullback_apply, Pi.smul_apply]
  rw [map_sum]
  congr 1
  funext output
  rw [map_smul]
  exact congrArg
    (fun vector => spatialRotationStructureConstant first second output • vector)
    (congrArg (fun field => field point)
      (throatRadial_mpullback_rotation period hPeriod output))

/-! ## Bracket closure on the actual quotient -/

/-- Intrinsic Lie bracket of smooth fixed-throat ghosts. -/
def throatGhostLieBracket
    (first second : CInfinityThroatGhost period hPeriod) :
    CInfinityThroatGhost period hPeriod where
  toFun := VectorField.mlieBracket throatCoverModelWithCorners first second
  contMDiff_toFun := by
    exact ContDiff.mlieBracket_vectorField
      (I := throatCoverModelWithCorners)
      (M := EffectiveThroat period hPeriod)
      (U := fun point => first point) (V := fun point => second point)
      (m := ⊤) (n := ⊤) first.contMDiff second.contMDiff (by
        rw [minSmoothness_of_isRCLikeNormedField]
        rfl)

@[simp]
theorem throatGhostLieBracket_apply
    (first second : CInfinityThroatGhost period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    throatGhostLieBracket period hPeriod first second point =
      VectorField.mlieBracket throatCoverModelWithCorners
        first second point :=
  rfl

private def throatProjection :
    EffectiveThroatCover period hPeriod → EffectiveThroat period hPeriod :=
  mappingTorusMk (throatData period hPeriod)

private theorem throatProjection_mfderiv_isInvertible
    (point : EffectiveThroatCover period hPeriod) :
    (mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
      (throatProjection period hPeriod) point).IsInvertible := by
  let derivativeEquiv :=
    (fixedThroat_projection_isLocalDiffeomorph period hPeriod)
      |>.mfderivToContinuousLinearEquiv (by simp) point
  unfold throatProjection
  rw [← IsLocalDiffeomorph.mfderivToContinuousLinearEquiv_coe
    (fixedThroat_projection_isLocalDiffeomorph period hPeriod)
      (by simp) point]
  exact ⟨derivativeEquiv, rfl⟩

private theorem throatProjection_mpullback_descended_rotation
    (axis : Fin 3) :
    VectorField.mpullback throatCoverModelWithCorners
        throatCoverModelWithCorners
        (throatProjection period hPeriod)
        (throatSpatialRotationGhost period hPeriod axis) =
      throatCoverSpatialRotationValue period hPeriod axis := by
  funext point
  unfold throatSpatialRotationGhost throatProjection
  rw [VectorField.mpullback_apply,
    descendSmoothDeckEquivariantThroatCoverGhost_mk]
  change (mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
      (throatProjection period hPeriod) point).inverse
        (mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
          (throatProjection period hPeriod) point
          (throatCoverSpatialRotationValue period hPeriod axis point)) = _
  exact (throatProjection_mfderiv_isInvertible period hPeriod point)
    |>.inverse_apply_self _

/-- The descended fixed-throat ghosts satisfy the exact full `so(3)` table. -/
theorem throatSpatialRotationGhost_bracket
    (first second : Fin 3) :
    throatGhostLieBracket period hPeriod
        (throatSpatialRotationGhost period hPeriod first)
        (throatSpatialRotationGhost period hPeriod second) =
      ∑ output : Fin 3,
        spatialRotationStructureConstant first second output •
          throatSpatialRotationGhost period hPeriod output := by
  apply ContMDiffSection.ext
  intro quotientPoint
  obtain ⟨point, rfl⟩ :=
    mappingTorusMk_surjective (throatData period hPeriod) quotientPoint
  let firstGhost := throatSpatialRotationGhost period hPeriod first
  let secondGhost := throatSpatialRotationGhost period hPeriod second
  have hProjection : ContMDiffAt throatCoverModelWithCorners
      throatCoverModelWithCorners ω
      (throatProjection period hPeriod) point := by
    simpa [throatProjection] using
      ((fixedThroat_projection_isLocalDiffeomorph period hPeriod)
        |>.contMDiff.contMDiffAt)
  have hNatural := VectorField.mpullback_mlieBracket
    (I := throatCoverModelWithCorners)
    (I' := throatCoverModelWithCorners)
    (n := ω)
    (f := throatProjection period hPeriod)
    (V := fun current => firstGhost current)
    (W := fun current => secondGhost current)
    (x₀ := point)
    (firstGhost.contMDiff.mdifferentiableAt (by simp))
    (secondGhost.contMDiff.mdifferentiableAt (by simp))
    hProjection
    (by simp)
  have hPullback :
      VectorField.mpullback throatCoverModelWithCorners
          throatCoverModelWithCorners
          (throatProjection period hPeriod)
          (VectorField.mlieBracket throatCoverModelWithCorners
            firstGhost secondGhost) point =
        VectorField.mpullback throatCoverModelWithCorners
          throatCoverModelWithCorners
          (throatProjection period hPeriod)
          (fun current => ∑ output : Fin 3,
            spatialRotationStructureConstant first second output •
              throatSpatialRotationGhost period hPeriod output current)
          point := by
    rw [hNatural,
      throatProjection_mpullback_descended_rotation,
      throatProjection_mpullback_descended_rotation,
      throatCoverSpatialRotation_lieBracket]
    simp only [VectorField.mpullback_apply, Pi.smul_apply]
    rw [map_sum]
    congr 1
    funext output
    rw [map_smul]
    exact congrArg
      (fun vector =>
        spatialRotationStructureConstant first second output • vector)
      (congrArg (fun field => field point)
        (throatProjection_mpullback_descended_rotation
          period hPeriod output)).symm
  exact (throatProjection_mfderiv_isInvertible period hPeriod point)
    |>.inverse.injective hPullback

/-! ## The scalar action and the isolated final Koszul contract -/

/-- Directional action of a genuine throat ghost on a smooth throat scalar. -/
def throatScalarLieDerivative
    (ghost : CInfinityThroatGhost period hPeriod)
    (scalar : ThroatScalar period hPeriod) :
    ThroatScalar period hPeriod :=
  ⟨fun point =>
      mvfderiv throatCoverModelWithCorners scalar point (ghost point),
    by
      have hEvaluation : ContMDiff throatCoverModelWithCorners.tangent
          (modelWithCornersSelf Real Real) ∞
          (fun vector : TangentBundle throatCoverModelWithCorners
              (EffectiveThroat period hPeriod) =>
            mvfderiv throatCoverModelWithCorners scalar vector.1 vector.2) := by
        have hDerivative :=
          (contMDiff_snd_tangentBundle_modelSpace Real
            (modelWithCornersSelf Real Real) (n := ∞)).comp
            (scalar.contMDiff.contMDiff_tangentMap (m := ∞) (by simp))
        convert hDerivative using 1
        funext vector
        rfl
      exact hEvaluation.comp ghost.contMDiff⟩

theorem throatScalarLieDerivative_addGhost
    (first second : CInfinityThroatGhost period hPeriod)
    (scalar : ThroatScalar period hPeriod) :
    throatScalarLieDerivative period hPeriod (first + second) scalar =
      throatScalarLieDerivative period hPeriod first scalar +
        throatScalarLieDerivative period hPeriod second scalar := by
  apply ContMDiffMap.ext
  intro point
  change mvfderiv throatCoverModelWithCorners scalar point
      (first point + second point) = _
  exact map_add _ _ _

theorem throatScalarLieDerivative_smulGhost
    (coefficient : Real)
    (ghost : CInfinityThroatGhost period hPeriod)
    (scalar : ThroatScalar period hPeriod) :
    throatScalarLieDerivative period hPeriod (coefficient • ghost) scalar =
      coefficient • throatScalarLieDerivative period hPeriod ghost scalar := by
  apply ContMDiffMap.ext
  intro point
  change mvfderiv throatCoverModelWithCorners scalar point
      (coefficient • ghost point) =
    coefficient • mvfderiv throatCoverModelWithCorners
      scalar point (ghost point)
  exact map_smul _ _ _

theorem throatScalarLieDerivative_addScalar
    (ghost : CInfinityThroatGhost period hPeriod)
    (first second : ThroatScalar period hPeriod) :
    throatScalarLieDerivative period hPeriod ghost (first + second) =
      throatScalarLieDerivative period hPeriod ghost first +
        throatScalarLieDerivative period hPeriod ghost second := by
  apply ContMDiffMap.ext
  intro point
  change mvfderiv throatCoverModelWithCorners
      ((first : EffectiveThroat period hPeriod → Real) +
        (second : EffectiveThroat period hPeriod → Real))
      point (ghost point) = _
  rw [mvfderiv_add
    (first.contMDiff.mdifferentiableAt (by simp))
    (second.contMDiff.mdifferentiableAt (by simp))]
  rfl

theorem throatScalarLieDerivative_smulScalar
    (ghost : CInfinityThroatGhost period hPeriod)
    (coefficient : Real) (scalar : ThroatScalar period hPeriod) :
    throatScalarLieDerivative period hPeriod ghost (coefficient • scalar) =
      coefficient • throatScalarLieDerivative period hPeriod ghost scalar := by
  apply ContMDiffMap.ext
  intro point
  have hConst : MDifferentiableAt throatCoverModelWithCorners
      (modelWithCornersSelf Real Real)
      (fun _ : EffectiveThroat period hPeriod => coefficient) point :=
    (contMDiff_const : ContMDiff throatCoverModelWithCorners
      (modelWithCornersSelf Real Real) ∞
      (fun _ : EffectiveThroat period hPeriod => coefficient))
      |>.mdifferentiableAt (by simp)
  change mvfderiv throatCoverModelWithCorners
      ((fun _ : EffectiveThroat period hPeriod => coefficient) *
        (scalar : EffectiveThroat period hPeriod → Real))
      point (ghost point) =
    coefficient * mvfderiv throatCoverModelWithCorners
      scalar point (ghost point)
  rw [mvfderiv_mul hConst
    (scalar.contMDiff.mdifferentiableAt (by simp)), mvfderiv_const]
  change coefficient * _ + _ * 0 = coefficient * _
  rw [mul_zero, add_zero]
  rfl

@[simp]
theorem throatScalarLieDerivative_one
    (ghost : CInfinityThroatGhost period hPeriod) :
    throatScalarLieDerivative period hPeriod ghost
        (1 : ThroatScalar period hPeriod) = 0 := by
  apply ContMDiffMap.ext
  intro point
  change mvfderiv throatCoverModelWithCorners
      (fun _ : EffectiveThroat period hPeriod => (1 : Real))
      point (ghost point) = 0
  rw [mvfderiv_const]
  rfl

/-- The throat scalar action, linear in both the ghost and scalar slots. -/
def throatScalarGhostAction :
    CInfinityThroatGhost period hPeriod →ₗ[Real]
      (ThroatScalar period hPeriod →ₗ[Real]
        ThroatScalar period hPeriod) where
  toFun ghost :=
    { toFun := throatScalarLieDerivative period hPeriod ghost
      map_add' := throatScalarLieDerivative_addScalar
        period hPeriod ghost
      map_smul' := throatScalarLieDerivative_smulScalar
        period hPeriod ghost }
  map_add' first second := by
    apply LinearMap.ext
    intro scalar
    exact throatScalarLieDerivative_addGhost
      period hPeriod first second scalar
  map_smul' coefficient ghost := by
    apply LinearMap.ext
    intro scalar
    exact throatScalarLieDerivative_smulGhost
      period hPeriod coefficient ghost scalar

private abbrev ThroatExteriorGhost :=
  Coefficient ⊗[Real] CInfinityThroatGhost period hPeriod

/-- Coefficient-linear action of exterior-valued throat ghosts. -/
def throatExteriorGhostScalarAction :
    ThroatExteriorGhost period hPeriod →ₗ[Real]
      ThroatTotal period hPeriod →ₗ[Real]
        ThroatTotal period hPeriod :=
  TensorProduct.map₂
    (LinearMap.mul Real Coefficient)
    (throatScalarGhostAction period hPeriod)

@[simp]
theorem throatExteriorGhostScalarAction_tmul
    (firstCoefficient secondCoefficient : Coefficient)
    (ghost : CInfinityThroatGhost period hPeriod)
    (scalar : ThroatScalar period hPeriod) :
    throatExteriorGhostScalarAction period hPeriod
        (firstCoefficient ⊗ₜ[Real] ghost)
        (secondCoefficient ⊗ₜ[Real] scalar) =
      (firstCoefficient * secondCoefficient) ⊗ₜ[Real]
        throatScalarLieDerivative period hPeriod ghost scalar :=
  rfl

/-- The universal odd throat rotation ghost. -/
def throatUniversalRotationGhost :
    ThroatExteriorGhost period hPeriod :=
  (oddGenerator 0) ⊗ₜ[Real] throatSpatialRotationGhost period hPeriod 0 +
    (oddGenerator 1) ⊗ₜ[Real] throatSpatialRotationGhost period hPeriod 1 +
    (oddGenerator 2) ⊗ₜ[Real] throatSpatialRotationGhost period hPeriod 2

/-- Candidate corrected throat differential `D_CE ⊗ id + c·∂`. -/
def throatCorrectedCombinedLinear :
    ThroatTotal period hPeriod →ₗ[Real] ThroatTotal period hPeriod :=
  TensorProduct.map spatialRotationKoszulDifferential
      (LinearMap.id : ThroatScalar period hPeriod →ₗ[Real]
        ThroatScalar period hPeriod) +
    throatExteriorGhostScalarAction period hPeriod
      (throatUniversalRotationGhost period hPeriod)

@[simp]
theorem throatCorrectedCombinedLinear_tmul
    (coefficient : Coefficient) (scalar : ThroatScalar period hPeriod) :
    throatCorrectedCombinedLinear period hPeriod
        (coefficient ⊗ₜ[Real] scalar) =
      spatialRotationKoszulDifferential coefficient ⊗ₜ[Real] scalar +
        (oddGenerator 0 * coefficient) ⊗ₜ[Real]
          throatScalarLieDerivative period hPeriod
            (throatSpatialRotationGhost period hPeriod 0) scalar +
        (oddGenerator 1 * coefficient) ⊗ₜ[Real]
          throatScalarLieDerivative period hPeriod
            (throatSpatialRotationGhost period hPeriod 1) scalar +
        (oddGenerator 2 * coefficient) ⊗ₜ[Real]
          throatScalarLieDerivative period hPeriod
            (throatSpatialRotationGhost period hPeriod 2) scalar := by
  simp [throatCorrectedCombinedLinear, throatUniversalRotationGhost,
    throatExteriorGhostScalarAction_tmul]
  abel

theorem throatCorrectedCombinedLinear_coefficient_rule
    (coefficient : Coefficient) :
    throatCorrectedCombinedLinear period hPeriod
        (coefficient ⊗ₜ[Real] (1 : ThroatScalar period hPeriod)) =
      ((unconditionalClosedThreeGeneratorGhostKoszulData period hPeriod)
          |>.coefficientDifferential coefficient) ⊗ₜ[Real]
        (1 : ThroatScalar period hPeriod) := by
  rw [throatCorrectedCombinedLinear_tmul]
  simp [throatScalarLieDerivative_one,
    unconditionalClosedThreeGeneratorGhostKoszulData,
    closedThreeGeneratorGhostKoszulData,
    unconditionalSpatialRotationKoszulCoefficientData,
    spatialRotationKoszulCoefficientData]

/-- Single exact residual contract: nilpotence of the now explicit corrected
Koszul map.  Geometry, bracket closure, and the LL action are unconditional. -/
structure ThroatCorrectedKoszulNilpotence where
  square_zero : ∀ element : ThroatTotal period hPeriod,
    throatCorrectedCombinedLinear period hPeriod
        (throatCorrectedCombinedLinear period hPeriod element) = 0

/-- Conditional completion of the existing LL API from the unique remaining
algebraic nilpotence contract. -/
def llThroatRotationBRSTCompletion
    (nilpotence : ThroatCorrectedKoszulNilpotence period hPeriod) :
    LLThroatBRSTCompletion period hPeriod where
  toLinearMap := throatCorrectedCombinedLinear period hPeriod
  coefficient_rule :=
    throatCorrectedCombinedLinear_coefficient_rule period hPeriod
  square_zero := nilpotence.square_zero

/-- The resulting componentwise action on the metric, measure, and LL-field
blocks, with no additional geometric hypothesis. -/
def correctedLLThroatRotationBRST
    (nilpotence : ThroatCorrectedKoszulNilpotence period hPeriod) :
    LLThroatLinearBRST period hPeriod →ₗ[Real]
      LLThroatLinearBRST period hPeriod :=
  correctedLLThroatLinearBRST period hPeriod
    (llThroatRotationBRSTCompletion period hPeriod nilpotence)

theorem correctedLLThroatRotationBRST_square_zero
    (nilpotence : ThroatCorrectedKoszulNilpotence period hPeriod)
    (fields : LLThroatLinearBRST period hPeriod) :
    correctedLLThroatRotationBRST period hPeriod nilpotence
        (correctedLLThroatRotationBRST period hPeriod nilpotence fields) = 0 :=
  correctedLLThroatLinearBRST_square_zero period hPeriod
    (llThroatRotationBRSTCompletion period hPeriod nilpotence) fields

end

end P0EFTJanusMappingTorusD8NonabelianGhostThroatBRST4D
end JanusFormal
