import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusD8NonabelianGhostTriple4D

/-!
# Unconditional bracket naturality for the D8 spatial rotations

Polar coordinates identify the sphere-times-real cover with punctured
Euclidean four-space.  The three cover rotations are therefore pullbacks of
the linear ambient rotations.  Lie-bracket naturality for local
diffeomorphisms first transports the explicit `so(3)` table to the cover and
then through the mapping-torus projection.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusD8NonabelianGhostBracketNaturality4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 800000

noncomputable section

open Set Topology TopologicalSpace
open scoped Manifold ContDiff BigOperators
open Bundle
open P0EFTJanusReflectionFixedThroat
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothDiffeomorphismGhostLieBracket4D
open P0EFTJanusMappingTorusD8NonabelianGhostTriple4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveCover := MappingTorusCover (sphereData period hPeriod)
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)
private abbrev EuclideanR4 := EuclideanSpace Real (Fin 4)

local instance effectiveCoverChartedSpace :
    ChartedSpace CoverModel (EffectiveCover period hPeriod) :=
  reflectedSphereCoverChartedSpace period hPeriod

local instance effectiveCoverIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveCover period hPeriod) :=
  reflectedSphereCover_isManifold period hPeriod

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

private def positiveReal : Opens Real := ⟨Ioi 0, isOpen_Ioi⟩

private def nonzeroEuclideanR4 : Opens EuclideanR4 :=
  ⟨({0}ᶜ : Set EuclideanR4), isOpen_compl_singleton⟩

private def sphereDiffeomorph :
    UnitThreeSphere ≃ₘ⟮(𝓡 3), (𝓡 3)⟯ StandardUnitThreeSphere where
  toEquiv := unitThreeSphereHomeomorph.toEquiv
  contMDiff_toFun := chartedSpacePullback_toFun_contMDiff (𝓡 3) ∞
    unitThreeSphereHomeomorph
  contMDiff_invFun := chartedSpacePullback_invFun_contMDiff (𝓡 3) ∞
    unitThreeSphereHomeomorph

private def coverDiffeomorphProd :
    EffectiveCover period hPeriod ≃ₘ⟮coverModelWithCorners,
      coverModelWithCorners⟯ (UnitThreeSphere × Real) where
  toEquiv := (coverHomeomorphProd (sphereData period hPeriod)).toEquiv
  contMDiff_toFun := chartedSpacePullback_toFun_contMDiff
    coverModelWithCorners ∞ (coverHomeomorphProd (sphereData period hPeriod))
  contMDiff_invFun := chartedSpacePullback_invFun_contMDiff
    coverModelWithCorners ∞ (coverHomeomorphProd (sphereData period hPeriod))

private def expToPositive (value : Real) : positiveReal :=
  ⟨Real.exp value, Real.exp_pos value⟩

private def positiveLog (value : positiveReal) : Real :=
  Real.log value

private theorem expToPositive_contMDiff :
    ContMDiff 𝓘(Real, Real) 𝓘(Real, Real) ∞ expToPositive := by
    rw [← ContMDiff.subtypeVal_comp_iff]
    simpa [expToPositive, Function.comp_def] using
      Real.contDiff_exp.contMDiff

private theorem positiveLog_contMDiff :
    ContMDiff 𝓘(Real, Real) 𝓘(Real, Real) ∞ positiveLog := by
  intro value
  change ContMDiffAt 𝓘(Real, Real) 𝓘(Real, Real) ∞
    (fun current : positiveReal => Real.log current) value
  rw [contMDiffAt_subtype_iff]
  exact (Real.contDiffAt_log.2 value.2.ne').contMDiffAt

private def expDiffeomorph :
    Real ≃ₘ⟮𝓘(Real, Real), 𝓘(Real, Real)⟯ positiveReal where
  toEquiv :=
    { toFun := expToPositive
      invFun := positiveLog
      left_inv := Real.log_exp
      right_inv := fun value => Subtype.ext (Real.exp_log value.2) }
  contMDiff_toFun := expToPositive_contMDiff
  contMDiff_invFun := positiveLog_contMDiff

private def normalizedNonzero
    (point : nonzeroEuclideanR4) : EuclideanR4 :=
  ‖(point : EuclideanR4)‖⁻¹ • (point : EuclideanR4)

private theorem normalizedNonzero_mem_sphere
    (point : nonzeroEuclideanR4) :
    normalizedNonzero point ∈ Metric.sphere (0 : EuclideanR4) 1 := by
  rw [Metric.mem_sphere, dist_zero_right, normalizedNonzero, norm_smul,
    Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _),
    inv_mul_cancel₀]
  exact norm_ne_zero_iff.mpr point.2

private theorem nonzero_norm_contMDiff :
    ContMDiff 𝓘(Real, EuclideanR4) 𝓘(Real, Real) ∞
      (fun point : nonzeroEuclideanR4 => ‖(point : EuclideanR4)‖) := by
  intro point
  rw [contMDiffAt_subtype_iff]
  exact (contDiffAt_norm Real point.2).contMDiffAt

private theorem normalizedNonzero_contMDiff :
    ContMDiff 𝓘(Real, EuclideanR4) 𝓘(Real, EuclideanR4) ∞
      normalizedNonzero := by
  exact (nonzero_norm_contMDiff.inv₀
      (fun point => norm_ne_zero_iff.mpr point.2)).smul
    contMDiff_subtype_val

private def normalizedNonzeroSphere
    (point : nonzeroEuclideanR4) : StandardUnitThreeSphere :=
  ⟨normalizedNonzero point, normalizedNonzero_mem_sphere point⟩

private theorem normalizedNonzeroSphere_contMDiff :
    ContMDiff 𝓘(Real, EuclideanR4) (𝓡 3) ∞
      normalizedNonzeroSphere :=
  normalizedNonzero_contMDiff.codRestrict_sphere
    normalizedNonzero_mem_sphere

private def nonzeroRadius
    (point : nonzeroEuclideanR4) : positiveReal :=
  ⟨‖(point : EuclideanR4)‖, norm_pos_iff.mpr point.2⟩

private theorem nonzeroRadius_contMDiff :
    ContMDiff 𝓘(Real, EuclideanR4) 𝓘(Real, Real) ∞
      nonzeroRadius := by
  rw [← ContMDiff.subtypeVal_comp_iff]
  exact nonzero_norm_contMDiff

private def radialDiffeomorph :
    (StandardUnitThreeSphere × positiveReal) ≃ₘ⟮
      coverModelWithCorners, 𝓘(Real, EuclideanR4)⟯
      nonzeroEuclideanR4 where
  toEquiv :=
    { toFun := fun point => (homeomorphUnitSphereProd EuclideanR4).symm point
      invFun := fun point => homeomorphUnitSphereProd EuclideanR4 point
      left_inv := fun point =>
        (homeomorphUnitSphereProd EuclideanR4).apply_symm_apply point
      right_inv := fun point =>
        (homeomorphUnitSphereProd EuclideanR4).symm_apply_apply point }
  contMDiff_toFun := by
    rw [← ContMDiff.subtypeVal_comp_iff]
    change ContMDiff coverModelWithCorners 𝓘(Real, EuclideanR4) ∞
      (fun point : StandardUnitThreeSphere × positiveReal =>
        (point.2 : Real) • (point.1 : EuclideanR4))
    exact (contMDiff_subtype_val.comp contMDiff_snd).smul
      (contMDiff_coe_sphere.comp contMDiff_fst)
  contMDiff_invFun := by
    refine (normalizedNonzeroSphere_contMDiff.prodMk
      nonzeroRadius_contMDiff).congr ?_
    intro point
    apply Prod.ext
    · apply Subtype.ext
      simp [normalizedNonzeroSphere, normalizedNonzero]
    · apply Subtype.ext
      simp [nonzeroRadius]

private def coverRadialDiffeomorph :
    EffectiveCover period hPeriod ≃ₘ⟮coverModelWithCorners,
      𝓘(Real, EuclideanR4)⟯ nonzeroEuclideanR4 :=
  (coverDiffeomorphProd period hPeriod).trans
    ((sphereDiffeomorph.prodCongr expDiffeomorph).trans radialDiffeomorph)

private def nonzeroDefault : nonzeroEuclideanR4 :=
  ⟨EuclideanSpace.single 0 1, by
    show EuclideanSpace.single (0 : Fin 4) (1 : Real) ≠ 0
    exact (EuclideanSpace.single_eq_zero_iff
      (i := (0 : Fin 4)) (a := (1 : Real))).not.mpr one_ne_zero⟩

private def nonzeroRetraction (point : EuclideanR4) : nonzeroEuclideanR4 :=
  if hPoint : point ≠ 0 then ⟨point, hPoint⟩ else nonzeroDefault

private def nonzeroInclusionPartialDiffeomorph :
    PartialDiffeomorph 𝓘(Real, EuclideanR4) 𝓘(Real, EuclideanR4)
      nonzeroEuclideanR4 EuclideanR4 ∞ where
  toPartialEquiv :=
    { toFun := Subtype.val
      invFun := nonzeroRetraction
      source := Set.univ
      target := ({0}ᶜ : Set EuclideanR4)
      map_source' := fun point _ => point.2
      map_target' := fun _ _ => Set.mem_univ _
      left_inv' := by
        intro point _
        have hPoint : (point : EuclideanR4) ≠ 0 := point.2
        simp [nonzeroRetraction, hPoint]
      right_inv' := by
        intro point hPoint
        have hPoint' : point ≠ 0 := by
          simpa only [mem_compl_iff, mem_singleton_iff] using hPoint
        simp [nonzeroRetraction, hPoint'] }
  open_source := isOpen_univ
  open_target := isOpen_compl_singleton
  contMDiffOn_toFun := contMDiff_subtype_val.contMDiffOn
  contMDiffOn_invFun := by
    intro point hPoint
    apply (ContMDiffWithinAt.subtypeVal_comp_iff
      nonzeroEuclideanR4 nonzeroRetraction ({0}ᶜ) point).mp
    exact contMDiffWithinAt_id.congr_of_mem (fun current hCurrent => by
      have hCurrent' : current ≠ 0 := by
        simpa only [mem_compl_iff, mem_singleton_iff] using hCurrent
      simp [nonzeroRetraction, hCurrent']) hPoint

private theorem nonzeroInclusion_isLocalDiffeomorph :
    IsLocalDiffeomorph 𝓘(Real, EuclideanR4) 𝓘(Real, EuclideanR4) ∞
      (Subtype.val : nonzeroEuclideanR4 → EuclideanR4) := by
  intro point
  exact PartialDiffeomorph.isLocalDiffeomorphAt
    (I := 𝓘(Real, EuclideanR4)) (J := 𝓘(Real, EuclideanR4))
    (n := ∞) nonzeroInclusionPartialDiffeomorph (Set.mem_univ point)

/-- Global polar coordinates on the sphere-times-real cover. -/
def coverRadialMap
    (point : EffectiveCover period hPeriod) : EuclideanR4 :=
  (coverRadialDiffeomorph period hPeriod point : nonzeroEuclideanR4)

@[simp]
theorem coverRadialMap_apply
    (point : EffectiveCover period hPeriod) :
    coverRadialMap period hPeriod point =
      Real.exp point.time •
        (EuclideanSpace.equiv (Fin 4) Real).symm point.fiber.1 := by
  rfl

theorem coverRadialMap_isLocalDiffeomorph :
    IsLocalDiffeomorph coverModelWithCorners 𝓘(Real, EuclideanR4) ∞
      (coverRadialMap period hPeriod) := by
  unfold coverRadialMap
  intro point
  exact IsLocalDiffeomorphAt.comp
    (I := coverModelWithCorners) (J := 𝓘(Real, EuclideanR4))
    (K := 𝓘(Real, EuclideanR4))
    (M := EffectiveCover period hPeriod) (N := nonzeroEuclideanR4)
    (P := EuclideanR4) (n := ∞)
    ((coverRadialDiffeomorph period hPeriod).isLocalDiffeomorph point)
    (nonzeroInclusion_isLocalDiffeomorph
      (coverRadialDiffeomorph period hPeriod point))

private def euclideanSpatialRotation (axis : Fin 3) :
    EuclideanR4 →L[Real] EuclideanR4 :=
  (EuclideanSpace.equiv (Fin 4) Real).symm.toContinuousLinearMap.comp
    ((ambientSpatialRotation axis).comp
      (EuclideanSpace.equiv (Fin 4) Real).toContinuousLinearMap)

private def euclideanSpatialRotationSection (axis : Fin 3) :
    ContMDiffSection 𝓘(Real, EuclideanR4) EuclideanR4 ∞
      (fun point : EuclideanR4 =>
        TangentSpace 𝓘(Real, EuclideanR4) point) where
  toFun := euclideanSpatialRotation axis
  contMDiff_toFun := by
    rw [contMDiff_vectorSpace_iff_contDiff]
    exact (euclideanSpatialRotation axis).contDiff

@[simp]
private theorem euclideanSpatialRotation_conjugates
    (axis : Fin 3) (point : EuclideanR4) :
    (EuclideanSpace.equiv (Fin 4) Real)
        (euclideanSpatialRotation axis point) =
      ambientSpatialRotation axis
        ((EuclideanSpace.equiv (Fin 4) Real) point) := by
  change WithLp.ofLp (WithLp.toLp 2
      (ambientSpatialRotation axis
        ((EuclideanSpace.equiv (Fin 4) Real) point))) = _
  rfl

private theorem euclideanSpatialRotation_lieBracket
    (first second : Fin 3) :
    VectorField.mlieBracket 𝓘(Real, EuclideanR4)
        (euclideanSpatialRotationSection first)
        (euclideanSpatialRotationSection second) =
      fun point => ∑ output : Fin 3,
        spatialRotationStructureConstant first second output •
          euclideanSpatialRotationSection output point := by
  rw [← VectorField.mlieBracketWithin_univ,
    VectorField.mlieBracketWithin_eq_lieBracketWithin,
    VectorField.lieBracketWithin_univ]
  funext point
  change VectorField.lieBracket Real
      (euclideanSpatialRotation first) (euclideanSpatialRotation second) point =
    ∑ output : Fin 3, spatialRotationStructureConstant first second output •
      euclideanSpatialRotation output point
  apply (EuclideanSpace.equiv (Fin 4) Real).injective
  have hAmbient := congrFun
    (ambientSpatialRotation_lieBracket first second)
    ((EuclideanSpace.equiv (Fin 4) Real) point)
  simpa only [euclideanSpatialRotationSection, VectorField.lieBracket,
    ContinuousLinearMap.fderiv, map_sub,
    euclideanSpatialRotation_conjugates, map_sum, map_smul] using hAmbient

private theorem coverRadialMap_comp_rotationCurve
    (axis : Fin 3) (point : EffectiveCover period hPeriod) :
    coverRadialMap period hPeriod ∘
        coverSpatialRotationCurve period hPeriod axis point =
      fun time => Real.exp point.time •
        (EuclideanSpace.equiv (Fin 4) Real).symm
          (ambientSpatialRotationFlow axis (time, point.fiber.1)) := by
  funext time
  rw [Function.comp_apply, coverRadialMap_apply]
  simp only [coverSpatialRotationCurve, coverSpatialRotationFlow]
  rw [sphereSpatialRotationFlow_coe]

private theorem coverRadialMap_mfderiv_rotation
    (axis : Fin 3) (point : EffectiveCover period hPeriod) :
    mfderiv coverModelWithCorners 𝓘(Real, EuclideanR4)
        (coverRadialMap period hPeriod) point
        (coverSpatialRotationValue period hPeriod axis point) =
      euclideanSpatialRotation axis (coverRadialMap period hPeriod point) := by
  rw [coverSpatialRotationValue_eq_curve_mfderiv]
  have hRadialAt : MDifferentiableAt coverModelWithCorners
      𝓘(Real, EuclideanR4) (coverRadialMap period hPeriod) point :=
    (coverRadialMap_isLocalDiffeomorph period hPeriod point).mdifferentiableAt
      (by simp)
  have hCurveAt : MDifferentiableAt 𝓘(Real, Real)
      coverModelWithCorners
      (coverSpatialRotationCurve period hPeriod axis point) 0 :=
    (coverSpatialRotationCurve_contMDiff period hPeriod axis point)
      |>.mdifferentiableAt (by simp)
  have hCurveZero :
      coverSpatialRotationCurve period hPeriod axis point 0 = point := by
    exact coverSpatialRotationFlow_zero period hPeriod axis point
  have hComp := mfderiv_comp_apply_of_eq
    (I := 𝓘(Real, Real)) (I' := coverModelWithCorners)
    (I'' := 𝓘(Real, EuclideanR4))
    (f := coverSpatialRotationCurve period hPeriod axis point)
    (g := coverRadialMap period hPeriod)
    (x := (0 : Real)) (y := point)
    hRadialAt hCurveAt hCurveZero (1 : Real)
  have hEuclidean : HasDerivAt
      (fun time => (EuclideanSpace.equiv (Fin 4) Real).symm
        (ambientSpatialRotationFlow axis (time, point.fiber.1)))
      ((EuclideanSpace.equiv (Fin 4) Real).symm
        (ambientSpatialRotation axis point.fiber.1)) 0 :=
    (EuclideanSpace.equiv (Fin 4) Real).symm.hasFDerivAt.comp_hasDerivAt
      0 (ambientSpatialRotationFlow_hasDerivAt_zero axis point.fiber.1)
  have hDerivative : HasDerivAt
      (fun time => Real.exp point.time •
        (EuclideanSpace.equiv (Fin 4) Real).symm
          (ambientSpatialRotationFlow axis (time, point.fiber.1)))
      (Real.exp point.time •
        (EuclideanSpace.equiv (Fin 4) Real).symm
          (ambientSpatialRotation axis point.fiber.1)) 0 := by
    exact hEuclidean.const_smul (Real.exp point.time)
  calc
    _ = mfderiv 𝓘(Real, Real) 𝓘(Real, EuclideanR4)
        (coverRadialMap period hPeriod ∘
          coverSpatialRotationCurve period hPeriod axis point) 0 1 :=
      hComp.symm
    _ = Real.exp point.time •
        (EuclideanSpace.equiv (Fin 4) Real).symm
          (ambientSpatialRotation axis point.fiber.1) := by
      rw [coverRadialMap_comp_rotationCurve, mfderiv_eq_fderiv]
      exact hDerivative.deriv
    _ = _ := by
      rw [coverRadialMap_apply]
      apply (EuclideanSpace.equiv (Fin 4) Real).injective
      simp only [map_smul, euclideanSpatialRotation_conjugates,
        ContinuousLinearEquiv.apply_symm_apply]

private theorem radial_mfderiv_isInvertible
    (point : EffectiveCover period hPeriod) :
    (mfderiv coverModelWithCorners 𝓘(Real, EuclideanR4)
      (coverRadialMap period hPeriod) point).IsInvertible := by
  let derivativeEquiv :=
    (coverRadialMap_isLocalDiffeomorph period hPeriod)
      |>.mfderivToContinuousLinearEquiv (by simp) point
  rw [← IsLocalDiffeomorph.mfderivToContinuousLinearEquiv_coe
    (coverRadialMap_isLocalDiffeomorph period hPeriod) (by simp) point]
  exact ⟨derivativeEquiv, rfl⟩

private theorem radial_mpullback_rotation
    (axis : Fin 3) :
    VectorField.mpullback coverModelWithCorners 𝓘(Real, EuclideanR4)
        (coverRadialMap period hPeriod)
        (euclideanSpatialRotationSection axis) =
      coverSpatialRotationValue period hPeriod axis := by
  funext point
  rw [VectorField.mpullback_apply,
    (radial_mfderiv_isInvertible period hPeriod point).inverse_apply_eq]
  exact (coverRadialMap_mfderiv_rotation period hPeriod axis point).symm

private theorem coverSpatialRotation_lieBracket
    (first second : Fin 3) :
    VectorField.mlieBracket coverModelWithCorners
        (coverSpatialRotationValue period hPeriod first)
        (coverSpatialRotationValue period hPeriod second) =
      fun point => ∑ output : Fin 3,
        spatialRotationStructureConstant first second output •
          coverSpatialRotationValue period hPeriod output point := by
  funext point
  have hSmooth : minSmoothness Real 2 ≤ (∞ : ℕ∞ω) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    change ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
    exact WithTop.coe_le_coe.mpr le_top
  have hNatural := VectorField.mpullback_mlieBracket
    (I := coverModelWithCorners) (I' := 𝓘(Real, EuclideanR4))
    (n := ∞)
    (f := coverRadialMap period hPeriod)
    (V := fun point => euclideanSpatialRotationSection first point)
    (W := fun point => euclideanSpatialRotationSection second point)
    (x₀ := point)
    ((euclideanSpatialRotationSection first).contMDiff.mdifferentiableAt
      (by simp))
    ((euclideanSpatialRotationSection second).contMDiff.mdifferentiableAt
      (by simp))
    ((coverRadialMap_isLocalDiffeomorph period hPeriod).contMDiff.contMDiffAt)
    hSmooth
  rw [← radial_mpullback_rotation period hPeriod first,
    ← radial_mpullback_rotation period hPeriod second,
    ← hNatural, euclideanSpatialRotation_lieBracket]
  simp only [VectorField.mpullback_apply, Pi.smul_apply]
  rw [map_sum]
  congr 1
  funext output
  rw [map_smul]
  exact congrArg
    (fun vector => spatialRotationStructureConstant first second output • vector)
    (congrArg (fun field => field point)
      (radial_mpullback_rotation period hPeriod output))

private def projection :
    EffectiveCover period hPeriod → EffectiveQuotient period hPeriod :=
  mappingTorusMk (sphereData period hPeriod)

private theorem projection_mfderiv_isInvertible
    (point : EffectiveCover period hPeriod) :
    (mfderiv coverModelWithCorners coverModelWithCorners
      (projection period hPeriod) point).IsInvertible := by
  let derivativeEquiv :=
    (reflectedSphere_projection_isLocalDiffeomorph period hPeriod)
      |>.mfderivToContinuousLinearEquiv (by simp) point
  unfold projection
  rw [← IsLocalDiffeomorph.mfderivToContinuousLinearEquiv_coe
    (reflectedSphere_projection_isLocalDiffeomorph period hPeriod)
      (by simp) point]
  exact ⟨derivativeEquiv, rfl⟩

private theorem projection_mpullback_descended_rotation
    (axis : Fin 3) :
    VectorField.mpullback coverModelWithCorners coverModelWithCorners
        (projection period hPeriod)
        (descendSmoothDeckEquivariantCoverGhost period hPeriod
          (smoothDeckEquivariantCoverSpatialRotation period hPeriod axis)) =
      coverSpatialRotationValue period hPeriod axis := by
  funext point
  unfold projection
  rw [VectorField.mpullback_apply,
    descendSmoothDeckEquivariantCoverGhost_mk]
  change (mfderiv coverModelWithCorners coverModelWithCorners
      (projection period hPeriod) point).inverse
        (mfderiv coverModelWithCorners coverModelWithCorners
          (projection period hPeriod) point
          (coverSpatialRotationValue period hPeriod axis point)) = _
  exact (projection_mfderiv_isInvertible period hPeriod point)
    |>.inverse_apply_self _

/-- The last conditional geometric bridge in the previous gate is proved by
two applications of local-diffeomorphism bracket naturality. -/
theorem descendedSpatialRotationBracketNaturality :
    DescendedSpatialRotationBracketNaturality period hPeriod := by
  intro first second
  apply ContMDiffSection.ext
  intro quotientPoint
  obtain ⟨point, rfl⟩ :=
    mappingTorusMk_surjective (sphereData period hPeriod) quotientPoint
  let firstGhost := descendSmoothDeckEquivariantCoverGhost period hPeriod
    (smoothDeckEquivariantCoverSpatialRotation period hPeriod first)
  let secondGhost := descendSmoothDeckEquivariantCoverGhost period hPeriod
    (smoothDeckEquivariantCoverSpatialRotation period hPeriod second)
  have hProjection : ContMDiffAt coverModelWithCorners coverModelWithCorners ω
      (projection period hPeriod) point := by
    simpa [projection] using
      ((reflectedSphere_projection_isLocalDiffeomorph period hPeriod)
        |>.contMDiff.contMDiffAt)
  have hNatural := VectorField.mpullback_mlieBracket
    (I := coverModelWithCorners) (I' := coverModelWithCorners)
    (n := ω)
    (f := projection period hPeriod)
    (V := fun current => firstGhost current)
    (W := fun current => secondGhost current)
    (x₀ := point)
    (firstGhost.contMDiff.mdifferentiableAt (by simp))
    (secondGhost.contMDiff.mdifferentiableAt (by simp))
    hProjection
    (by simp)
  have hPullback :
      VectorField.mpullback coverModelWithCorners coverModelWithCorners
          (projection period hPeriod)
          (VectorField.mlieBracket coverModelWithCorners firstGhost secondGhost)
          point =
        VectorField.mpullback coverModelWithCorners coverModelWithCorners
          (projection period hPeriod)
          (fun current => ∑ output : Fin 3,
            spatialRotationStructureConstant first second output •
              descendSmoothDeckEquivariantCoverGhost period hPeriod
                (smoothDeckEquivariantCoverSpatialRotation
                  period hPeriod output) current) point := by
    rw [hNatural, projection_mpullback_descended_rotation,
      projection_mpullback_descended_rotation,
      coverSpatialRotation_lieBracket]
    simp only [VectorField.mpullback_apply, Pi.smul_apply]
    rw [map_sum]
    congr 1
    funext output
    rw [map_smul]
    exact congrArg
      (fun vector => spatialRotationStructureConstant first second output • vector)
      (congrArg (fun field => field point)
        (projection_mpullback_descended_rotation
          period hPeriod output)).symm
  exact (projection_mfderiv_isInvertible period hPeriod point).inverse.injective
    hPullback

/-- Explicit cover realization with no bracket hypothesis. -/
def unconditionalD8SpatialRotationCoverRealization :
    D8SpatialRotationCoverRealization period hPeriod :=
  explicitD8SpatialRotationCoverRealization period hPeriod
    (descendedSpatialRotationBracketNaturality period hPeriod)

/-- Explicit quotient `so(3)` ghost triple with no geometric hypothesis. -/
def unconditionalD8SpatialRotationGhostRealization :
    D8SpatialRotationGhostRealization period hPeriod :=
  (unconditionalD8SpatialRotationCoverRealization period hPeriod)
    |>.toGhostRealization

/-- The unconditional quotient rotation triple is genuinely nonabelian. -/
theorem unconditionalD8SpatialRotationGhostRealization_nonabelian :
    smoothGhostLieBracket period hPeriod
        ((unconditionalD8SpatialRotationGhostRealization period hPeriod).ghosts 0)
        ((unconditionalD8SpatialRotationGhostRealization period hPeriod).ghosts 1) ≠ 0 :=
  (unconditionalD8SpatialRotationGhostRealization period hPeriod).nonabelian

end

end P0EFTJanusMappingTorusD8NonabelianGhostBracketNaturality4D
end JanusFormal
