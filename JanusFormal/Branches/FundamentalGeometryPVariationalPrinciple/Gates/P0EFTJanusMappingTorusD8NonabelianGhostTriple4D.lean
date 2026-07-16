import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusThreeGeneratorGlobalKoszulBRST4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntrinsicLorentzMetricDescent4D

/-!
# Concrete nonabelian D8 ghost triple frontier

The three ambient linear fields below rotate the spatial coordinates
`1,2,3`.  They are tangent to the unit three-sphere, commute with the D8 deck
reflection of coordinate `0`, and satisfy the exact `so(3)` bracket table.

The only geometric datum still isolated here is the standard naturality
bridge which turns these related ambient fields into smooth tangent sections
of the mapping-torus quotient and transports their bracket.  The independent
coefficient-side Chevalley--Eilenberg derivation is kept as a second explicit
input before constructing `ClosedThreeGeneratorGhostKoszulData`.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusD8NonabelianGhostTriple4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff BigOperators
open Bundle
open P0EFTJanusReflectionFixedThroat
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothDiffeomorphismGhostLieBracket4D
open P0EFTJanusMappingTorusExteriorDiffeomorphismGhostBRST4D
open P0EFTJanusMappingTorusThreeGeneratorScalarBRST4D
open P0EFTJanusMappingTorusThreeGeneratorGlobalKoszulBRST4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveCover := MappingTorusCover (sphereData period hPeriod)
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)
private abbrev Ghost := CInfinityDiffeomorphismGhost period hPeriod
private abbrev Coefficient := GhostCoefficientExterior

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

private abbrev CoverTangent (point : EffectiveCover period hPeriod) :=
  TangentSpace coverModelWithCorners point

/-- A genuine smooth tangent section upstairs. -/
abbrev CInfinityCoverGhost :=
  ContMDiffSection coverModelWithCorners CoverCoordinates ∞
    (fun point : EffectiveCover period hPeriod =>
      CoverTangent period hPeriod point)

/-- Smooth cover ghost with the exact derivative equivariance required by
the integer deck action. -/
structure SmoothDeckEquivariantCoverGhost where
  field : CInfinityCoverGhost period hPeriod
  deck_equivariant : ∀ (winding : Int) (point : EffectiveCover period hPeriod),
    field (winding +ᵥ point) =
      mfderiv coverModelWithCorners coverModelWithCorners
        (winding +ᵥ ·) point (field point)

@[ext]
theorem SmoothDeckEquivariantCoverGhost.ext
    {first second : SmoothDeckEquivariantCoverGhost period hPeriod}
    (hField : first.field = second.field) : first = second := by
  cases first
  cases second
  cases hField
  rfl

/-- Derivative equivalence of the actual analytic quotient projection. -/
private def projectionDerivativeEquiv
    (point : EffectiveCover period hPeriod) :
    CoverTangent period hPeriod point ≃L[Real]
      TangentSpace coverModelWithCorners
        (mappingTorusMk (sphereData period hPeriod) point) :=
  (reflectedSphere_projection_isLocalDiffeomorph period hPeriod)
    |>.mfderivToContinuousLinearEquiv (by simp) point

@[simp]
private theorem projectionDerivativeEquiv_coe
    (point : EffectiveCover period hPeriod) :
    (projectionDerivativeEquiv period hPeriod point :
      CoverTangent period hPeriod point →L[Real]
        TangentSpace coverModelWithCorners
          (mappingTorusMk (sphereData period hPeriod) point)) =
      mfderiv coverModelWithCorners coverModelWithCorners
        (mappingTorusMk (sphereData period hPeriod)) point :=
  IsLocalDiffeomorph.mfderivToContinuousLinearEquiv_coe
    (reflectedSphere_projection_isLocalDiffeomorph period hPeriod)
      (by simp) point

private def projectedCoverGhostValue
    (ghost : SmoothDeckEquivariantCoverGhost period hPeriod)
    (point : EffectiveCover period hPeriod) :
    TangentSpace coverModelWithCorners
      (mappingTorusMk (sphereData period hPeriod) point) :=
  projectionDerivativeEquiv period hPeriod point (ghost.field point)

/-- Deck-equivariant smooth tangent fields descend as genuine dependent
vector fields; the heterogeneous recursor accounts for the changing fiber. -/
private def descendedCoverGhostValue
    (ghost : SmoothDeckEquivariantCoverGhost period hPeriod) :
    ∀ point : EffectiveQuotient period hPeriod,
      TangentSpace coverModelWithCorners point :=
  fun quotientPoint =>
    Quotient.hrecOn quotientPoint
      (projectedCoverGhostValue period hPeriod ghost)
      (fun firstPoint secondPoint hOrbit => by
        have hProjection :
            mappingTorusMk (sphereData period hPeriod) firstPoint =
              mappingTorusMk (sphereData period hPeriod) secondPoint :=
          Quotient.sound hOrbit
        obtain ⟨winding, hWinding⟩ :=
          (mappingTorusMk_eq_iff_exists_vadd
            (sphereData period hPeriod) firstPoint secondPoint).1 hProjection
        subst firstPoint
        clear hOrbit
        have hTangent :
            TangentSpace coverModelWithCorners
                (mappingTorusMk (sphereData period hPeriod)
                  (winding +ᵥ secondPoint)) =
              TangentSpace coverModelWithCorners
                (mappingTorusMk (sphereData period hPeriod) secondPoint) :=
          congrArg (TangentSpace coverModelWithCorners) hProjection
        cases hTangent
        apply heq_of_eq
        have hNatural (vector : CoverTangent period hPeriod secondPoint) :
            mfderiv coverModelWithCorners coverModelWithCorners
                (mappingTorusMk (sphereData period hPeriod))
                (winding +ᵥ secondPoint)
                (mfderiv coverModelWithCorners coverModelWithCorners
                  (winding +ᵥ ·) secondPoint vector) =
              mfderiv coverModelWithCorners coverModelWithCorners
                (mappingTorusMk (sphereData period hPeriod))
                secondPoint vector := by
          have hProjectionAt : MDifferentiableAt coverModelWithCorners
              coverModelWithCorners
              (mappingTorusMk (sphereData period hPeriod))
              (winding +ᵥ secondPoint) :=
            (reflectedSphere_projection_isLocalDiffeomorph period hPeriod)
              |>.contMDiff.mdifferentiableAt (by simp)
          have hDeckAt : MDifferentiableAt coverModelWithCorners
              coverModelWithCorners (winding +ᵥ ·) secondPoint :=
            (reflectedSphereCover_deck_contMDiff period hPeriod winding)
              |>.mdifferentiableAt (by simp)
          have hComposite := mfderiv_comp secondPoint hProjectionAt hDeckAt
          have hMap :
              (mappingTorusMk (sphereData period hPeriod)) ∘
                  (winding +ᵥ ·) =
                mappingTorusMk (sphereData period hPeriod) := by
            funext point
            exact (mappingTorusMk_eq_iff_exists_vadd
              (sphereData period hPeriod) _ _).2 ⟨winding, rfl⟩
          calc
            _ = mfderiv coverModelWithCorners coverModelWithCorners
                  ((mappingTorusMk (sphereData period hPeriod)) ∘
                    (winding +ᵥ ·)) secondPoint vector := by
              rw [hComposite]
              rfl
            _ = _ := by rw [hMap]
        change projectionDerivativeEquiv period hPeriod
              (winding +ᵥ secondPoint) (ghost.field (winding +ᵥ secondPoint)) =
            projectionDerivativeEquiv period hPeriod secondPoint
              (ghost.field secondPoint)
        rw [ghost.deck_equivariant]
        change mfderiv coverModelWithCorners coverModelWithCorners
              (mappingTorusMk (sphereData period hPeriod))
              (winding +ᵥ secondPoint)
              (mfderiv coverModelWithCorners coverModelWithCorners
                (winding +ᵥ ·) secondPoint (ghost.field secondPoint)) = _
        exact hNatural (ghost.field secondPoint))

@[simp]
private theorem descendedCoverGhostValue_mk
    (ghost : SmoothDeckEquivariantCoverGhost period hPeriod)
    (point : EffectiveCover period hPeriod) :
    descendedCoverGhostValue period hPeriod ghost
        (mappingTorusMk (sphereData period hPeriod) point) =
      projectedCoverGhostValue period hPeriod ghost point :=
  rfl

/-- Generic smooth descent of deck-equivariant tangent sections. -/
def descendSmoothDeckEquivariantCoverGhost
    (ghost : SmoothDeckEquivariantCoverGhost period hPeriod) :
    Ghost period hPeriod where
  toFun := descendedCoverGhostValue period hPeriod ghost
  contMDiff_toFun := by
    intro quotientPoint
    obtain ⟨anchor, rfl⟩ :=
      mappingTorusMk_surjective (sphereData period hPeriod) quotientPoint
    let projection := mappingTorusMk (sphereData period hPeriod)
    let hAt := reflectedSphere_projection_isLocalDiffeomorph
      period hPeriod anchor
    have hLocalInverse : ContMDiffAt coverModelWithCorners
        coverModelWithCorners ∞ hAt.localInverse (projection anchor) :=
      hAt.localInverse_contMDiffAt.of_le (by simp)
    have hFieldLocal := ghost.field.contMDiff.contMDiffAt.comp
      (projection anchor) hLocalInverse
    have hProjectionSmooth : ContMDiff coverModelWithCorners
        coverModelWithCorners ∞ projection :=
      (reflectedSphere_projection_isLocalDiffeomorph period hPeriod).contMDiff
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
      (⟨current, descendedCoverGhostValue period hPeriod ghost current⟩ :
          TangentBundle coverModelWithCorners
            (EffectiveQuotient period hPeriod)) =
          ⟨projection (hAt.localInverse current),
            descendedCoverGhostValue period hPeriod ghost
              (projection (hAt.localInverse current))⟩ :=
        congrArg (fun point =>
          (⟨point, descendedCoverGhostValue period hPeriod ghost point⟩ :
            TangentBundle coverModelWithCorners
              (EffectiveQuotient period hPeriod))) hRight.symm
      _ = (tangentMap coverModelWithCorners coverModelWithCorners projection ∘
            (fun point =>
              (⟨point, ghost.field point⟩ :
                TangentBundle coverModelWithCorners
                  (EffectiveCover period hPeriod))) ∘
            hAt.localInverse) current := by
        apply TotalSpace.ext rfl
        simp

@[simp]
theorem descendSmoothDeckEquivariantCoverGhost_mk
    (ghost : SmoothDeckEquivariantCoverGhost period hPeriod)
    (point : EffectiveCover period hPeriod) :
    descendSmoothDeckEquivariantCoverGhost period hPeriod ghost
        (mappingTorusMk (sphereData period hPeriod) point) =
      projectionDerivativeEquiv period hPeriod point (ghost.field point) :=
  rfl

/-- No information is lost when a deck-equivariant tangent section is
descended through the local-diffeomorphism quotient. -/
theorem descendSmoothDeckEquivariantCoverGhost_injective :
    Function.Injective
      (descendSmoothDeckEquivariantCoverGhost period hPeriod) := by
  intro first second hEqual
  apply SmoothDeckEquivariantCoverGhost.ext period hPeriod
  apply ContMDiffSection.ext
  intro point
  have hAt := DFunLike.congr_fun hEqual
    (mappingTorusMk (sphereData period hPeriod) point)
  change projectionDerivativeEquiv period hPeriod point (first.field point) =
    projectionDerivativeEquiv period hPeriod point (second.field point) at hAt
  exact (projectionDerivativeEquiv period hPeriod point).injective hAt

/-- Zero deck-equivariant cover ghost. -/
def zeroSmoothDeckEquivariantCoverGhost :
    SmoothDeckEquivariantCoverGhost period hPeriod where
  field := 0
  deck_equivariant := by simp

@[simp]
theorem descendSmoothDeckEquivariantCoverGhost_zero :
    descendSmoothDeckEquivariantCoverGhost period hPeriod
        (zeroSmoothDeckEquivariantCoverGhost period hPeriod) = 0 := by
  apply ContMDiffSection.ext
  intro quotientPoint
  obtain ⟨point, rfl⟩ :=
    mappingTorusMk_surjective (sphereData period hPeriod) quotientPoint
  simp [zeroSmoothDeckEquivariantCoverGhost]

/-- Rotation about spatial coordinate `1`. -/
private def rotationOneLinear : R4Point →ₗ[Real] R4Point where
  toFun point := ![0, 0, -point 3, point 2]
  map_add' first second := by
    funext index
    fin_cases index <;> simp <;> abel
  map_smul' scalar point := by
    funext index
    fin_cases index <;> simp

/-- Rotation about spatial coordinate `2`. -/
private def rotationTwoLinear : R4Point →ₗ[Real] R4Point where
  toFun point := ![0, point 3, 0, -point 1]
  map_add' first second := by
    funext index
    fin_cases index <;> simp <;> abel
  map_smul' scalar point := by
    funext index
    fin_cases index <;> simp

/-- Rotation about spatial coordinate `3`. -/
private def rotationThreeLinear : R4Point →ₗ[Real] R4Point where
  toFun point := ![0, -point 2, point 1, 0]
  map_add' first second := by
    funext index
    fin_cases index <;> simp <;> abel
  map_smul' scalar point := by
    funext index
    fin_cases index <;> simp

/-- The concrete three-dimensional ambient rotation family. -/
def ambientSpatialRotation (axis : Fin 3) : R4Point →L[Real] R4Point :=
  (![rotationOneLinear, rotationTwoLinear, rotationThreeLinear] axis)
    |>.toContinuousLinearMap

/-- Structure constants for Mathlib's convention
`[V,W] = DW(V) - DV(W)`.  They are minus the usual epsilon tensor for the
chosen `eᵢ × x` generators. -/
def spatialRotationStructureConstant
    (first second output : Fin 3) : Real :=
  ![
    ![![0, 0, 0], ![0, 0, -1], ![0, 1, 0]],
    ![![0, 0, 1], ![0, 0, 0], ![-1, 0, 0]],
    ![![0, -1, 0], ![1, 0, 0], ![0, 0, 0]]
  ] first second output

theorem ambientSpatialRotation_contDiff (axis : Fin 3) :
    ContDiff Real ω (ambientSpatialRotation axis) :=
  (ambientSpatialRotation axis).contDiff

/-- Each generator is pointwise orthogonal to the radius, hence tangent to
the ambient algebraic unit three-sphere. -/
theorem ambientSpatialRotation_tangent
    (axis : Fin 3) (point : R4Point) :
    ∑ index : Fin 4, point index * ambientSpatialRotation axis point index = 0 := by
  fin_cases axis <;>
    simp [ambientSpatialRotation, rotationOneLinear, rotationTwoLinear,
      rotationThreeLinear, Fin.sum_univ_succ] <;> ring

/-- The rotations preserve the reflected coordinate and commute exactly with
the ambient deck reflection. -/
theorem ambientSpatialRotation_reflection_commutes
    (axis : Fin 3) (point : R4Point) :
    reflectPoint (ambientSpatialRotation axis point) =
      ambientSpatialRotation axis (reflectPoint point) := by
  fin_cases axis
  all_goals
    funext index
    fin_cases index <;>
      simp [ambientSpatialRotation, rotationOneLinear, rotationTwoLinear,
        rotationThreeLinear, reflectPoint]

/-- The ordinary normed-space Lie bracket is the exact finite `so(3)` table. -/
theorem ambientSpatialRotation_lieBracket
    (first second : Fin 3) :
    VectorField.lieBracket Real
        (ambientSpatialRotation first) (ambientSpatialRotation second) =
      fun point => ∑ output : Fin 3,
        spatialRotationStructureConstant first second output •
          ambientSpatialRotation output point := by
  funext point
  simp only [VectorField.lieBracket, ContinuousLinearMap.fderiv]
  fin_cases first <;> fin_cases second <;>
    funext index <;> fin_cases index <;>
    simp [ambientSpatialRotation,
      rotationOneLinear, rotationTwoLinear, rotationThreeLinear,
      spatialRotationStructureConstant, Fin.sum_univ_succ]

/-- The ambient algebra is genuinely nonabelian. -/
theorem ambientSpatialRotation_nonabelian :
    VectorField.lieBracket Real
        (ambientSpatialRotation 0) (ambientSpatialRotation 1) ≠ 0 := by
  rw [ambientSpatialRotation_lieBracket]
  intro hZero
  have hPoint := congrFun hZero (![0, 1, 0, 0] : R4Point)
  have hCoordinate := congrFun hPoint (2 : Fin 4)
  simp [ambientSpatialRotation, rotationOneLinear, rotationTwoLinear,
    rotationThreeLinear, spatialRotationStructureConstant,
    Fin.sum_univ_succ] at hCoordinate

/-! ## Smooth rotation sections on the cover -/

/-- The complete one-parameter rotations whose infinitesimal generators are
`ambientSpatialRotation`. -/
def ambientSpatialRotationFlow
    (axis : Fin 3) (input : Real × R4Point) : R4Point :=
  match axis with
  | 0 => ![input.2 0, input.2 1,
      Real.cos input.1 * input.2 2 - Real.sin input.1 * input.2 3,
      Real.sin input.1 * input.2 2 + Real.cos input.1 * input.2 3]
  | 1 => ![input.2 0,
      Real.cos input.1 * input.2 1 + Real.sin input.1 * input.2 3,
      input.2 2,
      -Real.sin input.1 * input.2 1 + Real.cos input.1 * input.2 3]
  | 2 => ![input.2 0,
      Real.cos input.1 * input.2 1 - Real.sin input.1 * input.2 2,
      Real.sin input.1 * input.2 1 + Real.cos input.1 * input.2 2,
      input.2 3]

@[simp]
theorem ambientSpatialRotationFlow_zero
    (axis : Fin 3) (point : R4Point) :
    ambientSpatialRotationFlow axis (0, point) = point := by
  fin_cases axis <;> ext index <;> fin_cases index <;>
    simp [ambientSpatialRotationFlow]

theorem ambientSpatialRotationFlow_contDiff (axis : Fin 3) :
    ContDiff Real ∞ (ambientSpatialRotationFlow axis) := by
  rw [contDiff_pi]
  intro index
  fin_cases axis <;> fin_cases index <;>
    simp [ambientSpatialRotationFlow] <;>
    fun_prop

theorem ambientSpatialRotationFlow_preserves_radius
    (axis : Fin 3) (input : Real × R4Point) :
    radiusSquared (ambientSpatialRotationFlow axis input) =
      radiusSquared input.2 := by
  fin_cases axis <;>
    simp [ambientSpatialRotationFlow, radiusSquared, Fin.sum_univ_succ] <;>
    nlinarith [Real.sin_sq_add_cos_sq input.1]

theorem ambientSpatialRotationFlow_reflection_commutes
    (axis : Fin 3) (input : Real × R4Point) :
    reflectPoint (ambientSpatialRotationFlow axis input) =
      ambientSpatialRotationFlow axis (input.1, reflectPoint input.2) := by
  fin_cases axis <;> ext index <;> fin_cases index <;>
    simp [ambientSpatialRotationFlow, reflectPoint]

theorem ambientSpatialRotationFlow_hasDerivAt_zero
    (axis : Fin 3) (point : R4Point) :
    HasDerivAt
      (fun time : Real => ambientSpatialRotationFlow axis (time, point))
      (ambientSpatialRotation axis point) 0 := by
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
  rw [hasDerivAt_pi]
  intro index
  fin_cases axis
  · fin_cases index
    · simpa [ambientSpatialRotationFlow, ambientSpatialRotation,
        rotationOneLinear] using (hasDerivAt_const (x := (0 : Real)) (c := point 0))
    · simpa [ambientSpatialRotationFlow, ambientSpatialRotation,
        rotationOneLinear] using (hasDerivAt_const (x := (0 : Real)) (c := point 1))
    · simpa [ambientSpatialRotationFlow, ambientSpatialRotation,
        rotationOneLinear] using hCosSubSin (point 2) (point 3)
    · simpa [ambientSpatialRotationFlow, ambientSpatialRotation,
        rotationOneLinear] using hSinAddCos (point 2) (point 3)
  · fin_cases index
    · simpa [ambientSpatialRotationFlow, ambientSpatialRotation,
        rotationTwoLinear] using (hasDerivAt_const (x := (0 : Real)) (c := point 0))
    · simpa [ambientSpatialRotationFlow, ambientSpatialRotation,
        rotationTwoLinear] using hCosAddSin (point 1) (point 3)
    · simpa [ambientSpatialRotationFlow, ambientSpatialRotation,
        rotationTwoLinear] using (hasDerivAt_const (x := (0 : Real)) (c := point 2))
    · simpa [ambientSpatialRotationFlow, ambientSpatialRotation,
        rotationTwoLinear] using hNegSinAddCos (point 1) (point 3)
  · fin_cases index
    · simpa [ambientSpatialRotationFlow, ambientSpatialRotation,
        rotationThreeLinear] using (hasDerivAt_const (x := (0 : Real)) (c := point 0))
    · simpa [ambientSpatialRotationFlow, ambientSpatialRotation,
        rotationThreeLinear] using hCosSubSin (point 1) (point 2)
    · simpa [ambientSpatialRotationFlow, ambientSpatialRotation,
        rotationThreeLinear] using hSinAddCos (point 1) (point 2)
    · simpa [ambientSpatialRotationFlow, ambientSpatialRotation,
        rotationThreeLinear] using (hasDerivAt_const (x := (0 : Real)) (c := point 3))

theorem ambientSpatialRotationFlow_deriv_zero
    (axis : Fin 3) (point : R4Point) :
    deriv (fun time : Real => ambientSpatialRotationFlow axis (time, point)) 0 =
      ambientSpatialRotation axis point :=
  (ambientSpatialRotationFlow_hasDerivAt_zero axis point).deriv

private def euclideanSpatialRotationFlow
    (axis : Fin 3) (input : Real × EuclideanR4) : EuclideanR4 :=
  (EuclideanSpace.equiv (Fin 4) Real).symm
    (ambientSpatialRotationFlow axis
      (input.1, EuclideanSpace.equiv (Fin 4) Real input.2))

private theorem euclideanSpatialRotationFlow_contDiff (axis : Fin 3) :
    ContDiff Real ∞ (euclideanSpatialRotationFlow axis) := by
  exact (EuclideanSpace.equiv (Fin 4) Real).symm.contDiff.comp
    ((ambientSpatialRotationFlow_contDiff axis).comp
      (contDiff_fst.prodMk
        ((EuclideanSpace.equiv (Fin 4) Real).contDiff.comp contDiff_snd)))

private theorem euclideanSpatialRotationFlow_mem_sphere
    (axis : Fin 3) (input : Real × StandardUnitThreeSphere) :
    euclideanSpatialRotationFlow axis (input.1, input.2.1) ∈
      Metric.sphere (0 : EuclideanR4) 1 := by
  rw [Metric.mem_sphere, dist_zero_right]
  have hNorm : ‖input.2.1‖ = 1 := by
    simpa [Metric.mem_sphere, dist_zero_right] using input.2.2
  have hSquare :
      ‖euclideanSpatialRotationFlow axis (input.1, input.2.1)‖ ^ 2 = 1 := by
    rw [euclideanSpatialRotationFlow,
      euclidean_norm_sq_eq_radiusSquared,
      ambientSpatialRotationFlow_preserves_radius,
      ← euclidean_norm_sq_eq_radiusSquared]
    simp [hNorm]
  nlinarith [norm_nonneg
    (euclideanSpatialRotationFlow axis (input.1, input.2.1))]

private def standardSphereSpatialRotationFlow
    (axis : Fin 3) (input : Real × StandardUnitThreeSphere) :
    StandardUnitThreeSphere :=
  ⟨euclideanSpatialRotationFlow axis (input.1, input.2.1),
    euclideanSpatialRotationFlow_mem_sphere axis input⟩

private theorem standardSphereSpatialRotationFlow_contMDiff
    (axis : Fin 3) :
    ContMDiff (𝓘(Real, Real).prod (𝓡 3)) (𝓡 3) ∞
      (standardSphereSpatialRotationFlow axis) := by
  letI : Fact (Module.finrank Real EuclideanR4 = 3 + 1) := ⟨by simp⟩
  apply ContMDiff.codRestrict_sphere
  exact (euclideanSpatialRotationFlow_contDiff axis).comp_contMDiff
    (contMDiff_fst.prodMk_space (contMDiff_coe_sphere.comp contMDiff_snd))

/-- Actual analytic sphere rotation in the transported Janus atlas. -/
def sphereSpatialRotationFlow
    (axis : Fin 3) (input : Real × UnitThreeSphere) : UnitThreeSphere :=
  unitThreeSphereHomeomorph.symm
    (standardSphereSpatialRotationFlow axis
      (input.1, unitThreeSphereHomeomorph input.2))

theorem sphereSpatialRotationFlow_contMDiff (axis : Fin 3) :
    ContMDiff (𝓘(Real, Real).prod (𝓡 3)) (𝓡 3) ∞
      (sphereSpatialRotationFlow axis) := by
  have hTo := chartedSpacePullback_toFun_contMDiff (𝓡 3) ∞
    unitThreeSphereHomeomorph
  have hInv := chartedSpacePullback_invFun_contMDiff (𝓡 3) ∞
    unitThreeSphereHomeomorph
  exact hInv.comp ((standardSphereSpatialRotationFlow_contMDiff axis).comp
    (contMDiff_fst.prodMk (hTo.comp contMDiff_snd)))

@[simp]
theorem sphereSpatialRotationFlow_zero
    (axis : Fin 3) (point : UnitThreeSphere) :
    sphereSpatialRotationFlow axis (0, point) = point := by
  apply unitThreeSphereHomeomorph.injective
  apply Subtype.ext
  apply (EuclideanSpace.equiv (Fin 4) Real).injective
  simpa [sphereSpatialRotationFlow, standardSphereSpatialRotationFlow,
    euclideanSpatialRotationFlow]

@[simp]
theorem sphereSpatialRotationFlow_coe
    (axis : Fin 3) (input : Real × UnitThreeSphere) :
    (sphereSpatialRotationFlow axis input).1 =
      ambientSpatialRotationFlow axis (input.1, input.2.1) := by
  change WithLp.ofLp
      (WithLp.toLp 2
        (ambientSpatialRotationFlow axis
          (input.1, WithLp.ofLp (WithLp.toLp 2 input.2.1)))) = _
  rw [WithLp.ofLp_toLp, WithLp.ofLp_toLp]

theorem sphereSpatialRotationFlow_reflection_commutes
    (axis : Fin 3) (input : Real × UnitThreeSphere) :
    sphereReflection (sphereSpatialRotationFlow axis input) =
      sphereSpatialRotationFlow axis (input.1, sphereReflection input.2) := by
  apply Subtype.ext
  change reflectPoint (sphereSpatialRotationFlow axis input).1 =
    (sphereSpatialRotationFlow axis
      (input.1, sphereReflection input.2)).1
  rw [sphereSpatialRotationFlow_coe, sphereSpatialRotationFlow_coe]
  exact ambientSpatialRotationFlow_reflection_commutes axis
    (input.1, input.2.1)

theorem sphereSpatialRotationFlow_reflection_zpow_commutes
    (axis : Fin 3) (winding : Int) (input : Real × UnitThreeSphere) :
    (sphereReflection ^ winding) (sphereSpatialRotationFlow axis input) =
      sphereSpatialRotationFlow axis
        (input.1, (sphereReflection ^ winding) input.2) := by
  induction winding using Int.induction_on generalizing input with
  | zero => simp
  | succ winding ih =>
      rw [zpow_add_one]
      change (sphereReflection ^ winding)
          (sphereReflection (sphereSpatialRotationFlow axis input)) =
        sphereSpatialRotationFlow axis
          (input.1, (sphereReflection ^ winding)
            (sphereReflection input.2))
      rw [sphereSpatialRotationFlow_reflection_commutes]
      simpa using ih (input.1, sphereReflection input.2)
  | pred winding ih =>
      rw [zpow_sub_one]
      have hInverse (point : UnitThreeSphere) :
          sphereReflection⁻¹ point = sphereReflection point := by
        rfl
      change (sphereReflection ^ (-(winding : Int)))
          (sphereReflection⁻¹ (sphereSpatialRotationFlow axis input)) =
        sphereSpatialRotationFlow axis
          (input.1, (sphereReflection ^ (-(winding : Int)))
            (sphereReflection⁻¹ input.2))
      rw [hInverse, hInverse,
        sphereSpatialRotationFlow_reflection_commutes]
      exact ih (input.1, sphereReflection input.2)

/-- Rotation of the sphere factor, leaving mapping-torus time fixed. -/
def coverSpatialRotationFlow
    (axis : Fin 3) (input : Real × EffectiveCover period hPeriod) :
    EffectiveCover period hPeriod :=
  ⟨sphereSpatialRotationFlow axis (input.1, input.2.fiber), input.2.time⟩

@[simp]
theorem coverSpatialRotationFlow_zero
    (axis : Fin 3) (point : EffectiveCover period hPeriod) :
    coverSpatialRotationFlow period hPeriod axis (0, point) = point := by
  apply MappingTorusCover.ext
  · simp [coverSpatialRotationFlow]
  · rfl

theorem coverSpatialRotationFlow_deck_commutes
    (axis : Fin 3) (winding : Int)
    (input : Real × EffectiveCover period hPeriod) :
    winding +ᵥ coverSpatialRotationFlow period hPeriod axis input =
      coverSpatialRotationFlow period hPeriod axis
        (input.1, winding +ᵥ input.2) := by
  apply MappingTorusCover.ext
  · exact sphereSpatialRotationFlow_reflection_zpow_commutes
      axis winding (input.1, input.2.fiber)
  · simp [coverSpatialRotationFlow]

theorem coverSpatialRotationFlow_contMDiff (axis : Fin 3) :
    ContMDiff (𝓘(Real, Real).prod coverModelWithCorners)
      coverModelWithCorners ∞
      (coverSpatialRotationFlow period hPeriod axis) := by
  let productEquiv := coverHomeomorphProd (sphereData period hPeriod)
  have hTo := chartedSpacePullback_toFun_contMDiff coverModelWithCorners ∞
    productEquiv
  have hInv := chartedSpacePullback_invFun_contMDiff coverModelWithCorners ∞
    productEquiv
  have hFiber : ContMDiff coverModelWithCorners (𝓡 3) ∞
      (fun point : EffectiveCover period hPeriod => point.fiber) :=
    contMDiff_fst.comp hTo
  have hTime : ContMDiff coverModelWithCorners 𝓘(Real, Real) ∞
      (fun point : EffectiveCover period hPeriod => point.time) :=
    contMDiff_snd.comp hTo
  have hSphere := (sphereSpatialRotationFlow_contMDiff axis).comp
    (contMDiff_fst.prodMk (hFiber.comp contMDiff_snd))
  have hProduct := hSphere.prodMk (hTime.comp contMDiff_snd)
  exact hInv.comp hProduct

private def sphereAmbientPoint (point : UnitThreeSphere) : R4Point :=
  point.1

private theorem sphereAmbientPoint_contMDiff :
    ContMDiff (𝓡 3) 𝓘(Real, R4Point) ∞ sphereAmbientPoint := by
  have hTo := chartedSpacePullback_toFun_contMDiff (𝓡 3) ∞
    unitThreeSphereHomeomorph
  have hStandard : ContMDiff (𝓡 3) 𝓘(Real, R4Point) ∞
      (fun point : StandardUnitThreeSphere =>
        EuclideanSpace.equiv (Fin 4) Real point.1) :=
    (EuclideanSpace.equiv (Fin 4) Real).toContinuousLinearMap.contMDiff.comp
      contMDiff_coe_sphere
  exact (hStandard.comp hTo).congr fun point => by
    change WithLp.ofLp (WithLp.toLp 2 point.1) = point.1
    rfl

private def coverAmbientPoint
    (point : EffectiveCover period hPeriod) : R4Point :=
  point.fiber.1

private theorem coverAmbientPoint_contMDiff :
    ContMDiff coverModelWithCorners 𝓘(Real, R4Point) ∞
      (coverAmbientPoint period hPeriod) := by
  let productEquiv := coverHomeomorphProd (sphereData period hPeriod)
  have hTo := chartedSpacePullback_toFun_contMDiff coverModelWithCorners ∞
    productEquiv
  have hFiber : ContMDiff coverModelWithCorners (𝓡 3) ∞
      (fun point : EffectiveCover period hPeriod => point.fiber) :=
    contMDiff_fst.comp hTo
  exact sphereAmbientPoint_contMDiff.comp hFiber

private def rotationFlowInputBundle
    (point : EffectiveCover period hPeriod) :
    TangentBundle (𝓘(Real, Real).prod coverModelWithCorners)
      (Real × EffectiveCover period hPeriod) :=
  (equivTangentBundleProd 𝓘(Real, Real) Real coverModelWithCorners
      (EffectiveCover period hPeriod)).symm
    (⟨0, 1⟩, ⟨point, 0⟩)

@[simp]
private theorem rotationFlowInputBundle_eq
    (point : EffectiveCover period hPeriod) :
    rotationFlowInputBundle period hPeriod point =
      (⟨(0, point), (1, 0)⟩ :
        TangentBundle (𝓘(Real, Real).prod coverModelWithCorners)
          (Real × EffectiveCover period hPeriod)) :=
  rfl

private theorem rotationFlowInputBundle_contMDiff :
    ContMDiff coverModelWithCorners
      (𝓘(Real, Real).prod coverModelWithCorners).tangent ∞
      (rotationFlowInputBundle period hPeriod) := by
  apply (contMDiff_equivTangentBundleProd_symm
    (I := 𝓘(Real, Real)) (I' := coverModelWithCorners)
    (M := Real) (M' := EffectiveCover period hPeriod)).comp
  exact contMDiff_const.prodMk
    ((Bundle.contMDiff_zeroSection Real
      (TangentSpace coverModelWithCorners :
        EffectiveCover period hPeriod → Type _)).of_le le_top)

private def rawCoverSpatialRotationBundle
    (axis : Fin 3) (point : EffectiveCover period hPeriod) :
    TangentBundle coverModelWithCorners (EffectiveCover period hPeriod) :=
  tangentMap (𝓘(Real, Real).prod coverModelWithCorners)
    coverModelWithCorners (coverSpatialRotationFlow period hPeriod axis)
    (rotationFlowInputBundle period hPeriod point)

private theorem rawCoverSpatialRotationBundle_contMDiff (axis : Fin 3) :
    ContMDiff coverModelWithCorners coverModelWithCorners.tangent ∞
      (rawCoverSpatialRotationBundle period hPeriod axis) :=
  ((coverSpatialRotationFlow_contMDiff period hPeriod axis)
      |>.contMDiff_tangentMap (m := ∞) (by simp)).comp
    (rotationFlowInputBundle_contMDiff period hPeriod)

private theorem rawCoverSpatialRotationBundle_base
    (axis : Fin 3) (point : EffectiveCover period hPeriod) :
    (rawCoverSpatialRotationBundle period hPeriod axis point).1 = point := by
  exact coverSpatialRotationFlow_zero period hPeriod axis point

/-- Intrinsic cover tangent generated by the explicit ambient rotation. -/
def coverSpatialRotationValue
    (axis : Fin 3) (point : EffectiveCover period hPeriod) :
    CoverTangent period hPeriod point :=
  (rawCoverSpatialRotationBundle_base period hPeriod axis point) ▸
    (rawCoverSpatialRotationBundle period hPeriod axis point).2

private theorem coverSpatialRotationValue_bundle
    (axis : Fin 3) (point : EffectiveCover period hPeriod) :
    (⟨point, coverSpatialRotationValue period hPeriod axis point⟩ :
        TangentBundle coverModelWithCorners (EffectiveCover period hPeriod)) =
      rawCoverSpatialRotationBundle period hPeriod axis point := by
  let raw := rawCoverSpatialRotationBundle period hPeriod axis point
  have hBase : raw.1 = point :=
    rawCoverSpatialRotationBundle_base period hPeriod axis point
  change (⟨point, hBase ▸ raw.2⟩ :
      TangentBundle coverModelWithCorners (EffectiveCover period hPeriod)) = raw
  rcases raw with ⟨base, vector⟩
  simp only at hBase
  subst base
  rfl

/-- The three ambient rotations are genuine smooth tangent sections upstairs. -/
def coverSpatialRotationSection (axis : Fin 3) :
    CInfinityCoverGhost period hPeriod where
  toFun := coverSpatialRotationValue period hPeriod axis
  contMDiff_toFun :=
    (rawCoverSpatialRotationBundle_contMDiff period hPeriod axis).congr
      (fun point =>
        coverSpatialRotationValue_bundle period hPeriod axis point)

private def coverSpatialRotationCurve
    (axis : Fin 3) (point : EffectiveCover period hPeriod) (time : Real) :
    EffectiveCover period hPeriod :=
  coverSpatialRotationFlow period hPeriod axis (time, point)

private theorem coverSpatialRotationCurve_contMDiff
    (axis : Fin 3) (point : EffectiveCover period hPeriod) :
    ContMDiff 𝓘(Real, Real) coverModelWithCorners ∞
      (coverSpatialRotationCurve period hPeriod axis point) :=
  (coverSpatialRotationFlow_contMDiff period hPeriod axis).comp
    (contMDiff_id.prodMk contMDiff_const)

private theorem rawCoverSpatialRotationBundle_eq_curve
    (axis : Fin 3) (point : EffectiveCover period hPeriod) :
    rawCoverSpatialRotationBundle period hPeriod axis point =
      tangentMap 𝓘(Real, Real) coverModelWithCorners
        (coverSpatialRotationCurve period hPeriod axis point)
        (⟨0, 1⟩ : TangentBundle 𝓘(Real, Real) Real) := by
  let slice : Real → Real × EffectiveCover period hPeriod :=
    fun time => (time, point)
  have hFlowAt : MDifferentiableAt
      (𝓘(Real, Real).prod coverModelWithCorners) coverModelWithCorners
      (coverSpatialRotationFlow period hPeriod axis) (0, point) :=
    (coverSpatialRotationFlow_contMDiff period hPeriod axis)
      |>.mdifferentiableAt (by simp)
  have hSliceAt : MDifferentiableAt 𝓘(Real, Real)
      (𝓘(Real, Real).prod coverModelWithCorners) slice 0 :=
    mdifferentiableAt_id.prodMk mdifferentiableAt_const
  have hComp := tangentMap_comp_at
    (I := 𝓘(Real, Real))
    (I' := 𝓘(Real, Real).prod coverModelWithCorners)
    (I'' := coverModelWithCorners)
    (f := slice)
    (g := coverSpatialRotationFlow period hPeriod axis)
    (⟨0, 1⟩ : TangentBundle 𝓘(Real, Real) Real)
    hFlowAt hSliceAt
  rw [tangentMap_prod_left] at hComp
  change tangentMap 𝓘(Real, Real) coverModelWithCorners
      (coverSpatialRotationCurve period hPeriod axis point)
      (⟨0, 1⟩ : TangentBundle 𝓘(Real, Real) Real) =
    rawCoverSpatialRotationBundle period hPeriod axis point at hComp
  exact hComp.symm

private theorem coverSpatialRotationValue_eq_curve_mfderiv
    (axis : Fin 3) (point : EffectiveCover period hPeriod) :
    coverSpatialRotationValue period hPeriod axis point =
      mfderiv 𝓘(Real, Real) coverModelWithCorners
        (coverSpatialRotationCurve period hPeriod axis point) 0 1 := by
  apply (TotalSpace.mk_injective
    (F := CoverCoordinates) (b := point))
  calc
    (⟨point, coverSpatialRotationValue period hPeriod axis point⟩ :
        TangentBundle coverModelWithCorners (EffectiveCover period hPeriod)) =
      rawCoverSpatialRotationBundle period hPeriod axis point :=
        coverSpatialRotationValue_bundle period hPeriod axis point
    _ = tangentMap 𝓘(Real, Real) coverModelWithCorners
        (coverSpatialRotationCurve period hPeriod axis point)
        (⟨0, 1⟩ : TangentBundle 𝓘(Real, Real) Real) :=
      rawCoverSpatialRotationBundle_eq_curve period hPeriod axis point
    _ = (⟨point,
          mfderiv 𝓘(Real, Real) coverModelWithCorners
            (coverSpatialRotationCurve period hPeriod axis point) 0 1⟩ :
        TangentBundle coverModelWithCorners
          (EffectiveCover period hPeriod)) := by
      simp [tangentMap, coverSpatialRotationCurve]
      exact HEq.rfl

/-- Applying the ambient sphere inclusion to the intrinsic cover section
recovers exactly the prescribed linear rotation generator. -/
theorem coverAmbientPoint_mfderiv_coverSpatialRotationValue
    (axis : Fin 3) (point : EffectiveCover period hPeriod) :
    mfderiv coverModelWithCorners 𝓘(Real, R4Point)
        (coverAmbientPoint period hPeriod) point
        (coverSpatialRotationValue period hPeriod axis point) =
      ambientSpatialRotation axis point.fiber.1 := by
  rw [coverSpatialRotationValue_eq_curve_mfderiv]
  have hCurveZero :
      coverSpatialRotationCurve period hPeriod axis point 0 = point := by
    simp [coverSpatialRotationCurve]
  have hAmbientAt : MDifferentiableAt coverModelWithCorners
      𝓘(Real, R4Point) (coverAmbientPoint period hPeriod) point :=
    (coverAmbientPoint_contMDiff period hPeriod)
      |>.mdifferentiableAt (by simp)
  have hCurveAt : MDifferentiableAt 𝓘(Real, Real)
      coverModelWithCorners
      (coverSpatialRotationCurve period hPeriod axis point) 0 :=
    (coverSpatialRotationCurve_contMDiff period hPeriod axis point)
      |>.mdifferentiableAt (by simp)
  have hComp := mfderiv_comp_apply_of_eq
    (I := 𝓘(Real, Real)) (I' := coverModelWithCorners)
    (I'' := 𝓘(Real, R4Point))
    (f := coverSpatialRotationCurve period hPeriod axis point)
    (g := coverAmbientPoint period hPeriod)
    (x := (0 : Real)) (y := point)
    hAmbientAt hCurveAt hCurveZero (1 : Real)
  have hFunction :
      (coverAmbientPoint period hPeriod) ∘
          (coverSpatialRotationCurve period hPeriod axis point) =
        fun time : Real =>
          ambientSpatialRotationFlow axis (time, point.fiber.1) := by
    funext time
    exact sphereSpatialRotationFlow_coe axis (time, point.fiber)
  calc
    _ = mfderiv 𝓘(Real, Real) 𝓘(Real, R4Point)
        ((coverAmbientPoint period hPeriod) ∘
          (coverSpatialRotationCurve period hPeriod axis point)) 0 1 :=
      hComp.symm
    _ = ambientSpatialRotation axis point.fiber.1 := by
      rw [hFunction, mfderiv_eq_fderiv]
      exact ambientSpatialRotationFlow_deriv_zero axis point.fiber.1

private theorem coverSpatialRotationCurve_deck
    (axis : Fin 3) (winding : Int)
    (point : EffectiveCover period hPeriod) :
    coverSpatialRotationCurve period hPeriod axis (winding +ᵥ point) =
      (winding +ᵥ ·) ∘
        coverSpatialRotationCurve period hPeriod axis point := by
  funext time
  exact (coverSpatialRotationFlow_deck_commutes
    period hPeriod axis winding (time, point)).symm

private theorem rawCoverSpatialRotationBundle_deck
    (axis : Fin 3) (winding : Int)
    (point : EffectiveCover period hPeriod) :
    rawCoverSpatialRotationBundle period hPeriod axis (winding +ᵥ point) =
      tangentMap coverModelWithCorners coverModelWithCorners
        (winding +ᵥ ·)
        (rawCoverSpatialRotationBundle period hPeriod axis point) := by
  rw [rawCoverSpatialRotationBundle_eq_curve,
    rawCoverSpatialRotationBundle_eq_curve,
    coverSpatialRotationCurve_deck]
  exact tangentMap_comp_at
    (I := 𝓘(Real, Real)) (I' := coverModelWithCorners)
    (I'' := coverModelWithCorners)
    (f := coverSpatialRotationCurve period hPeriod axis point)
    (g := (winding +ᵥ ·))
    (⟨0, 1⟩ : TangentBundle 𝓘(Real, Real) Real)
    ((reflectedSphereCover_deck_contMDiff period hPeriod winding)
      |>.mdifferentiableAt (by simp))
    ((coverSpatialRotationCurve_contMDiff period hPeriod axis point)
      |>.mdifferentiableAt (by simp))

theorem coverSpatialRotationValue_deck_equivariant
    (axis : Fin 3) (winding : Int)
    (point : EffectiveCover period hPeriod) :
    coverSpatialRotationValue period hPeriod axis (winding +ᵥ point) =
      mfderiv coverModelWithCorners coverModelWithCorners
        (winding +ᵥ ·) point
        (coverSpatialRotationValue period hPeriod axis point) := by
  have hTotal :
      (⟨winding +ᵥ point,
          coverSpatialRotationValue period hPeriod axis (winding +ᵥ point)⟩ :
        TangentBundle coverModelWithCorners (EffectiveCover period hPeriod)) =
      tangentMap coverModelWithCorners coverModelWithCorners
        (winding +ᵥ ·)
        (⟨point, coverSpatialRotationValue period hPeriod axis point⟩ :
          TangentBundle coverModelWithCorners
            (EffectiveCover period hPeriod)) := by
    calc
      _ = rawCoverSpatialRotationBundle period hPeriod axis
          (winding +ᵥ point) :=
        coverSpatialRotationValue_bundle period hPeriod axis _
      _ = tangentMap coverModelWithCorners coverModelWithCorners
          (winding +ᵥ ·)
          (rawCoverSpatialRotationBundle period hPeriod axis point) :=
        rawCoverSpatialRotationBundle_deck period hPeriod axis winding point
      _ = _ := congrArg
        (tangentMap coverModelWithCorners coverModelWithCorners
          (winding +ᵥ ·))
        (coverSpatialRotationValue_bundle period hPeriod axis point).symm
  apply (TotalSpace.mk_injective
    (F := CoverCoordinates) (b := winding +ᵥ point))
  simpa [tangentMap] using hTotal

/-- The explicit rotation sections satisfy the exact derivative cocycle for
every integer deck transformation. -/
def smoothDeckEquivariantCoverSpatialRotation (axis : Fin 3) :
    SmoothDeckEquivariantCoverGhost period hPeriod where
  field := coverSpatialRotationSection period hPeriod axis
  deck_equivariant :=
    coverSpatialRotationValue_deck_equivariant period hPeriod axis

private def spatialAxisOneSphere : UnitThreeSphere :=
  ⟨![0, 1, 0, 0], by
    norm_num [OnUnitThreeSphere, radiusSquared, Fin.sum_univ_succ]⟩

private def spatialAxisOneCover : EffectiveCover period hPeriod :=
  ⟨spatialAxisOneSphere, 0⟩

private theorem coverSpatialRotationValue_injective_at_axisOne :
    Function.Injective (fun axis : Fin 3 =>
      coverSpatialRotationValue period hPeriod axis
        (spatialAxisOneCover period hPeriod)) := by
  intro first second hEqual
  have hAmbient :
      ambientSpatialRotation first spatialAxisOneSphere.1 =
        ambientSpatialRotation second spatialAxisOneSphere.1 := by
    have hMapped := congrArg
      (mfderiv coverModelWithCorners 𝓘(Real, R4Point)
        (coverAmbientPoint period hPeriod)
        (spatialAxisOneCover period hPeriod)) hEqual
    rw [coverAmbientPoint_mfderiv_coverSpatialRotationValue,
      coverAmbientPoint_mfderiv_coverSpatialRotationValue] at hMapped
    have hMapped' := congrArg
      (NormedSpace.fromTangentSpace
        (coverAmbientPoint period hPeriod
          (spatialAxisOneCover period hPeriod))) hMapped
    change ambientSpatialRotation first spatialAxisOneSphere.1 =
      ambientSpatialRotation second spatialAxisOneSphere.1 at hMapped'
    exact hMapped'
  fin_cases first <;> fin_cases second <;> try rfl
  all_goals
    have hTwo := congrFun hAmbient (2 : Fin 4)
    have hThree := congrFun hAmbient (3 : Fin 4)
    simp [ambientSpatialRotation, rotationOneLinear, rotationTwoLinear,
      rotationThreeLinear, spatialAxisOneSphere] at hTwo hThree

private def rotationNonzeroSphere (axis : Fin 3) : UnitThreeSphere :=
  match axis with
  | 0 => ⟨![0, 0, 1, 0], by
      norm_num [OnUnitThreeSphere, radiusSquared, Fin.sum_univ_succ]⟩
  | 1 => spatialAxisOneSphere
  | 2 => spatialAxisOneSphere

private def rotationNonzeroCover
    (axis : Fin 3) : EffectiveCover period hPeriod :=
  ⟨rotationNonzeroSphere axis, 0⟩

private theorem ambientSpatialRotation_nonzero_at_witness (axis : Fin 3) :
    ambientSpatialRotation axis (rotationNonzeroSphere axis).1 ≠ 0 := by
  fin_cases axis
  · intro hZero
    have hCoordinate := congrFun hZero (3 : Fin 4)
    simp [ambientSpatialRotation, rotationOneLinear,
      rotationNonzeroSphere] at hCoordinate
  · intro hZero
    have hCoordinate := congrFun hZero (3 : Fin 4)
    simp [ambientSpatialRotation, rotationTwoLinear,
      rotationNonzeroSphere, spatialAxisOneSphere] at hCoordinate
  · intro hZero
    have hCoordinate := congrFun hZero (2 : Fin 4)
    simp [ambientSpatialRotation, rotationThreeLinear,
      rotationNonzeroSphere, spatialAxisOneSphere] at hCoordinate

private theorem coverSpatialRotationValue_nonzero_at_witness (axis : Fin 3) :
    coverSpatialRotationValue period hPeriod axis
        (rotationNonzeroCover period hPeriod axis) ≠ 0 := by
  intro hZero
  have hMapped := congrArg
    (mfderiv coverModelWithCorners 𝓘(Real, R4Point)
      (coverAmbientPoint period hPeriod)
      (rotationNonzeroCover period hPeriod axis)) hZero
  rw [coverAmbientPoint_mfderiv_coverSpatialRotationValue] at hMapped
  simp at hMapped
  exact ambientSpatialRotation_nonzero_at_witness axis hMapped

theorem smoothDeckEquivariantCoverSpatialRotation_faithful :
    Function.Injective
      (smoothDeckEquivariantCoverSpatialRotation period hPeriod) := by
  intro first second hEqual
  apply coverSpatialRotationValue_injective_at_axisOne period hPeriod
  have hField := congrArg SmoothDeckEquivariantCoverGhost.field hEqual
  exact DFunLike.congr_fun hField (spatialAxisOneCover period hPeriod)

theorem smoothDeckEquivariantCoverSpatialRotation_nonzero (axis : Fin 3) :
    smoothDeckEquivariantCoverSpatialRotation period hPeriod axis ≠
      zeroSmoothDeckEquivariantCoverGhost period hPeriod := by
  intro hZero
  have hField := congrArg SmoothDeckEquivariantCoverGhost.field hZero
  have hAt := DFunLike.congr_fun hField
    (rotationNonzeroCover period hPeriod axis)
  apply coverSpatialRotationValue_nonzero_at_witness period hPeriod axis
  simpa [smoothDeckEquivariantCoverSpatialRotation,
    coverSpatialRotationSection, zeroSmoothDeckEquivariantCoverGhost] using hAt

/-- Quotient-level packaging of a closed spatial rotation triple. -/
structure D8SpatialRotationGhostRealization where
  ghosts : Fin 3 → Ghost period hPeriod
  bracket_closure : ∀ first second,
    smoothGhostLieBracket period hPeriod (ghosts first) (ghosts second) =
      ∑ output : Fin 3,
        spatialRotationStructureConstant first second output • ghosts output
  faithful : Function.Injective ghosts
  nonzero : ∀ axis, ghosts axis ≠ 0

/-- Cover-level form of the remaining rotation problem.  Smooth dependent
descent itself is no longer an assumption: it is supplied by
`descendSmoothDeckEquivariantCoverGhost`. -/
structure D8SpatialRotationCoverRealization where
  coverGhosts : Fin 3 → SmoothDeckEquivariantCoverGhost period hPeriod
  bracket_closure : ∀ first second,
    smoothGhostLieBracket period hPeriod
        (descendSmoothDeckEquivariantCoverGhost period hPeriod
          (coverGhosts first))
        (descendSmoothDeckEquivariantCoverGhost period hPeriod
          (coverGhosts second)) =
      ∑ output : Fin 3,
        spatialRotationStructureConstant first second output •
          descendSmoothDeckEquivariantCoverGhost period hPeriod
            (coverGhosts output)
  faithful : Function.Injective coverGhosts
  nonzero : ∀ axis,
    coverGhosts axis ≠ zeroSmoothDeckEquivariantCoverGhost period hPeriod

/-- A cover realization gives actual smooth quotient ghosts automatically. -/
def D8SpatialRotationCoverRealization.toGhostRealization
    (realization : D8SpatialRotationCoverRealization period hPeriod) :
    D8SpatialRotationGhostRealization period hPeriod where
  ghosts := fun axis =>
    descendSmoothDeckEquivariantCoverGhost period hPeriod
      (realization.coverGhosts axis)
  bracket_closure := realization.bracket_closure
  faithful := by
    intro first second hEqual
    apply realization.faithful
    exact descendSmoothDeckEquivariantCoverGhost_injective
      period hPeriod hEqual
  nonzero := by
    intro axis hZero
    apply realization.nonzero axis
    apply descendSmoothDeckEquivariantCoverGhost_injective period hPeriod
    simpa using hZero

/-- The exact remaining statement after constructing the three smooth,
faithful, nonzero deck-equivariant cover sections.  Mathlib provides
`mpullback_mlieBracket`, but no ready-made theorem identifies the bracket of
these flow-generated sphere sections through the local quotient projection;
that single naturality equality is isolated here. -/
def DescendedSpatialRotationBracketNaturality : Prop :=
  ∀ first second,
    smoothGhostLieBracket period hPeriod
        (descendSmoothDeckEquivariantCoverGhost period hPeriod
          (smoothDeckEquivariantCoverSpatialRotation period hPeriod first))
        (descendSmoothDeckEquivariantCoverGhost period hPeriod
          (smoothDeckEquivariantCoverSpatialRotation period hPeriod second)) =
      ∑ output : Fin 3,
        spatialRotationStructureConstant first second output •
          descendSmoothDeckEquivariantCoverGhost period hPeriod
            (smoothDeckEquivariantCoverSpatialRotation period hPeriod output)

/-- The implemented cover family closes the previous cover-realization input
as soon as the single bracket-naturality statement is supplied. -/
def explicitD8SpatialRotationCoverRealization
    (bracketNaturality :
      DescendedSpatialRotationBracketNaturality period hPeriod) :
    D8SpatialRotationCoverRealization period hPeriod where
  coverGhosts := smoothDeckEquivariantCoverSpatialRotation period hPeriod
  bracket_closure := bracketNaturality
  faithful :=
    smoothDeckEquivariantCoverSpatialRotation_faithful period hPeriod
  nonzero :=
    smoothDeckEquivariantCoverSpatialRotation_nonzero period hPeriod

/-- Actual quotient ghosts obtained from the explicit rotation sections. -/
def explicitD8SpatialRotationGhostRealization
    (bracketNaturality :
      DescendedSpatialRotationBracketNaturality period hPeriod) :
    D8SpatialRotationGhostRealization period hPeriod :=
  (explicitD8SpatialRotationCoverRealization period hPeriod
    bracketNaturality).toGhostRealization

theorem explicitD8SpatialRotationGhostRealization_nonabelian
    (bracketNaturality :
      DescendedSpatialRotationBracketNaturality period hPeriod) :
    smoothGhostLieBracket period hPeriod
        ((explicitD8SpatialRotationGhostRealization period hPeriod
          bracketNaturality).ghosts 0)
        ((explicitD8SpatialRotationGhostRealization period hPeriod
          bracketNaturality).ghosts 1) ≠ 0 := by
  let realization := explicitD8SpatialRotationGhostRealization
    period hPeriod bracketNaturality
  rw [realization.bracket_closure]
  intro hZero
  have hGhost : realization.ghosts 2 = 0 := by
    simpa [spatialRotationStructureConstant, Fin.sum_univ_succ] using
      congrArg Neg.neg hZero
  exact realization.nonzero 2 hGhost

/-- Unconditional closure of the previously missing section-construction
lock: three genuine smooth, deck-equivariant, faithful and nonzero cover
ghosts now exist. -/
theorem d8_spatial_rotation_smooth_cover_family :
    ∃ coverGhosts : Fin 3 →
        SmoothDeckEquivariantCoverGhost period hPeriod,
      Function.Injective coverGhosts ∧
        ∀ axis, coverGhosts axis ≠
          zeroSmoothDeckEquivariantCoverGhost period hPeriod :=
  ⟨smoothDeckEquivariantCoverSpatialRotation period hPeriod,
    smoothDeckEquivariantCoverSpatialRotation_faithful period hPeriod,
    smoothDeckEquivariantCoverSpatialRotation_nonzero period hPeriod⟩

/-- Any realization is an actual nonabelian closed three-ghost family. -/
theorem D8SpatialRotationGhostRealization.nonabelian
    (realization : D8SpatialRotationGhostRealization period hPeriod) :
    smoothGhostLieBracket period hPeriod
        (realization.ghosts 0) (realization.ghosts 1) ≠ 0 := by
  rw [realization.bracket_closure]
  intro hZero
  have hGhost : realization.ghosts 2 = 0 := by
    simpa [spatialRotationStructureConstant, Fin.sum_univ_succ] using
      congrArg Neg.neg hZero
  exact realization.nonzero 2 hGhost

/-- Coefficient-side data still needed after the geometric triple has been
realized.  This is independent of the sphere/deck descent problem. -/
structure SpatialRotationKoszulCoefficientData
    (realization : D8SpatialRotationGhostRealization period hPeriod) where
  differential : Coefficient →ₗ[Real] Coefficient
  parity_odd : ∀ coefficient,
    ghostCoefficientParity (differential coefficient) =
      -differential (ghostCoefficientParity coefficient)
  leibniz : ∀ first second,
    differential (first * second) =
      differential first * second +
        ghostCoefficientParity first * differential second
  square_zero : ∀ coefficient,
    differential (differential coefficient) = 0
  generator_rule : ∀ output : Fin 3,
    differential (oddGenerator output) =
      (-((2 : Real)⁻¹)) •
        ∑ first : Fin 3, ∑ second : Fin 3,
          spatialRotationStructureConstant first second output •
            (oddGenerator first * oddGenerator second)
  nonlinear_ghost_rule :
    TensorProduct.map differential
        (LinearMap.id : Ghost period hPeriod →ₗ[Real] Ghost period hPeriod)
        (threeGeneratorOddGhost period hPeriod
          (realization.ghosts 0) (realization.ghosts 1)
          (realization.ghosts 2)) =
      threeGeneratorNonlinearGhostBRSTTerm period hPeriod
        (realization.ghosts 0) (realization.ghosts 1)
        (realization.ghosts 2)

/-- Once the two sharply separated bridges are supplied, the existing global
three-generator gate is instantiated without any further assumptions. -/
def closedThreeGeneratorGhostKoszulData
    (realization : D8SpatialRotationGhostRealization period hPeriod)
    (coefficient : SpatialRotationKoszulCoefficientData
      period hPeriod realization) :
    ClosedThreeGeneratorGhostKoszulData period hPeriod where
  ghosts := realization.ghosts
  structureConstant := spatialRotationStructureConstant
  bracket_closure := realization.bracket_closure
  coefficientDifferential := coefficient.differential
  coefficient_parity_odd := coefficient.parity_odd
  coefficient_leibniz := coefficient.leibniz
  coefficient_square_zero := coefficient.square_zero
  generator_rule := coefficient.generator_rule
  nonlinear_ghost_rule := coefficient.nonlinear_ghost_rule

theorem d8_nonabelian_ghost_triple4D_frontier :
    (∀ axis point,
      ∑ index : Fin 4,
        point index * ambientSpatialRotation axis point index = 0) ∧
    (∀ axis point,
      reflectPoint (ambientSpatialRotation axis point) =
        ambientSpatialRotation axis (reflectPoint point)) ∧
    (∀ first second,
      VectorField.lieBracket Real
          (ambientSpatialRotation first) (ambientSpatialRotation second) =
        fun point => ∑ output : Fin 3,
          spatialRotationStructureConstant first second output •
            ambientSpatialRotation output point) ∧
    VectorField.lieBracket Real
        (ambientSpatialRotation 0) (ambientSpatialRotation 1) ≠ 0 :=
  ⟨ambientSpatialRotation_tangent,
    ambientSpatialRotation_reflection_commutes,
    ambientSpatialRotation_lieBracket,
    ambientSpatialRotation_nonabelian⟩

end

end P0EFTJanusMappingTorusD8NonabelianGhostTriple4D
end JanusFormal
