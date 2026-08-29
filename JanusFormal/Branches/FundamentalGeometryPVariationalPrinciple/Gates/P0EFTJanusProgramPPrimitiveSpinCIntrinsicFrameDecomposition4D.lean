import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9MatterSpinorDoubledIntrinsicDiracOperator4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCLocalGeometricDirac4D

/-!
# Intrinsic SpinC frame in invariant throat generators

The Dirac operator uses the orthonormal radial frame `eᵢ = r ∂ᵢ`, whereas the
canonical measure-preserving integration-by-parts gate uses quotient time
translation and the three round-sphere rotations.  These are not competing
frames.  In radial Euclidean coordinates,

`eᵢ = nᵢ T + ∑ₐ (n × eᵢ)ₐ Rₐ`,

where `T` is the radial/time generator, `Rₐ` is rotation about axis `a`, and
`n` is the unit radial vector.  This file proves that identity first under the
radial derivative equivalence and then on every quotient tangent space.

No new frame, metric, measure or D10 direction is introduced.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPPrimitiveSpinCIntrinsicFrameDecomposition4D

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section

open Set Bundle
open scoped Manifold ContDiff BigOperators InnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D
open P0EFTJanusMappingTorusD8NonabelianGhostThroatBRST4D
open P0EFTJanusProgramPD9MatterSpinorLeviCivitaConnection4D
open P0EFTJanusProgramPD9MatterSpinorDoubledIntrinsicDiracOperator4D
open P0EFTJanusProgramPD9PrimitiveMonopoleCartesianConnection4D
open P0EFTJanusProgramPD9PrimitiveSpinCLocalGeometricDirac4D
open P0EFTJanusNormalPinLiftBoundaryConditions

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev ThroatData := fixedEquatorData period hPeriod
private abbrev ThroatCover := MappingTorusCover (ThroatData period hPeriod)
private abbrev ThroatBase := MappingTorus (ThroatData period hPeriod)
private abbrev EuclideanR3 := EuclideanSpace Real (Fin 3)

local instance throatCoverChartedSpace :
    ChartedSpace ThroatCoverModel (ThroatCover period hPeriod) :=
  fixedThroatCoverChartedSpace period hPeriod

local instance throatCoverIsManifold :
    IsManifold throatCoverModelWithCorners ω (ThroatCover period hPeriod) :=
  fixedThroatCover_isManifold period hPeriod

local instance throatBaseChartedSpace :
    ChartedSpace ThroatCoverModel (ThroatBase period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance throatBaseIsManifold :
    IsManifold throatCoverModelWithCorners ω (ThroatBase period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

/-- Coefficient `(n × eᵢ)ₐ` on the quotient throat. -/
def d9IntrinsicRotationCoefficient
    (direction axis : Fin 3) (base : ThroatBase period hPeriod) : Real :=
  match direction.1, axis.1 with
  | 0, 0 => 0
  | 0, 1 =>
      d9PrimitiveSpinCBaseUnitRadialCoordinate period hPeriod 2 base
  | 0, 2 =>
      -d9PrimitiveSpinCBaseUnitRadialCoordinate period hPeriod 1 base
  | 1, 0 =>
      -d9PrimitiveSpinCBaseUnitRadialCoordinate period hPeriod 2 base
  | 1, 1 => 0
  | 1, 2 =>
      d9PrimitiveSpinCBaseUnitRadialCoordinate period hPeriod 0 base
  | 2, 0 =>
      d9PrimitiveSpinCBaseUnitRadialCoordinate period hPeriod 1 base
  | 2, 1 =>
      -d9PrimitiveSpinCBaseUnitRadialCoordinate period hPeriod 0 base
  | 2, 2 => 0
  | _, _ => 0

/-- The same coefficient before quotient descent. -/
def d9IntrinsicRotationCoefficientCover
    (direction axis : Fin 3) (point : ThroatCover period hPeriod) : Real :=
  match direction.1, axis.1 with
  | 0, 0 => 0
  | 0, 1 => d9UnitRadialCoordinate period hPeriod 2 point
  | 0, 2 => -d9UnitRadialCoordinate period hPeriod 1 point
  | 1, 0 => -d9UnitRadialCoordinate period hPeriod 2 point
  | 1, 1 => 0
  | 1, 2 => d9UnitRadialCoordinate period hPeriod 0 point
  | 2, 0 => d9UnitRadialCoordinate period hPeriod 1 point
  | 2, 1 => -d9UnitRadialCoordinate period hPeriod 0 point
  | 2, 2 => 0
  | _, _ => 0

@[simp]
theorem d9IntrinsicRotationCoefficient_mk
    (direction axis : Fin 3) (point : ThroatCover period hPeriod) :
    d9IntrinsicRotationCoefficient period hPeriod direction axis
        (mappingTorusMk (ThroatData period hPeriod) point) =
      d9IntrinsicRotationCoefficientCover period hPeriod direction axis point := by
  fin_cases direction <;> fin_cases axis <;>
    simp [d9IntrinsicRotationCoefficient,
      d9IntrinsicRotationCoefficientCover,
      d9PrimitiveSpinCBaseUnitRadialCoordinate_mk]

/-- Quotient tangent coordinates obtained by undoing the quotient projection
and applying the genuine radial derivative. -/
def d9QuotientRadialDerivativeEquiv
    (point : ThroatCover period hPeriod) :
    TangentSpace throatCoverModelWithCorners
        (mappingTorusMk (ThroatData period hPeriod) point) ≃L[Real]
      EuclideanR3 :=
  (d9ThroatProjectionDerivativeEquiv period hPeriod point).symm.trans
    (canonicalThroatRadialDerivativeEquiv period hPeriod point)

@[simp]
theorem d9QuotientRadialDerivativeEquiv_projection
    (point : ThroatCover period hPeriod)
    (vector : TangentSpace throatCoverModelWithCorners point) :
    d9QuotientRadialDerivativeEquiv period hPeriod point
        (d9ThroatProjectionDerivativeEquiv period hPeriod point vector) =
      canonicalThroatRadialDerivativeEquiv period hPeriod point vector := by
  simp [d9QuotientRadialDerivativeEquiv]

/-- Image of the intrinsic orthonormal frame under radial coordinates. -/
theorem d9QuotientRadialDerivativeEquiv_intrinsicFrame
    (direction : Fin 3) (point : ThroatCover period hPeriod) :
    d9QuotientRadialDerivativeEquiv period hPeriod point
        (d9IntrinsicThroatFrame period hPeriod direction
          (mappingTorusMk (ThroatData period hPeriod) point)) =
      Real.exp point.time •
        EuclideanSpace.basisFun (Fin 3) Real direction := by
  rw [d9IntrinsicThroatFrame_mk,
    d9QuotientRadialDerivativeEquiv_projection,
    d9IntrinsicThroatCoverFrame_radial]

/-- Image of quotient time translation under radial coordinates. -/
theorem d9QuotientRadialDerivativeEquiv_time
    (point : ThroatCover period hPeriod) :
    d9QuotientRadialDerivativeEquiv period hPeriod point
        (throatTimeTranslationGhost period hPeriod
          (mappingTorusMk (ThroatData period hPeriod) point)) =
      throatCoverRadialMap period hPeriod point := by
  change d9QuotientRadialDerivativeEquiv period hPeriod point
      (throatTimeTranslationVelocity period hPeriod
        (mappingTorusMk (ThroatData period hPeriod) point)) = _
  rw [← throatProjection_mfderiv_time period hPeriod point,
    ← d9ThroatProjectionDerivativeEquiv_coe]
  change d9QuotientRadialDerivativeEquiv period hPeriod point
      (d9ThroatProjectionDerivativeEquiv period hPeriod point
        (throatCoverTimeTranslationValue period hPeriod point)) = _
  rw [d9QuotientRadialDerivativeEquiv_projection]
  change mfderiv throatCoverModelWithCorners 𝓘(Real, EuclideanR3)
      (throatCoverRadialMap period hPeriod) point
        (throatCoverTimeTranslationValue period hPeriod point) = _
  exact throatCoverRadialMap_mfderiv_time period hPeriod point

/-- Projection of one cover rotation velocity is the descended rotation ghost. -/
theorem d9ThroatProjectionDerivativeEquiv_rotation
    (axis : Fin 3) (point : ThroatCover period hPeriod) :
    d9ThroatProjectionDerivativeEquiv period hPeriod point
        (throatCoverSpatialRotationValue period hPeriod axis point) =
      throatSpatialRotationGhost period hPeriod axis
        (mappingTorusMk (ThroatData period hPeriod) point) := by
  change mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
      (mappingTorusMk (ThroatData period hPeriod)) point
        (throatCoverSpatialRotationValue period hPeriod axis point) = _
  rw [throatSpatialRotationGhost,
    descendSmoothDeckEquivariantThroatCoverGhost_mk]
  rfl

/-- Image of one quotient rotation generator under radial coordinates. -/
theorem d9QuotientRadialDerivativeEquiv_rotation
    (axis : Fin 3) (point : ThroatCover period hPeriod) :
    d9QuotientRadialDerivativeEquiv period hPeriod point
        (throatSpatialRotationGhost period hPeriod axis
          (mappingTorusMk (ThroatData period hPeriod) point)) =
      canonicalRotationVelocity axis
        (throatCoverRadialMap period hPeriod point) := by
  rw [← d9ThroatProjectionDerivativeEquiv_rotation period hPeriod axis point,
    d9QuotientRadialDerivativeEquiv_projection]
  change mfderiv throatCoverModelWithCorners 𝓘(Real, EuclideanR3)
      (throatCoverRadialMap period hPeriod) point
        (throatCoverSpatialRotationValue period hPeriod axis point) = _
  exact throatCoverRadialMap_mfderiv_rotation period hPeriod axis point

/-- Euclidean vector identity underlying the frame decomposition. -/
theorem d9IntrinsicEuclideanFrame_decomposition
    (direction : Fin 3) (point : ThroatCover period hPeriod) :
    Real.exp point.time •
        EuclideanSpace.basisFun (Fin 3) Real direction =
      d9UnitRadialCoordinate period hPeriod direction point •
          throatCoverRadialMap period hPeriod point +
        ∑ axis : Fin 3,
          d9IntrinsicRotationCoefficientCover period hPeriod direction axis
              point •
            canonicalRotationVelocity axis
              (throatCoverRadialMap period hPeriod point) := by
  have hNorm :
      ‖(equatorialTwoSphereHomeomorph point.fiber).1‖ = 1 := by
    have hSphere := (equatorialTwoSphereHomeomorph point.fiber).2
    simp only [Metric.mem_sphere, dist_zero_right] at hSphere
    exact hSphere
  have hSquare := EuclideanSpace.real_norm_sq_eq
    (equatorialTwoSphereHomeomorph point.fiber).1
  rw [hNorm] at hSquare
  norm_num at hSquare
  simp [Fin.sum_univ_succ] at hSquare
  apply (EuclideanSpace.equiv (Fin 3) Real).injective
  funext coordinate
  fin_cases direction <;> fin_cases coordinate <;>
    simp [d9IntrinsicRotationCoefficientCover, Fin.sum_univ_succ,
      throatCoverRadialMap_apply, d9UnitRadialCoordinate,
      canonicalRotationVelocity] <;>
    try ring <;>
    (conv_lhs => rw [← mul_one (Real.exp point.time), hSquare]) <;>
    ring

/-- Exact quotient decomposition at one selected mapping-torus representative. -/
theorem d9IntrinsicThroatFrame_decomposition_mk
    (direction : Fin 3) (point : ThroatCover period hPeriod) :
    d9IntrinsicThroatFrame period hPeriod direction
        (mappingTorusMk (ThroatData period hPeriod) point) =
      d9PrimitiveSpinCBaseUnitRadialCoordinate period hPeriod direction
          (mappingTorusMk (ThroatData period hPeriod) point) •
        throatTimeTranslationGhost period hPeriod
          (mappingTorusMk (ThroatData period hPeriod) point) +
      ∑ axis : Fin 3,
        d9IntrinsicRotationCoefficient period hPeriod direction axis
            (mappingTorusMk (ThroatData period hPeriod) point) •
          throatSpatialRotationGhost period hPeriod axis
            (mappingTorusMk (ThroatData period hPeriod) point) := by
  apply (d9QuotientRadialDerivativeEquiv period hPeriod point).injective
  rw [d9QuotientRadialDerivativeEquiv_intrinsicFrame,
    map_add, map_smul, map_sum]
  simp_rw [map_smul,
    d9QuotientRadialDerivativeEquiv_time,
    d9QuotientRadialDerivativeEquiv_rotation,
    d9IntrinsicRotationCoefficient_mk,
    d9PrimitiveSpinCBaseUnitRadialCoordinate_mk]
  exact d9IntrinsicEuclideanFrame_decomposition
    period hPeriod direction point

/-- Global frame decomposition on every quotient tangent space. -/
theorem d9IntrinsicThroatFrame_decomposition
    (direction : Fin 3) (base : ThroatBase period hPeriod) :
    d9IntrinsicThroatFrame period hPeriod direction base =
      d9PrimitiveSpinCBaseUnitRadialCoordinate period hPeriod direction base •
        throatTimeTranslationGhost period hPeriod base +
      ∑ axis : Fin 3,
        d9IntrinsicRotationCoefficient period hPeriod direction axis base •
          throatSpatialRotationGhost period hPeriod axis base := by
  obtain ⟨point, rfl⟩ :=
    mappingTorusMk_surjective (ThroatData period hPeriod) base
  exact d9IntrinsicThroatFrame_decomposition_mk
    period hPeriod direction point

/-- Directional derivatives in the intrinsic frame are the corresponding
variable-coefficient combination of the four invariant generators. -/
theorem mfderiv_intrinsicThroatFrame_decomposition
    {Fiber : Type*} [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
    (field : ThroatBase period hPeriod → Fiber)
    (direction : Fin 3) (base : ThroatBase period hPeriod) :
    mfderiv throatCoverModelWithCorners 𝓘(Real, Fiber) field base
        (d9IntrinsicThroatFrame period hPeriod direction base) =
      d9PrimitiveSpinCBaseUnitRadialCoordinate period hPeriod direction base •
        mfderiv throatCoverModelWithCorners 𝓘(Real, Fiber) field base
          (throatTimeTranslationGhost period hPeriod base) +
      ∑ axis : Fin 3,
        d9IntrinsicRotationCoefficient period hPeriod direction axis base •
          mfderiv throatCoverModelWithCorners 𝓘(Real, Fiber) field base
            (throatSpatialRotationGhost period hPeriod axis base) := by
  rw [d9IntrinsicThroatFrame_decomposition]
  simp only [map_add, map_smul, map_sum]

/-- Public certificate that the Dirac frame and the invariant-flow frame are
the same tangent geometry. -/
structure ProgramPPrimitiveSpinCIntrinsicFrameDecompositionCertificate4D :
    Prop where
  decomposition : ∀ direction base,
    d9IntrinsicThroatFrame period hPeriod direction base =
      d9PrimitiveSpinCBaseUnitRadialCoordinate period hPeriod direction base •
        throatTimeTranslationGhost period hPeriod base +
      ∑ axis : Fin 3,
        d9IntrinsicRotationCoefficient period hPeriod direction axis base •
          throatSpatialRotationGhost period hPeriod axis base

/-- The radial and rotational flows construct the certificate
unconditionally. -/
def programPPrimitiveSpinCIntrinsicFrameDecompositionCertificate4D :
    ProgramPPrimitiveSpinCIntrinsicFrameDecompositionCertificate4D period
      hPeriod where
  decomposition := d9IntrinsicThroatFrame_decomposition period hPeriod

end
end P0EFTJanusProgramPPrimitiveSpinCIntrinsicFrameDecomposition4D
end JanusFormal
