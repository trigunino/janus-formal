import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPrimitiveSpinCIntrinsicFrameDecomposition4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCGeometricDiracLeibniz4D

/-!
# Coordinate derivatives for the intrinsic SpinC frame

The previous gate expresses each intrinsic Dirac-frame vector in quotient time
and rotation generators.  This file proves the inverse identities and computes
how the unit radial coordinates transform under those generators:

* quotient time translation fixes every sphere coordinate;
* rotation about axis `a` differentiates coordinate `j` by
  `(n × eⱼ)ₐ`;
* the sum of the coefficient divergences in the intrinsic-frame decomposition
  is `-2 nⱼ`.

The last identity is the exact divergence defect of `eⱼ = r ∂ⱼ` for the
product throat volume.  It is derived from the already proved tangential
projector formula, not supplied as a geometric assumption.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPPrimitiveSpinCIntrinsicFrameCoordinateDerivatives4D

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section

open Set Bundle
open scoped Manifold ContDiff BigOperators InnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D
open P0EFTJanusProgramPD9MatterSpinorDoubledIntrinsicDiracOperator4D
open P0EFTJanusProgramPD9PrimitiveMonopoleCartesianConnection4D
open P0EFTJanusProgramPD9PrimitiveSpinCLocalGeometricDirac4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricDiracLeibniz4D
open P0EFTJanusProgramPPrimitiveSpinCIntrinsicFrameDecomposition4D
open P0EFTJanusNormalPinLiftBoundaryConditions

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev ThroatData := fixedEquatorData period hPeriod
private abbrev ThroatCover := MappingTorusCover (ThroatData period hPeriod)
private abbrev ThroatBase := MappingTorus (ThroatData period hPeriod)

local instance throatBaseChartedSpace :
    ChartedSpace ThroatCoverModel (ThroatBase period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance throatBaseIsManifold :
    IsManifold throatCoverModelWithCorners ω (ThroatBase period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

/-! ## Inverse frame decompositions -/

/-- Euclidean radial vector as its orthonormal-coordinate expansion. -/
theorem d9EuclideanTimeGenerator_intrinsic_decomposition
    (point : ThroatCover period hPeriod) :
    throatCoverRadialMap period hPeriod point =
      ∑ direction : Fin 3,
        d9UnitRadialCoordinate period hPeriod direction point •
          (Real.exp point.time •
            EuclideanSpace.basisFun (Fin 3) Real direction) := by
  apply (EuclideanSpace.equiv (Fin 3) Real).injective
  funext coordinate
  fin_cases coordinate <;>
    simp [Fin.sum_univ_succ, throatCoverRadialMap_apply,
      d9UnitRadialCoordinate]

/-- Every Euclidean rotation velocity expands in the intrinsic orthonormal
frame with coefficients `(n × eᵢ)ₐ`. -/
theorem d9EuclideanRotationGenerator_intrinsic_decomposition
    (axis : Fin 3) (point : ThroatCover period hPeriod) :
    canonicalRotationVelocity axis
        (throatCoverRadialMap period hPeriod point) =
      ∑ direction : Fin 3,
        d9IntrinsicRotationCoefficientCover period hPeriod direction axis point •
          (Real.exp point.time •
            EuclideanSpace.basisFun (Fin 3) Real direction) := by
  apply (EuclideanSpace.equiv (Fin 3) Real).injective
  funext coordinate
  fin_cases axis <;> fin_cases coordinate <;>
    simp [Fin.sum_univ_succ, throatCoverRadialMap_apply,
      d9UnitRadialCoordinate, canonicalRotationVelocity,
      d9IntrinsicRotationCoefficientCover] <;>
    ring

/-- Quotient time translation is the radial-coordinate combination of the
three intrinsic frame vectors. -/
theorem throatTimeTranslationGhost_eq_intrinsic_sum
    (base : ThroatBase period hPeriod) :
    throatTimeTranslationGhost period hPeriod base =
      ∑ direction : Fin 3,
        d9PrimitiveSpinCBaseUnitRadialCoordinate period hPeriod direction base •
          d9IntrinsicThroatFrame period hPeriod direction base := by
  obtain ⟨point, rfl⟩ :=
    mappingTorusMk_surjective (ThroatData period hPeriod) base
  apply (d9QuotientRadialDerivativeEquiv period hPeriod point).injective
  rw [d9QuotientRadialDerivativeEquiv_time, map_sum]
  simp_rw [map_smul,
    d9QuotientRadialDerivativeEquiv_intrinsicFrame,
    d9PrimitiveSpinCBaseUnitRadialCoordinate_mk]
  exact d9EuclideanTimeGenerator_intrinsic_decomposition
    period hPeriod point

/-- Each quotient rotation generator is the corresponding tangential
combination of the intrinsic frame. -/
theorem throatSpatialRotationGhost_eq_intrinsic_sum
    (axis : Fin 3) (base : ThroatBase period hPeriod) :
    throatSpatialRotationGhost period hPeriod axis base =
      ∑ direction : Fin 3,
        d9IntrinsicRotationCoefficient period hPeriod direction axis base •
          d9IntrinsicThroatFrame period hPeriod direction base := by
  obtain ⟨point, rfl⟩ :=
    mappingTorusMk_surjective (ThroatData period hPeriod) base
  apply (d9QuotientRadialDerivativeEquiv period hPeriod point).injective
  rw [d9QuotientRadialDerivativeEquiv_rotation, map_sum]
  simp_rw [map_smul,
    d9QuotientRadialDerivativeEquiv_intrinsicFrame,
    d9IntrinsicRotationCoefficient_mk]
  exact d9EuclideanRotationGenerator_intrinsic_decomposition
    period hPeriod axis point

/-! ## Radial-coordinate derivatives -/

private theorem d9BaseUnitRadialCoordinate_sq_sum
    (base : ThroatBase period hPeriod) :
    (d9PrimitiveSpinCBaseUnitRadialCoordinate period hPeriod 0 base) ^ 2 +
        (d9PrimitiveSpinCBaseUnitRadialCoordinate period hPeriod 1 base) ^ 2 +
        (d9PrimitiveSpinCBaseUnitRadialCoordinate period hPeriod 2 base) ^ 2 =
      1 := by
  simpa [d9PrimitiveSpinCBaseUnitRadialCoordinate,
    d9PrimitiveMonopoleBaseCoordinate] using
    monopoleSphereCoordinate_sq_sum
      (d9ThroatMonopoleSphereProjection period hPeriod base)

/-- Quotient time translation fixes all unit radial coordinates. -/
theorem d9BaseUnitRadialCoordinate_mvfderiv_time
    (coordinate : Fin 3) (base : ThroatBase period hPeriod) :
    mvfderiv throatCoverModelWithCorners
        (d9PrimitiveSpinCBaseUnitRadialCoordinate period hPeriod coordinate)
        base (throatTimeTranslationGhost period hPeriod base) = 0 := by
  rw [throatTimeTranslationGhost_eq_intrinsic_sum, map_sum]
  simp_rw [map_smul]
  change
    (∑ direction : Fin 3,
      d9PrimitiveSpinCBaseUnitRadialCoordinate period hPeriod direction base *
        d9PrimitiveMonopoleCoordinateFrameDerivative period hPeriod coordinate
          direction base) = 0
  simp_rw [d9PrimitiveMonopoleCoordinateFrameDerivative_eq_projector]
  have hSphere := d9BaseUnitRadialCoordinate_sq_sum period hPeriod base
  fin_cases coordinate <;>
    simp [Fin.sum_univ_succ, d9KroneckerDelta] at hSphere ⊢ <;>
    nlinarith

/-- Rotation about axis `a` differentiates coordinate `j` by
`(n × eⱼ)ₐ`, exactly the coefficient used in the frame decomposition. -/
theorem d9BaseUnitRadialCoordinate_mvfderiv_rotation
    (axis coordinate : Fin 3) (base : ThroatBase period hPeriod) :
    mvfderiv throatCoverModelWithCorners
        (d9PrimitiveSpinCBaseUnitRadialCoordinate period hPeriod coordinate)
        base (throatSpatialRotationGhost period hPeriod axis base) =
      d9IntrinsicRotationCoefficient period hPeriod coordinate axis base := by
  rw [throatSpatialRotationGhost_eq_intrinsic_sum, map_sum]
  simp_rw [map_smul]
  change
    (∑ direction : Fin 3,
      d9IntrinsicRotationCoefficient period hPeriod direction axis base *
        d9PrimitiveMonopoleCoordinateFrameDerivative period hPeriod coordinate
          direction base) = _
  simp_rw [d9PrimitiveMonopoleCoordinateFrameDerivative_eq_projector]
  have hSphere := d9BaseUnitRadialCoordinate_sq_sum period hPeriod base
  fin_cases axis <;> fin_cases coordinate <;>
    simp [Fin.sum_univ_succ, d9KroneckerDelta,
      d9IntrinsicRotationCoefficient] at hSphere ⊢ <;>
    nlinarith

/-- The rotation coefficients have total invariant-frame derivative
`-2 nᵢ`.  This is the divergence of `r ∂ᵢ` relative to the product throat
measure, since the four generating flows themselves preserve that measure. -/
theorem d9IntrinsicRotationCoefficient_rotationDerivative_sum
    (direction : Fin 3) (base : ThroatBase period hPeriod) :
    (∑ axis : Fin 3,
      mvfderiv throatCoverModelWithCorners
        (d9IntrinsicRotationCoefficient period hPeriod direction axis)
        base (throatSpatialRotationGhost period hPeriod axis base)) =
      -2 * d9PrimitiveSpinCBaseUnitRadialCoordinate
        period hPeriod direction base := by
  have hSmooth (coordinate : Fin 3) :
      MDifferentiableAt throatCoverModelWithCorners 𝓘(Real, Real)
        (d9PrimitiveSpinCBaseUnitRadialCoordinate period hPeriod coordinate)
        base :=
    (d9PrimitiveMonopoleBaseCoordinate_contMDiff period hPeriod coordinate)
      |>.mdifferentiableAt (by simp)
  fin_cases direction <;>
    simp [Fin.sum_univ_succ, d9IntrinsicRotationCoefficient,
      mfderiv_const, mfderiv_neg, hSmooth,
      d9BaseUnitRadialCoordinate_mvfderiv_rotation] <;>
    ring

/-- The complete coefficient divergence in the decomposition of `eᵢ` is
`-2 nᵢ`: the time coefficient has zero time derivative and the rotational
coefficients contribute the whole defect. -/
theorem d9IntrinsicFrameCoefficientDivergence
    (direction : Fin 3) (base : ThroatBase period hPeriod) :
    mvfderiv throatCoverModelWithCorners
        (d9PrimitiveSpinCBaseUnitRadialCoordinate period hPeriod direction)
        base (throatTimeTranslationGhost period hPeriod base) +
      ∑ axis : Fin 3,
        mvfderiv throatCoverModelWithCorners
          (d9IntrinsicRotationCoefficient period hPeriod direction axis)
          base (throatSpatialRotationGhost period hPeriod axis base) =
      -2 * d9PrimitiveSpinCBaseUnitRadialCoordinate period hPeriod direction
        base := by
  rw [d9BaseUnitRadialCoordinate_mvfderiv_time,
    zero_add, d9IntrinsicRotationCoefficient_rotationDerivative_sum]

/-- Public certificate for the exact divergence defect of the Dirac frame. -/
structure ProgramPPrimitiveSpinCIntrinsicFrameDivergenceCertificate4D : Prop where
  coefficientDivergence : ∀ direction base,
    mvfderiv throatCoverModelWithCorners
        (d9PrimitiveSpinCBaseUnitRadialCoordinate period hPeriod direction)
        base (throatTimeTranslationGhost period hPeriod base) +
      ∑ axis : Fin 3,
        mvfderiv throatCoverModelWithCorners
          (d9IntrinsicRotationCoefficient period hPeriod direction axis)
          base (throatSpatialRotationGhost period hPeriod axis base) =
      -2 * d9PrimitiveSpinCBaseUnitRadialCoordinate period hPeriod direction
        base

/-- The explicit sphere-coordinate algebra supplies the certificate
unconditionally. -/
def programPPrimitiveSpinCIntrinsicFrameDivergenceCertificate4D :
    ProgramPPrimitiveSpinCIntrinsicFrameDivergenceCertificate4D period hPeriod
    where
  coefficientDivergence :=
    d9IntrinsicFrameCoefficientDivergence period hPeriod

end
end P0EFTJanusProgramPPrimitiveSpinCIntrinsicFrameCoordinateDerivatives4D
end JanusFormal
