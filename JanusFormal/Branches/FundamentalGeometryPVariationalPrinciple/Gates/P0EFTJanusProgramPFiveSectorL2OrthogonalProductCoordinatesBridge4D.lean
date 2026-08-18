import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiveSectorL2NaturalRepresentationPullbackBridge4D

/-!
# Orthogonal five-sector resolutions as genuine L² coordinates

An inner-product preserving equivalence to the raw five-factor product lifts
canonically to an isometry equivalence to the nested L² product.  If that raw
equivalence is the one underlying the legacy D11 coordinates, the two sets of
sector projectors agree exactly.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiveSectorL2OrthogonalProductCoordinatesBridge4D

set_option autoImplicit false

noncomputable section

open scoped InnerProductSpace
open P0EFTJanusProgramPFiveSectorHilbertCoordinates4D
open P0EFTJanusProgramPFiveSectorOrthogonalProductResolution4D
open P0EFTJanusProgramPFiveSectorL2LinearIsometryResolution4D
open P0EFTJanusProgramPFiveSectorL2HilbertCoordinates4D
open P0EFTJanusProgramPFiveSectorL2NaturalRepresentationPullbackBridge4D

variable
  {E Metric Abelian Matter Longitudinal Boundary : Type*}
  [NormedAddCommGroup E] [InnerProductSpace Real E]
  [NormedAddCommGroup Metric] [InnerProductSpace Real Metric]
  [NormedAddCommGroup Abelian] [InnerProductSpace Real Abelian]
  [NormedAddCommGroup Matter] [InnerProductSpace Real Matter]
  [NormedAddCommGroup Longitudinal] [InnerProductSpace Real Longitudinal]
  [NormedAddCommGroup Boundary] [InnerProductSpace Real Boundary]

/-- Lift an explicitly orthogonal raw-product resolution to the genuine
nested L² Hilbert product. -/
def fiveSectorL2IsometryOfOrthogonalProduct
    (resolution : FiveSectorOrthogonalProductDecomposition
      (E := E) (MetricDiffeomorphism := Metric) (AbelianGauge := Abelian)
      (PrimitiveSpinCMatter := Matter) (LongitudinalLL := Longitudinal)
      (BoundaryFiniteBV := Boundary)) :
    E ≃ₗᵢ[Real] FiveSectorL2Product Metric Abelian Matter Longitudinal Boundary where
  toLinearEquiv := resolution.decomposition.toLinearEquiv.trans
    fiveSectorL2Forget.symm.toLinearEquiv
  norm_map' state := by
    let target : FiveSectorL2Product Metric Abelian Matter Longitudinal Boundary :=
      fiveSectorL2Forget.symm (resolution.decomposition state)
    have hInner : inner Real target target = inner Real state state := by
      calc
        inner Real target target =
            fiveSectorProductInner (fiveSectorL2Forget target)
              (fiveSectorL2Forget target) :=
          (fiveSectorL2Forget_inner target target).symm
        _ = fiveSectorProductInner (resolution.decomposition state)
              (resolution.decomposition state) := by
          simp [target]
        _ = inner Real state state := resolution.inner_map state state
    have hSq : ‖target‖ ^ 2 = ‖state‖ ^ 2 := by
      simpa only [real_inner_self_eq_norm_sq] using hInner
    change ‖target‖ = ‖state‖
    nlinarith [norm_nonneg target, norm_nonneg state]

/-- L² coordinate facade associated to one orthogonal product resolution. -/
def fiveSectorL2HilbertCoordinatesOfOrthogonalProduct
    (resolution : FiveSectorOrthogonalProductDecomposition
      (E := E) (MetricDiffeomorphism := Metric) (AbelianGauge := Abelian)
      (PrimitiveSpinCMatter := Matter) (LongitudinalLL := Longitudinal)
      (BoundaryFiniteBV := Boundary)) :
    FiveSectorL2HilbertCoordinates
      (E := E) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary) where
  decomposition := fiveSectorL2IsometryOfOrthogonalProduct resolution

/-- The lifted L² coordinates recover the projectors of the supplied
orthogonal resolution. -/
theorem fiveSectorL2HilbertCoordinatesOfOrthogonalProduct_projector
    (resolution : FiveSectorOrthogonalProductDecomposition
      (E := E) (MetricDiffeomorphism := Metric) (AbelianGauge := Abelian)
      (PrimitiveSpinCMatter := Matter) (LongitudinalLL := Longitudinal)
      (BoundaryFiniteBV := Boundary))
    (sector : FiveSectorSlot) :
    (fiveSectorL2HilbertCoordinatesOfOrthogonalProduct resolution).sectorProjector
        sector =
      resolution.projection sector := by
  ext state
  apply resolution.decomposition.injective
  simp [fiveSectorL2HilbertCoordinatesOfOrthogonalProduct,
    fiveSectorL2IsometryOfOrthogonalProduct,
    FiveSectorL2HilbertCoordinates.sectorProjector,
    FiveSectorL2HilbertCoordinates.orthogonalProductDecomposition,
    fiveSectorOrthogonalProductDecompositionOfL2Isometry,
    FiveSectorOrthogonalProductDecomposition.projection]
  change resolution.decomposition
      (resolution.decomposition.symm
        (fiveSectorL2Forget
          (fiveSectorL2Forget.symm
            (fiveSectorProductProjection sector
              (resolution.decomposition state))))) =
    fiveSectorProductProjection sector (resolution.decomposition state)
  simp

/-- Exact `projector_eq` adapter consumed by the D11 L² bridges. -/
theorem fiveSectorLegacyProjector_eq_l2OfOrthogonalProduct
    (coordinates : FiveSectorHilbertCoordinates
      (E := E) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary))
    (resolution : FiveSectorOrthogonalProductDecomposition
      (E := E) (MetricDiffeomorphism := Metric) (AbelianGauge := Abelian)
      (PrimitiveSpinCMatter := Matter) (LongitudinalLL := Longitudinal)
      (BoundaryFiniteBV := Boundary))
    (decomposition_eq : resolution.decomposition =
      coordinates.decomposition.toContinuousLinearEquiv)
    (sector : FivePhysicalSector) :
    coordinates.sectorProjector sector =
      (fiveSectorL2HilbertCoordinatesOfOrthogonalProduct resolution).sectorProjector
        (fivePhysicalSectorL2SlotEquiv sector) := by
  rw [fiveSectorL2HilbertCoordinatesOfOrthogonalProduct_projector]
  ext state
  apply coordinates.decomposition.injective
  have hProjection := resolution.projection_apply
    (fivePhysicalSectorL2SlotEquiv sector) state
  rw [decomposition_eq] at hProjection
  rw [hProjection]
  cases sector <;>
    simp [FiveSectorHilbertCoordinates.sectorProjector,
      fivePhysicalSectorL2SlotEquiv, fiveSectorProductProjection,
      fiveSectorMetricProjection, fiveSectorAbelianProjection,
      fiveSectorSpinCProjection, fiveSectorLLProjection,
      fiveSectorBoundaryProjection, fiveSectorMetricAxis,
      fiveSectorAbelianAxis, fiveSectorMatterAxis,
      fiveSectorLongitudinalAxis, fiveSectorBoundaryAxis,
      fiveSectorMetricCoordinate, fiveSectorAbelianCoordinate,
      fiveSectorMatterCoordinate, fiveSectorLongitudinalCoordinate,
      fiveSectorBoundaryCoordinate]

end

end P0EFTJanusProgramPFiveSectorL2OrthogonalProductCoordinatesBridge4D
end JanusFormal
