import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPLinearNaturalRepresentationAdmissibleIsomorphismBasepointSectorNorm4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPLinearNaturalRepresentationAdmissibleIsomorphismFrame4D

/-!
# Sector norm assembly for a represented basepoint frame

Five sectorwise norm identities for the chosen `0 → parameter` frame imply
global norm preservation.  No pairwise admissible-isomorphism family is used.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPLinearNaturalRepresentationAdmissibleIsomorphismFrameSectorNorm4D

set_option autoImplicit false
noncomputable section

open scoped BigOperators InnerProductSpace
open P0EFTJanusSpinCImmersionCategory
open P0EFTJanusNaturalEllipticFamilyExistence
open P0EFTJanusProgramPNaturalEllipticOperatorRepresentation4D
open P0EFTJanusProgramPFiveSectorHilbertCoordinates4D
open P0EFTJanusProgramPFiveSectorNaturalRepresentationRefinement4D
open P0EFTJanusProgramPFiveSectorNaturalRepresentationPullback4D
open P0EFTJanusProgramPFiveSectorOrthogonalProductResolution4D
open P0EFTJanusProgramPFiveSectorOrthogonalProductPythagoras4D
open P0EFTJanusProgramPFiveSectorL2NaturalRepresentationPullbackBridge4D
open P0EFTJanusProgramPFiveSectorL2OrthogonalProductCoordinatesBridge4D
open P0EFTJanusProgramPLinearNaturalRepresentationAdmissibleIsomorphismFrame4D

variable
  {State Metric Abelian Matter Longitudinal Boundary : Type*}
  [NormedAddCommGroup State] [InnerProductSpace Real State]
  [NormedAddCommGroup Metric] [InnerProductSpace Real Metric]
  [NormedAddCommGroup Abelian] [InnerProductSpace Real Abelian]
  [NormedAddCommGroup Matter] [InnerProductSpace Real Matter]
  [NormedAddCommGroup Longitudinal] [InnerProductSpace Real Longitudinal]
  [NormedAddCommGroup Boundary] [InnerProductSpace Real Boundary]
  {immersionCategory : SpinCImmersionCategory}
  {family : NaturalEllipticOperatorFamily immersionCategory}
  {operator : Real → State →L[Real] State}

/-- Sectorwise isometry data for a chosen represented basepoint frame. -/
structure LinearNaturalRepresentationAdmissibleIsomorphismFrameSectorNormData
    (representation : NaturalEllipticOperatorRepresentationData
      immersionCategory family
        (fun parameter state => operator parameter state))
    (coordinates : FiveSectorHilbertCoordinates
      (E := State) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary))
    (refinement : FiveSectorNaturalRepresentationRefinementData
      representation coordinates)
    (pullback : FiveSectorNaturalRepresentationPullbackData
      representation coordinates refinement)
    (frameData : LinearNaturalRepresentationAdmissibleIsomorphismFrameData
      representation coordinates refinement pullback)
    (resolution : FiveSectorOrthogonalProductDecomposition
      (E := State) (MetricDiffeomorphism := Metric)
      (AbelianGauge := Abelian) (PrimitiveSpinCMatter := Matter)
      (LongitudinalLL := Longitudinal) (BoundaryFiniteBV := Boundary)) where
  projection_eq : ∀ sector : FiveSectorSlot,
    coordinates.sectorProjector
        (fivePhysicalSectorL2SlotEquiv.symm sector) =
      resolution.projection sector
  reverse_projection_norm_map : ∀ parameter sector state,
    ‖frameData.reverseLinear parameter
        (resolution.projection sector state)‖ =
      ‖resolution.projection sector state‖

namespace LinearNaturalRepresentationAdmissibleIsomorphismFrameSectorNormData

/-- Construct the certificate from the canonical orthogonal product. -/
def ofOrthogonalProduct
    (representation : NaturalEllipticOperatorRepresentationData
      immersionCategory family
        (fun parameter state => operator parameter state))
    (coordinates : FiveSectorHilbertCoordinates
      (E := State) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary))
    (refinement : FiveSectorNaturalRepresentationRefinementData
      representation coordinates)
    (pullback : FiveSectorNaturalRepresentationPullbackData
      representation coordinates refinement)
    (frameData : LinearNaturalRepresentationAdmissibleIsomorphismFrameData
      representation coordinates refinement pullback)
    (resolution : FiveSectorOrthogonalProductDecomposition
      (E := State) (MetricDiffeomorphism := Metric)
      (AbelianGauge := Abelian) (PrimitiveSpinCMatter := Matter)
      (LongitudinalLL := Longitudinal) (BoundaryFiniteBV := Boundary))
    (decomposition_eq : resolution.decomposition =
      coordinates.decomposition.toContinuousLinearEquiv)
    (reverse_projection_norm_map : ∀ parameter sector state,
      ‖frameData.reverseLinear parameter
          (resolution.projection sector state)‖ =
        ‖resolution.projection sector state‖) :
    LinearNaturalRepresentationAdmissibleIsomorphismFrameSectorNormData
      representation coordinates refinement pullback frameData resolution where
  projection_eq := by
    intro sector
    have hProjection := fiveSectorLegacyProjector_eq_l2OfOrthogonalProduct
      coordinates resolution decomposition_eq
        (fivePhysicalSectorL2SlotEquiv.symm sector)
    rw [fiveSectorL2HilbertCoordinatesOfOrthogonalProduct_projector] at hProjection
    simpa using hProjection
  reverse_projection_norm_map := reverse_projection_norm_map

/-- The frame commutes with the canonical orthogonal projections. -/
theorem reverse_projection_commutes
    (representation : NaturalEllipticOperatorRepresentationData
      immersionCategory family
        (fun parameter state => operator parameter state))
    (coordinates : FiveSectorHilbertCoordinates
      (E := State) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary))
    (refinement : FiveSectorNaturalRepresentationRefinementData
      representation coordinates)
    (pullback : FiveSectorNaturalRepresentationPullbackData
      representation coordinates refinement)
    (frameData : LinearNaturalRepresentationAdmissibleIsomorphismFrameData
      representation coordinates refinement pullback)
    (resolution : FiveSectorOrthogonalProductDecomposition
      (E := State) (MetricDiffeomorphism := Metric)
      (AbelianGauge := Abelian) (PrimitiveSpinCMatter := Matter)
      (LongitudinalLL := Longitudinal) (BoundaryFiniteBV := Boundary))
    (sectorNorm :
      LinearNaturalRepresentationAdmissibleIsomorphismFrameSectorNormData
        representation coordinates refinement pullback frameData resolution)
    (parameter : Real) (sector : FiveSectorSlot) (state : State) :
    frameData.reverseLinear parameter
        (resolution.projection sector state) =
      resolution.projection sector
        (frameData.reverseLinear parameter state) := by
  rw [← sectorNorm.projection_eq sector,
    ← frameData.reverse_source_agreement parameter
      (coordinates.sectorProjector
        (fivePhysicalSectorL2SlotEquiv.symm sector) state),
    ← frameData.reverse_source_agreement parameter state]
  exact (pullback.source_commutes
    (frameData.isomorphismAt parameter).inv
    (fivePhysicalSectorL2SlotEquiv.symm sector) state).symm

/-- Five sectorwise frame isometries imply global norm preservation. -/
theorem reverse_norm_map
    (representation : NaturalEllipticOperatorRepresentationData
      immersionCategory family
        (fun parameter state => operator parameter state))
    (coordinates : FiveSectorHilbertCoordinates
      (E := State) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary))
    (refinement : FiveSectorNaturalRepresentationRefinementData
      representation coordinates)
    (pullback : FiveSectorNaturalRepresentationPullbackData
      representation coordinates refinement)
    (frameData : LinearNaturalRepresentationAdmissibleIsomorphismFrameData
      representation coordinates refinement pullback)
    (resolution : FiveSectorOrthogonalProductDecomposition
      (E := State) (MetricDiffeomorphism := Metric)
      (AbelianGauge := Abelian) (PrimitiveSpinCMatter := Matter)
      (LongitudinalLL := Longitudinal) (BoundaryFiniteBV := Boundary))
    (sectorNorm :
      LinearNaturalRepresentationAdmissibleIsomorphismFrameSectorNormData
        representation coordinates refinement pullback frameData resolution)
    (parameter : Real) (state : State) :
    ‖frameData.reverseLinear parameter state‖ = ‖state‖ := by
  have hSq :
      ‖frameData.reverseLinear parameter state‖ ^ 2 = ‖state‖ ^ 2 := by
    calc
      ‖frameData.reverseLinear parameter state‖ ^ 2 =
          ∑ sector : FiveSectorSlot,
            ‖resolution.projection sector
              (frameData.reverseLinear parameter state)‖ ^ 2 :=
        fiveSectorProjection_norm_sq_sum resolution
          (frameData.reverseLinear parameter state)
      _ = ∑ sector : FiveSectorSlot,
            ‖frameData.reverseLinear parameter
              (resolution.projection sector state)‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro sector _
        rw [sectorNorm.reverse_projection_commutes representation coordinates
          refinement pullback frameData resolution parameter sector state]
      _ = ∑ sector : FiveSectorSlot,
            ‖resolution.projection sector state‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro sector _
        rw [sectorNorm.reverse_projection_norm_map parameter sector state]
      _ = ‖state‖ ^ 2 :=
        (fiveSectorProjection_norm_sq_sum resolution state).symm
  nlinarith [norm_nonneg (frameData.reverseLinear parameter state),
    norm_nonneg state]

end LinearNaturalRepresentationAdmissibleIsomorphismFrameSectorNormData

end
end P0EFTJanusProgramPLinearNaturalRepresentationAdmissibleIsomorphismFrameSectorNorm4D
end JanusFormal
