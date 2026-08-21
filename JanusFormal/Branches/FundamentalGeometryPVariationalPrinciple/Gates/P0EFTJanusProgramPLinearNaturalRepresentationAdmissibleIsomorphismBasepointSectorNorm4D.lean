import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPLinearNaturalRepresentationAdmissibleIsomorphismFamilySectorMetric4D

/-!
# Basepoint-sector norm assembly for represented D11 transport

This is the basepoint-only analogue of the pairwise sector metric packet.  It
records norm preservation solely for `reverseLinear 0 parameter` and therefore
constructs a unitary basepoint frame without constructing `MetricData`.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPLinearNaturalRepresentationAdmissibleIsomorphismBasepointSectorNorm4D

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
open P0EFTJanusProgramPLinearNaturalRepresentationAdmissibleIsomorphismFamily4D

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

/-- Sectorwise isometry data only for the basepoint-restricted family
`reverseLinear 0 parameter`. -/
structure LinearNaturalRepresentationAdmissibleIsomorphismBasepointSectorNormData
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
    (isomorphisms : LinearNaturalRepresentationAdmissibleIsomorphismFamilyData
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
    ‖isomorphisms.reverseLinear 0 parameter
        (resolution.projection sector state)‖ =
      ‖resolution.projection sector state‖

namespace LinearNaturalRepresentationAdmissibleIsomorphismBasepointSectorNormData

/-- Construct the basepoint-sector certificate from an orthogonal product
resolution agreeing with the represented coordinates. -/
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
    (isomorphisms : LinearNaturalRepresentationAdmissibleIsomorphismFamilyData
      representation coordinates refinement pullback)
    (resolution : FiveSectorOrthogonalProductDecomposition
      (E := State) (MetricDiffeomorphism := Metric)
      (AbelianGauge := Abelian) (PrimitiveSpinCMatter := Matter)
      (LongitudinalLL := Longitudinal) (BoundaryFiniteBV := Boundary))
    (decomposition_eq : resolution.decomposition =
      coordinates.decomposition.toContinuousLinearEquiv)
    (reverse_projection_norm_map : ∀ parameter sector state,
      ‖isomorphisms.reverseLinear 0 parameter
          (resolution.projection sector state)‖ =
        ‖resolution.projection sector state‖) :
    LinearNaturalRepresentationAdmissibleIsomorphismBasepointSectorNormData
      representation coordinates refinement pullback isomorphisms resolution where
  projection_eq := by
    intro sector
    have hProjection := fiveSectorLegacyProjector_eq_l2OfOrthogonalProduct
      coordinates resolution decomposition_eq
        (fivePhysicalSectorL2SlotEquiv.symm sector)
    rw [fiveSectorL2HilbertCoordinatesOfOrthogonalProduct_projector] at hProjection
    simpa using hProjection
  reverse_projection_norm_map := reverse_projection_norm_map

/-- The basepoint reverse pullback commutes with the orthogonal resolution. -/
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
    (isomorphisms : LinearNaturalRepresentationAdmissibleIsomorphismFamilyData
      representation coordinates refinement pullback)
    (resolution : FiveSectorOrthogonalProductDecomposition
      (E := State) (MetricDiffeomorphism := Metric)
      (AbelianGauge := Abelian) (PrimitiveSpinCMatter := Matter)
      (LongitudinalLL := Longitudinal) (BoundaryFiniteBV := Boundary))
    (sectorNorm :
      LinearNaturalRepresentationAdmissibleIsomorphismBasepointSectorNormData
        representation coordinates refinement pullback isomorphisms resolution)
    (parameter : Real) (sector : FiveSectorSlot) (state : State) :
    isomorphisms.reverseLinear 0 parameter
        (resolution.projection sector state) =
      resolution.projection sector
        (isomorphisms.reverseLinear 0 parameter state) := by
  rw [← sectorNorm.projection_eq sector,
    ← isomorphisms.reverse_source_agreement 0 parameter
      (coordinates.sectorProjector
        (fivePhysicalSectorL2SlotEquiv.symm sector) state),
    ← isomorphisms.reverse_source_agreement 0 parameter state]
  exact (pullback.source_commutes
    (isomorphisms.isomorphism 0 parameter).inv
    (fivePhysicalSectorL2SlotEquiv.symm sector) state).symm

/-- Five sectorwise basepoint isometries imply global norm preservation. -/
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
    (isomorphisms : LinearNaturalRepresentationAdmissibleIsomorphismFamilyData
      representation coordinates refinement pullback)
    (resolution : FiveSectorOrthogonalProductDecomposition
      (E := State) (MetricDiffeomorphism := Metric)
      (AbelianGauge := Abelian) (PrimitiveSpinCMatter := Matter)
      (LongitudinalLL := Longitudinal) (BoundaryFiniteBV := Boundary))
    (sectorNorm :
      LinearNaturalRepresentationAdmissibleIsomorphismBasepointSectorNormData
        representation coordinates refinement pullback isomorphisms resolution)
    (parameter : Real) (state : State) :
    ‖isomorphisms.reverseLinear 0 parameter state‖ = ‖state‖ := by
  have hSq :
      ‖isomorphisms.reverseLinear 0 parameter state‖ ^ 2 = ‖state‖ ^ 2 := by
    calc
      ‖isomorphisms.reverseLinear 0 parameter state‖ ^ 2 =
          ∑ sector : FiveSectorSlot,
            ‖resolution.projection sector
              (isomorphisms.reverseLinear 0 parameter state)‖ ^ 2 :=
        fiveSectorProjection_norm_sq_sum resolution
          (isomorphisms.reverseLinear 0 parameter state)
      _ = ∑ sector : FiveSectorSlot,
            ‖isomorphisms.reverseLinear 0 parameter
              (resolution.projection sector state)‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro sector _
        rw [sectorNorm.reverse_projection_commutes representation coordinates
          refinement pullback isomorphisms resolution parameter sector state]
      _ = ∑ sector : FiveSectorSlot,
            ‖resolution.projection sector state‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro sector _
        rw [sectorNorm.reverse_projection_norm_map parameter sector state]
      _ = ‖state‖ ^ 2 :=
        (fiveSectorProjection_norm_sq_sum resolution state).symm
  nlinarith [norm_nonneg (isomorphisms.reverseLinear 0 parameter state),
    norm_nonneg state]

end LinearNaturalRepresentationAdmissibleIsomorphismBasepointSectorNormData

end
end P0EFTJanusProgramPLinearNaturalRepresentationAdmissibleIsomorphismBasepointSectorNorm4D
end JanusFormal
