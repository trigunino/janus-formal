import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPLinearNaturalRepresentationAdmissibleIsomorphismFamilyMetric4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiveSectorL2OrthogonalProductCoordinatesBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiveSectorOrthogonalProductPythagoras4D

/-!
# Sectorwise metric assembly for represented D11 transport

Five sectorwise norm-preservation statements assemble into metric compatibility
of the full represented D11 pullback.  The only bridge required is exact
agreement between the D11 projectors and one orthogonal product resolution.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPLinearNaturalRepresentationAdmissibleIsomorphismFamilySectorMetric4D

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
open P0EFTJanusProgramPLinearNaturalRepresentationAdmissibleIsomorphismFamilyMetric4D

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

/-- Sectorwise norm preservation for a represented D11 family, measured with
one genuine orthogonal product resolution. -/
structure LinearNaturalRepresentationAdmissibleIsomorphismFamilySectorMetricData
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
  reverse_projection_norm_map : ∀ first second sector state,
    ‖isomorphisms.reverseLinear first second
        (resolution.projection sector state)‖ =
      ‖resolution.projection sector state‖

namespace LinearNaturalRepresentationAdmissibleIsomorphismFamilySectorMetricData

/-- Build the sectorwise certificate from the raw/L² decomposition agreement
already supplied by an orthogonal product resolution. -/
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
    (reverse_projection_norm_map : ∀ first second sector state,
      ‖isomorphisms.reverseLinear first second
          (resolution.projection sector state)‖ =
        ‖resolution.projection sector state‖) :
    LinearNaturalRepresentationAdmissibleIsomorphismFamilySectorMetricData
      representation coordinates refinement pullback isomorphisms resolution where
  projection_eq := by
    intro sector
    have hProjection := fiveSectorLegacyProjector_eq_l2OfOrthogonalProduct
      coordinates resolution decomposition_eq
        (fivePhysicalSectorL2SlotEquiv.symm sector)
    rw [fiveSectorL2HilbertCoordinatesOfOrthogonalProduct_projector] at hProjection
    simpa using hProjection
  reverse_projection_norm_map := reverse_projection_norm_map

/-- The represented reverse pullback commutes with the orthogonal resolution. -/
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
    (metric :
      LinearNaturalRepresentationAdmissibleIsomorphismFamilySectorMetricData
        representation coordinates refinement pullback isomorphisms resolution)
    (first second : Real) (sector : FiveSectorSlot) (state : State) :
    isomorphisms.reverseLinear first second
        (resolution.projection sector state) =
      resolution.projection sector
        (isomorphisms.reverseLinear first second state) := by
  rw [← metric.projection_eq sector,
    ← isomorphisms.reverse_source_agreement first second
      (coordinates.sectorProjector
        (fivePhysicalSectorL2SlotEquiv.symm sector) state),
    ← isomorphisms.reverse_source_agreement first second state]
  exact (pullback.source_commutes
    (isomorphisms.isomorphism first second).inv
    (fivePhysicalSectorL2SlotEquiv.symm sector) state).symm

/-- Sectorwise isometries and orthogonal Pythagoras imply global norm
preservation. -/
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
    (metric :
      LinearNaturalRepresentationAdmissibleIsomorphismFamilySectorMetricData
        representation coordinates refinement pullback isomorphisms resolution)
    (first second : Real) (state : State) :
    ‖isomorphisms.reverseLinear first second state‖ = ‖state‖ := by
  have hSq :
      ‖isomorphisms.reverseLinear first second state‖ ^ 2 = ‖state‖ ^ 2 := by
    calc
      ‖isomorphisms.reverseLinear first second state‖ ^ 2 =
          ∑ sector : FiveSectorSlot,
            ‖resolution.projection sector
              (isomorphisms.reverseLinear first second state)‖ ^ 2 :=
        fiveSectorProjection_norm_sq_sum resolution
          (isomorphisms.reverseLinear first second state)
      _ = ∑ sector : FiveSectorSlot,
            ‖isomorphisms.reverseLinear first second
              (resolution.projection sector state)‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro sector _
        rw [metric.reverse_projection_commutes representation coordinates
          refinement pullback isomorphisms resolution first second sector state]
      _ = ∑ sector : FiveSectorSlot,
            ‖resolution.projection sector state‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro sector _
        rw [metric.reverse_projection_norm_map first second sector state]
      _ = ‖state‖ ^ 2 :=
        (fiveSectorProjection_norm_sq_sum resolution state).symm
  nlinarith [norm_nonneg (isomorphisms.reverseLinear first second state),
    norm_nonneg state]

/-- The sectorwise certificate assembles into the global inner-product
certificate. -/
def toMetricData
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
    (metric :
      LinearNaturalRepresentationAdmissibleIsomorphismFamilySectorMetricData
        representation coordinates refinement pullback isomorphisms resolution) :
    LinearNaturalRepresentationAdmissibleIsomorphismFamilyMetricData
      representation coordinates refinement pullback isomorphisms where
  reverse_inner_map := by
    intro first second firstState secondState
    exact (LinearMap.norm_map_iff_inner_map_map
      (isomorphisms.reverseLinear first second)).mp
        (metric.reverse_norm_map representation coordinates refinement pullback
          isomorphisms resolution first second) firstState secondState

end LinearNaturalRepresentationAdmissibleIsomorphismFamilySectorMetricData

end
end P0EFTJanusProgramPLinearNaturalRepresentationAdmissibleIsomorphismFamilySectorMetric4D
end JanusFormal
