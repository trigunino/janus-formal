import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiveSectorHilbertCoordinates4D

/-!
# Componentwise maps on the five-sector product

This purely algebraic helper packages a map acting independently on the five
right-associated physical coordinates.  If every component map fixes zero,
the total map commutes with every coordinate projector.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiveSectorComponentwiseProductMap4D

set_option autoImplicit false

open P0EFTJanusProgramPFiveSectorHilbertCoordinates4D

variable
  {Metric Abelian Matter Longitudinal Boundary : Type*}
  [Zero Metric] [Zero Abelian] [Zero Matter] [Zero Longitudinal] [Zero Boundary]

private abbrev ProductSpace :=
  FiveSectorProduct Metric Abelian Matter Longitudinal Boundary

/-- Coordinatewise five-sector map. -/
def fiveSectorComponentwiseMap
    (metric : Metric → Metric)
    (abelian : Abelian → Abelian)
    (matter : Matter → Matter)
    (longitudinal : Longitudinal → Longitudinal)
    (boundary : Boundary → Boundary) : ProductSpace → ProductSpace :=
  fun value =>
    (metric value.1,
      (abelian value.2.1,
        (matter value.2.2.1,
          (longitudinal value.2.2.2.1,
            boundary value.2.2.2.2))))

/-- Coordinate projector on the raw five-sector product. -/
def fiveSectorProductProjector : FivePhysicalSector → ProductSpace → ProductSpace
  | .metricDiffeomorphism => fun value =>
      (value.1, (0, (0, (0, 0))))
  | .abelianGauge => fun value =>
      (0, (value.2.1, (0, (0, 0))))
  | .primitiveSpinCMatter => fun value =>
      (0, (0, (value.2.2.1, (0, 0))))
  | .longitudinalLL => fun value =>
      (0, (0, (0, (value.2.2.2.1, 0))))
  | .boundaryFiniteBV => fun value =>
      (0, (0, (0, (0, value.2.2.2.2))))

/-- A componentwise map fixing zero in every component commutes with all five
raw coordinate projectors. -/
theorem fiveSectorComponentwiseMap_commutes_projector
    (metric : Metric → Metric)
    (abelian : Abelian → Abelian)
    (matter : Matter → Matter)
    (longitudinal : Longitudinal → Longitudinal)
    (boundary : Boundary → Boundary)
    (hMetric : metric 0 = 0)
    (hAbelian : abelian 0 = 0)
    (hMatter : matter 0 = 0)
    (hLongitudinal : longitudinal 0 = 0)
    (hBoundary : boundary 0 = 0)
    (sector : FivePhysicalSector) (value : ProductSpace) :
    fiveSectorComponentwiseMap metric abelian matter longitudinal boundary
        (fiveSectorProductProjector sector value) =
      fiveSectorProductProjector sector
        (fiveSectorComponentwiseMap metric abelian matter longitudinal boundary
          value) := by
  rcases value with ⟨m, a, s, l, b⟩
  cases sector <;>
    simp [fiveSectorComponentwiseMap, fiveSectorProductProjector,
      hMetric, hAbelian, hMatter, hLongitudinal, hBoundary]

end
end P0EFTJanusProgramPFiveSectorComponentwiseProductMap4D
end JanusFormal
