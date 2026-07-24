import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBoundaryScalarCauchyL24D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkGlobalGreenStokes4D

/-!
# Global cut-bulk Green form from the concrete scalar Cauchy trace

The exact global cut-bulk boundary is homeomorphic to the orientation-double
throat.  Transporting the concrete value and normal traces through that
homeomorphism gives scalar boundary data directly on the manifold-boundary
subtype.

The descended global Green current is pointwise the symplectic expression

`value(field) * normal(test) - normal(field) * value(test)`.

The global oriented current is twice the first-sheet integral of this pairing,
and the canonical pushed divergence measure is its negative.  This closes the
geometric boundary half of the physical Hilbert Green bridge without introducing
an abstract normal-trace placeholder.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutBulkGlobalScalarCauchyGreen4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff
open MeasureTheory Set Topology
open P0EFTJanusGaussianNormalEmbeddedHypersurface
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCutThroatBoundaryDoubleCover4D
open P0EFTJanusMappingTorusCutThroatSmoothFiniteCollar4D
open P0EFTJanusMappingTorusCutBoundaryScalarCauchyTrace4D
open P0EFTJanusMappingTorusCutBoundaryFirstSheetCurrentBridge4D
open P0EFTJanusMappingTorusCutBulkGlobalChartedSpace4D
open P0EFTJanusMappingTorusCutBoundaryGlobalHomeomorph4D
open P0EFTJanusMappingTorusCutBulkGlobalBoundaryMeasure4D
open P0EFTJanusMappingTorusCutBulkGlobalOrientedBoundaryCurrent4D
open P0EFTJanusMappingTorusCutBulkCanonicalDivergenceMeasure4D
open P0EFTJanusMappingTorusCutBulkGlobalGreenStokes4D

variable (period : Real) (hPeriod : period ≠ 0)

local instance cutBoundaryChartedSpace :
    ChartedSpace ThroatCoverModel (CutThroatBoundary period hPeriod) :=
  cutThroatBoundaryChartedSpace period hPeriod

local instance cutBoundaryIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (CutThroatBoundary period hPeriod) :=
  cutThroatBoundary_isManifold period hPeriod

/-- Scalar value trace transported to the exact global manifold boundary. -/
def cutBulkGlobalScalarValueTrace
    (field : SmoothQuotientField period hPeriod Real)
    (boundary : CutBulkGlobalBoundary period hPeriod) : Real := by
  letI := cutBulkGlobalChartedSpace period hPeriod
  exact cutBoundaryScalarValueTrace period hPeriod field
    ((cutBoundaryGlobalBoundaryHomeomorph period hPeriod).symm boundary)

/-- Scalar normal trace transported to the exact global manifold boundary. -/
def cutBulkGlobalScalarNormalTrace
    (field : SmoothQuotientField period hPeriod Real)
    (boundary : CutBulkGlobalBoundary period hPeriod) : Real := by
  letI := cutBulkGlobalChartedSpace period hPeriod
  exact cutBoundaryScalarNormalTrace period hPeriod field
    ((cutBoundaryGlobalBoundaryHomeomorph period hPeriod).symm boundary)

/-- Value trace on the exact global boundary is continuous. -/
theorem cutBulkGlobalScalarValueTrace_continuous
    (field : SmoothQuotientField period hPeriod Real) :
    Continuous (cutBulkGlobalScalarValueTrace period hPeriod field) := by
  letI := cutBulkGlobalChartedSpace period hPeriod
  exact (cutBoundaryScalarValueTrace_continuous period hPeriod field).comp
    (cutBoundaryGlobalBoundaryHomeomorph period hPeriod).symm.continuous

/-- Normal trace on the exact global boundary is continuous. -/
theorem cutBulkGlobalScalarNormalTrace_continuous
    (field : SmoothQuotientField period hPeriod Real) :
    Continuous (cutBulkGlobalScalarNormalTrace period hPeriod field) := by
  letI := cutBulkGlobalChartedSpace period hPeriod
  exact (cutBoundaryScalarNormalTrace_continuous period hPeriod field).comp
    (cutBoundaryGlobalBoundaryHomeomorph period hPeriod).symm.continuous

/-- Pointwise Green current on the exact global boundary in Cauchy data. -/
theorem cutBulkGlobalBoundaryScalarCurrent_eq_cauchyPairing
    (field test : SmoothQuotientField period hPeriod Real)
    (boundary : CutBulkGlobalBoundary period hPeriod) :
    cutBulkGlobalBoundaryScalarCurrent period hPeriod field test boundary =
      cutBulkGlobalScalarValueTrace period hPeriod field boundary *
          cutBulkGlobalScalarNormalTrace period hPeriod test boundary -
        cutBulkGlobalScalarNormalTrace period hPeriod field boundary *
          cutBulkGlobalScalarValueTrace period hPeriod test boundary := by
  letI := cutBulkGlobalChartedSpace period hPeriod
  exact cutBoundaryScalarCurrent_eq_cauchyPairing period hPeriod field test
    ((cutBoundaryGlobalBoundaryHomeomorph period hPeriod).symm boundary)

/-- First-sheet Cauchy symplectic pairing. -/
def cutBulkGlobalFirstSheetScalarCauchyPairing
    (field test : SmoothQuotientField period hPeriod Real) : Real :=
  ∫ base : CanonicalLatitudeBase,
    (cutBulkGlobalScalarValueTrace period hPeriod field
        (canonicalLatitudeCutBulkGlobalBoundaryFirstLift period hPeriod base) *
      cutBulkGlobalScalarNormalTrace period hPeriod test
        (canonicalLatitudeCutBulkGlobalBoundaryFirstLift period hPeriod base) -
      cutBulkGlobalScalarNormalTrace period hPeriod field
        (canonicalLatitudeCutBulkGlobalBoundaryFirstLift period hPeriod base) *
      cutBulkGlobalScalarValueTrace period hPeriod test
        (canonicalLatitudeCutBulkGlobalBoundaryFirstLift period hPeriod base))
    ∂canonicalLatitudeBaseMeasure period

/-- The first-sheet Cauchy pairing is the first-sheet Green-current integral. -/
theorem cutBulkGlobalFirstSheetScalarCauchyPairing_eq_current
    (field test : SmoothQuotientField period hPeriod Real) :
    cutBulkGlobalFirstSheetScalarCauchyPairing period hPeriod field test =
      ∫ base : CanonicalLatitudeBase,
        cutBulkGlobalBoundaryScalarCurrent period hPeriod field test
          (canonicalLatitudeCutBulkGlobalBoundaryFirstLift period hPeriod base)
        ∂canonicalLatitudeBaseMeasure period := by
  unfold cutBulkGlobalFirstSheetScalarCauchyPairing
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun base =>
    (cutBulkGlobalBoundaryScalarCurrent_eq_cauchyPairing
      period hPeriod field test
      (canonicalLatitudeCutBulkGlobalBoundaryFirstLift
        period hPeriod base)).symm

/-- The exact global oriented current is twice the first-sheet Cauchy pairing. -/
theorem cutBulkGlobalOrientedBoundaryCurrent_eq_two_mul_cauchyPairing
    (field test : SmoothQuotientField period hPeriod Real) :
    cutBulkGlobalOrientedScalarCurrentIntegral period hPeriod field test =
      2 * cutBulkGlobalFirstSheetScalarCauchyPairing
        period hPeriod field test := by
  rw [cutBulkGlobalOrientedScalarCurrentIntegral_eq_two_mul_first]
  congr 1
  unfold P0EFTJanusMappingTorusCutBoundaryOrientedFluxSign4D.orientedCutLiftFlux
  simp only [NormalOrientation.sign, one_mul]
  exact (cutBulkGlobalFirstSheetScalarCauchyPairing_eq_current
    period hPeriod field test).symm

/-- Physical Green--Stokes identity in concrete Cauchy variables. -/
theorem cutBulkCanonicalDivergenceMeasure_eq_neg_cauchyPairing
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real) :
    cutBulkCanonicalDivergenceMeasure period hPeriod massSquared
        field test Set.univ =
      -cutBulkGlobalFirstSheetScalarCauchyPairing
        period hPeriod field test := by
  have hStokes := cutBulkGlobalMeasuredGreenStokes
    period hPeriod massSquared field test
  rw [cutBulkGlobalOrientedBoundaryCurrent_eq_two_mul_cauchyPairing]
    at hStokes
  linarith

/-- Direct latitude-coordinate form of the same physical boundary pairing. -/
theorem cutBulkGlobalFirstSheetScalarCauchyPairing_eq_latitude
    (field test : SmoothQuotientField period hPeriod Real) :
    cutBulkGlobalFirstSheetScalarCauchyPairing period hPeriod field test =
      ∫ base : CanonicalLatitudeBase,
        (canonicalLatitudeValue period hPeriod field base 0 *
            canonicalLatitudeDerivative period hPeriod test base 0 -
          canonicalLatitudeDerivative period hPeriod field base 0 *
            canonicalLatitudeValue period hPeriod test base 0)
        ∂canonicalLatitudeBaseMeasure period := by
  unfold cutBulkGlobalFirstSheetScalarCauchyPairing
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun base => by
    letI := cutBulkGlobalChartedSpace period hPeriod
    simp only [cutBulkGlobalScalarValueTrace,
      cutBulkGlobalScalarNormalTrace,
      canonicalLatitudeCutBulkGlobalBoundaryFirstLift,
      Homeomorph.symm_apply_apply]
    rw [cutBoundaryScalarValueTrace_firstLift,
      cutBoundaryScalarNormalTrace_firstLift,
      cutBoundaryScalarNormalTrace_firstLift,
      cutBoundaryScalarValueTrace_firstLift]

/-- Concrete global Cauchy--Green certificate. -/
theorem cutBulkGlobalScalarCauchyGreen_certificate
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real) :
    (∀ boundary : CutBulkGlobalBoundary period hPeriod,
      cutBulkGlobalBoundaryScalarCurrent period hPeriod field test boundary =
        cutBulkGlobalScalarValueTrace period hPeriod field boundary *
            cutBulkGlobalScalarNormalTrace period hPeriod test boundary -
          cutBulkGlobalScalarNormalTrace period hPeriod field boundary *
            cutBulkGlobalScalarValueTrace period hPeriod test boundary) ∧
      cutBulkGlobalOrientedScalarCurrentIntegral period hPeriod field test =
        2 * cutBulkGlobalFirstSheetScalarCauchyPairing
          period hPeriod field test ∧
      cutBulkCanonicalDivergenceMeasure period hPeriod massSquared
          field test Set.univ =
        -cutBulkGlobalFirstSheetScalarCauchyPairing
          period hPeriod field test :=
  ⟨cutBulkGlobalBoundaryScalarCurrent_eq_cauchyPairing
      period hPeriod field test,
    cutBulkGlobalOrientedBoundaryCurrent_eq_two_mul_cauchyPairing
      period hPeriod field test,
    cutBulkCanonicalDivergenceMeasure_eq_neg_cauchyPairing
      period hPeriod massSquared field test⟩

end
end P0EFTJanusMappingTorusCutBulkGlobalScalarCauchyGreen4D
end JanusFormal
