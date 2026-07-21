import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkGlobalOrientedBoundaryCurrent4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkGenuineGreenCurrentMeasuredStokes4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutOpenScalarStokes4D

/-!
# Global Green--Stokes assembly on the canonical cut-open Janus bulk

This file closes the canonical assembly gap between four objects that were
already constructed separately:

* the genuine global cut bulk with its exact manifold boundary;
* the pushed bulk divergence vector measure;
* the descended Green current on the orientation-double boundary;
* the genuine intrinsic normal flux on the canonical latitude collar.

The resulting theorem is a global statement on the exact cut-bulk boundary,
not merely a collar-coordinate identity.  It remains specific to the canonical
cut and canonical latitude parametrization; it is not a general Stokes theorem
for arbitrary Lorentz metrics, arbitrary vector currents or arbitrary
stratified boundaries.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutBulkGlobalGreenStokes4D

set_option autoImplicit false
noncomputable section

open Set MeasureTheory
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalLatitudeScalarGreenCurrent4D
open P0EFTJanusMappingTorusCutBoundaryTwoSheetOrientedCurrentIntegral4D
open P0EFTJanusMappingTorusCutBulkCanonicalDivergenceMeasure4D
open P0EFTJanusMappingTorusCutBulkGenuineGreenCurrentMeasuredStokes4D
open P0EFTJanusMappingTorusCanonicalLatitudeCenteredCutoffDivergenceIntrinsicMetricBridge4D
open P0EFTJanusMappingTorusCanonicalLatitudePTFixedOrientedFlux4D
open P0EFTJanusMappingTorusCanonicalLatitudePTFixedProjection4D
open P0EFTJanusMappingTorusCutOpenScalarStokes4D
open P0EFTJanusMappingTorusCutBulkGlobalBoundaryMeasure4D
open P0EFTJanusMappingTorusCutBulkGlobalOrientedBoundaryCurrent4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Canonical measured Green--Stokes theorem on the genuine global cut bulk.
The boundary term is evaluated on the exact manifold-boundary subtype. -/
theorem cutBulkGlobalMeasuredGreenStokes
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real) :
    2 * cutBulkCanonicalDivergenceMeasure period hPeriod massSquared
          field test Set.univ =
      -cutBulkGlobalOrientedScalarCurrentIntegral period hPeriod field test := by
  calc
    2 * cutBulkCanonicalDivergenceMeasure period hPeriod massSquared
          field test Set.univ =
        -twoSheetOrientedScalarCurrentIntegral period hPeriod field test :=
      two_mul_cutBulkCanonicalDivergenceMeasure_univ_eq_neg_boundary
        period hPeriod massSquared field test
    _ = -cutBulkGlobalOrientedScalarCurrentIntegral period hPeriod field test := by
      rw [cutBulkGlobalOrientedScalarCurrentIntegral_eq_twoSheet]

/-- The exact global boundary functional is twice the genuine intrinsic normal
flux through the first throat sheet. -/
theorem cutBulkGlobalOrientedBoundaryCurrent_eq_two_mul_genuineFlux
    (field test : SmoothQuotientField period hPeriod Real) :
    cutBulkGlobalOrientedScalarCurrentIntegral period hPeriod field test =
      2 * canonicalMeasuredCutBulkIntrinsicGreenNormalFlux period hPeriod
        field test 0 := by
  calc
    cutBulkGlobalOrientedScalarCurrentIntegral period hPeriod field test =
        twoSheetOrientedScalarCurrentIntegral period hPeriod field test :=
      cutBulkGlobalOrientedScalarCurrentIntegral_eq_twoSheet
        period hPeriod field test
    _ = 2 * canonicalMeasuredCutBulkIntrinsicGreenNormalFlux period hPeriod
          field test 0 :=
      twoSheetOrientedScalarCurrentIntegral_eq_two_mul_genuineFlux
        period hPeriod field test

/-- Equivalent normal-flux form of the global measured theorem. -/
theorem cutBulkGlobalMeasuredGreenStokes_eq_genuineFlux
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real) :
    2 * cutBulkCanonicalDivergenceMeasure period hPeriod massSquared
          field test Set.univ =
      -(2 * canonicalMeasuredCutBulkIntrinsicGreenNormalFlux period hPeriod
        field test 0) := by
  rw [cutBulkGlobalMeasuredGreenStokes,
    cutBulkGlobalOrientedBoundaryCurrent_eq_two_mul_genuineFlux]

/-- In the Euler sector, the complete metric-volume formula is equivalent to
vanishing of the exact global oriented boundary period. -/
theorem cutBulkGlobalMetricGreenStokes_iff_orientedBoundary_zero
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real)
    (hField : CanonicalLatitudeScalarEulerSolution period hPeriod massSquared field)
    (hTest : CanonicalLatitudeScalarEulerSolution period hPeriod massSquared test) :
    (2 * canonicalLatitudeCenteredMetricCutoffDivergenceIntegral period hPeriod
          massSquared field test =
        -cutBulkGlobalOrientedScalarCurrentIntegral period hPeriod field test) ↔
      cutBulkGlobalOrientedScalarCurrentIntegral period hPeriod field test = 0 := by
  rw [cutBulkGlobalOrientedScalarCurrentIntegral_eq_twoSheet]
  exact cutOpenScalarMetricGreenStokes_iff_orientedPeriod_zero
    period hPeriod massSquared field test hField hTest

/-- PT-fixed scalar pairs have zero oriented current on the exact global
boundary. -/
theorem cutBulkGlobalOrientedBoundaryCurrent_zero_of_ptFixed
    (field test : SmoothQuotientField period hPeriod Real)
    (hFieldPT : CanonicalLatitudeScalarPTFixed period hPeriod field)
    (hTestPT : CanonicalLatitudeScalarPTFixed period hPeriod test) :
    cutBulkGlobalOrientedScalarCurrentIntegral period hPeriod field test = 0 := by
  rw [cutBulkGlobalOrientedScalarCurrentIntegral_eq_twoSheet]
  exact twoSheetOrientedFlux_zero_of_ptFixed
    period hPeriod field test hFieldPT hTestPT

/-- The canonical bulk divergence measure has zero total mass in the PT-fixed
sector.  No Euler equation is needed for this cutoff-current statement. -/
theorem cutBulkGlobalDivergenceMeasure_zero_of_ptFixed
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real)
    (hFieldPT : CanonicalLatitudeScalarPTFixed period hPeriod field)
    (hTestPT : CanonicalLatitudeScalarPTFixed period hPeriod test) :
    2 * cutBulkCanonicalDivergenceMeasure period hPeriod massSquared
          field test Set.univ = 0 := by
  calc
    2 * cutBulkCanonicalDivergenceMeasure period hPeriod massSquared
          field test Set.univ =
        -cutBulkGlobalOrientedScalarCurrentIntegral period hPeriod field test :=
      cutBulkGlobalMeasuredGreenStokes period hPeriod massSquared field test
    _ = 0 := by
      rw [cutBulkGlobalOrientedBoundaryCurrent_zero_of_ptFixed
        period hPeriod field test hFieldPT hTestPT, neg_zero]

/-- The complete metric Green--Stokes formula on the exact global boundary in
the PT-fixed Euler sector. -/
theorem cutBulkGlobalMetricGreenStokes_of_ptFixed
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real)
    (hFieldEuler : CanonicalLatitudeScalarEulerSolution period hPeriod massSquared field)
    (hTestEuler : CanonicalLatitudeScalarEulerSolution period hPeriod massSquared test)
    (hFieldPT : CanonicalLatitudeScalarPTFixed period hPeriod field)
    (hTestPT : CanonicalLatitudeScalarPTFixed period hPeriod test) :
    2 * canonicalLatitudeCenteredMetricCutoffDivergenceIntegral period hPeriod
          massSquared field test =
      -cutBulkGlobalOrientedScalarCurrentIntegral period hPeriod field test := by
  rw [cutBulkGlobalOrientedScalarCurrentIntegral_eq_twoSheet]
  exact cutOpenScalarMetricGreenStokes_of_ptFixed period hPeriod massSquared
    field test hFieldEuler hTestEuler hFieldPT hTestPT

/-- In the PT-fixed Euler sector the metric-volume divergence integral itself
vanishes. -/
theorem cutBulkGlobalMetricDivergence_zero_of_ptFixed
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real)
    (hFieldEuler : CanonicalLatitudeScalarEulerSolution period hPeriod massSquared field)
    (hTestEuler : CanonicalLatitudeScalarEulerSolution period hPeriod massSquared test)
    (hFieldPT : CanonicalLatitudeScalarPTFixed period hPeriod field)
    (hTestPT : CanonicalLatitudeScalarPTFixed period hPeriod test) :
    2 * canonicalLatitudeCenteredMetricCutoffDivergenceIntegral period hPeriod
          massSquared field test = 0 := by
  calc
    2 * canonicalLatitudeCenteredMetricCutoffDivergenceIntegral period hPeriod
          massSquared field test =
        -cutBulkGlobalOrientedScalarCurrentIntegral period hPeriod field test :=
      cutBulkGlobalMetricGreenStokes_of_ptFixed period hPeriod massSquared
        field test hFieldEuler hTestEuler hFieldPT hTestPT
    _ = 0 := by
      rw [cutBulkGlobalOrientedBoundaryCurrent_zero_of_ptFixed
        period hPeriod field test hFieldPT hTestPT, neg_zero]

/-- Every Euler pair has a canonical PT-even projection whose metric Green--
Stokes formula is expressed on the exact global boundary. -/
theorem cutBulkGlobalMetricGreenStokes_of_ptEvenProjection
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real)
    (hField : CanonicalLatitudeScalarEulerSolution period hPeriod massSquared field)
    (hTest : CanonicalLatitudeScalarEulerSolution period hPeriod massSquared test) :
    2 * canonicalLatitudeCenteredMetricCutoffDivergenceIntegral period hPeriod
          massSquared
          (canonicalScalarPTEvenProjection period hPeriod field)
          (canonicalScalarPTEvenProjection period hPeriod test) =
      -cutBulkGlobalOrientedScalarCurrentIntegral period hPeriod
          (canonicalScalarPTEvenProjection period hPeriod field)
          (canonicalScalarPTEvenProjection period hPeriod test) := by
  rw [cutBulkGlobalOrientedScalarCurrentIntegral_eq_twoSheet]
  exact cutOpenScalarMetricGreenStokes_of_ptEvenProjection
    period hPeriod massSquared field test hField hTest

/-- Homogeneous Dirichlet Euler data also satisfy the exact global-boundary
metric Green--Stokes formula, without a PT hypothesis. -/
theorem cutBulkGlobalMetricGreenStokes_of_dirichletEuler
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real)
    (hField : CanonicalLatitudeScalarDirichletEulerSolution period hPeriod
      massSquared field)
    (hTest : CanonicalLatitudeScalarDirichletEulerSolution period hPeriod
      massSquared test) :
    2 * canonicalLatitudeCenteredMetricCutoffDivergenceIntegral period hPeriod
          massSquared field test =
      -cutBulkGlobalOrientedScalarCurrentIntegral period hPeriod field test := by
  rw [cutBulkGlobalOrientedBoundaryCurrent_eq_two_mul_genuineFlux]
  exact cutOpenScalarMetricGreenStokes_of_dirichletEuler
    period hPeriod massSquared field test hField hTest

/-- The exact global oriented boundary period vanishes for homogeneous
Dirichlet Euler pairs. -/
theorem cutBulkGlobalOrientedBoundaryCurrent_zero_of_dirichletEuler
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real)
    (hField : CanonicalLatitudeScalarDirichletEulerSolution period hPeriod
      massSquared field)
    (hTest : CanonicalLatitudeScalarDirichletEulerSolution period hPeriod
      massSquared test) :
    cutBulkGlobalOrientedScalarCurrentIntegral period hPeriod field test = 0 := by
  calc
    cutBulkGlobalOrientedScalarCurrentIntegral period hPeriod field test =
        2 * canonicalMeasuredCutBulkIntrinsicGreenNormalFlux period hPeriod
          field test 0 :=
      cutBulkGlobalOrientedBoundaryCurrent_eq_two_mul_genuineFlux
        period hPeriod field test
    _ = 2 * canonicalLatitudeMeasuredScalarGreenCurrent period hPeriod
          field test 0 := by
      rw [canonicalMeasuredCutBulkIntrinsicGreenNormalFlux_eq_greenCurrent
        period hPeriod field test 0 (by norm_num)]
    _ = 0 := by
      rw [canonicalLatitudeMeasuredScalarGreenCurrent_zero_of_dirichletEuler
        period hPeriod massSquared field test hField hTest 0]
      ring

/-- The complete metric-volume divergence integral vanishes for homogeneous
Dirichlet Euler pairs. -/
theorem cutBulkGlobalMetricDivergence_zero_of_dirichletEuler
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real)
    (hField : CanonicalLatitudeScalarDirichletEulerSolution period hPeriod
      massSquared field)
    (hTest : CanonicalLatitudeScalarDirichletEulerSolution period hPeriod
      massSquared test) :
    2 * canonicalLatitudeCenteredMetricCutoffDivergenceIntegral period hPeriod
          massSquared field test = 0 := by
  calc
    2 * canonicalLatitudeCenteredMetricCutoffDivergenceIntegral period hPeriod
          massSquared field test =
        -cutBulkGlobalOrientedScalarCurrentIntegral period hPeriod field test :=
      cutBulkGlobalMetricGreenStokes_of_dirichletEuler period hPeriod
        massSquared field test hField hTest
    _ = 0 := by
      rw [cutBulkGlobalOrientedBoundaryCurrent_zero_of_dirichletEuler
        period hPeriod massSquared field test hField hTest, neg_zero]

/-- Structural closure certificate for the canonical global Green--Stokes
assembly. -/
theorem cutBulkGlobalGreenStokes_certificate
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real) :
    2 * cutBulkCanonicalDivergenceMeasure period hPeriod massSquared
          field test Set.univ =
        -cutBulkGlobalOrientedScalarCurrentIntegral period hPeriod field test ∧
      cutBulkGlobalOrientedScalarCurrentIntegral period hPeriod field test =
        2 * canonicalMeasuredCutBulkIntrinsicGreenNormalFlux period hPeriod
          field test 0 ∧
      (∫ boundary,
          cutBulkGlobalBoundaryScalarCurrent period hPeriod field test boundary
          ∂cutBulkGlobalBoundaryCanonicalMeasure period hPeriod) = 0 := by
  exact ⟨cutBulkGlobalMeasuredGreenStokes period hPeriod massSquared field test,
    cutBulkGlobalOrientedBoundaryCurrent_eq_two_mul_genuineFlux
      period hPeriod field test,
    cutBulkGlobalBoundaryScalarCurrent_unorientedIntegral_eq_zero
      period hPeriod field test⟩

end
end P0EFTJanusMappingTorusCutBulkGlobalGreenStokes4D
end JanusFormal
