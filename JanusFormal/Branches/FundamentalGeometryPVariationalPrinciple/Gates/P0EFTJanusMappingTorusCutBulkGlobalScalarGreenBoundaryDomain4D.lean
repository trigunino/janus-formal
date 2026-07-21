import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarSeparatedBoundaryCondition4D

/-!
# Green-isotropic scalar boundary domains on the global cut bulk

This file packages a boundary predicate together with the exact condition that
its global Green boundary form vanish pairwise.  The canonical separated
Dirichlet, Neumann and real Robin conditions, as well as the PT-fixed sector,
instantiate the package.

The global Green--Stokes theorem then shows that every such condition kills the
total pushed divergence.  In the latitude Euler sector it also kills the exact
metric-volume skew pairing.  This is formal self-adjointness at the smooth
Green-identity level, not closedness, maximality, compact resolvent or a
self-adjoint unbounded-operator theorem.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutBulkGlobalScalarGreenBoundaryDomain4D

set_option autoImplicit false
noncomputable section

open Set MeasureTheory
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalLatitudeScalarGreenCurrent4D
open P0EFTJanusMappingTorusCutBulkCanonicalDivergenceMeasure4D
open P0EFTJanusMappingTorusCanonicalLatitudeCenteredCutoffDivergenceIntrinsicMetricBridge4D
open P0EFTJanusMappingTorusCanonicalLatitudePTFixedOrientedFlux4D
open P0EFTJanusMappingTorusCutBulkGlobalOrientedBoundaryCurrent4D
open P0EFTJanusMappingTorusCutBulkGlobalGreenStokes4D
open P0EFTJanusMappingTorusCutBulkGlobalScalarBoundaryForm4D
open P0EFTJanusMappingTorusScalarSeparatedBoundaryCondition4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- A smooth scalar boundary predicate whose exact global Green form vanishes
on every pair of admitted fields. -/
structure CanonicalCutBulkScalarGreenBoundaryCondition where
  admits : SmoothQuotientField period hPeriod Real → Prop
  green_isotropic : ∀ (field test : SmoothQuotientField period hPeriod Real),
    admits field → admits test →
      cutBulkGlobalScalarBoundaryGreenForm period hPeriod field test = 0

/-- Every nondegenerate separated real boundary line defines a Green-isotropic
boundary condition. -/
def separatedScalarGreenBoundaryCondition
    (valueCoefficient normalCoefficient : CanonicalLatitudeBase → Real)
    (hNondegenerate : CanonicalLatitudeScalarSeparatedBoundaryNondegenerate
      valueCoefficient normalCoefficient) :
    CanonicalCutBulkScalarGreenBoundaryCondition period hPeriod where
  admits := CanonicalLatitudeScalarSeparatedBoundaryCondition period hPeriod
    valueCoefficient normalCoefficient
  green_isotropic := fun field test hField hTest =>
    cutBulkGlobalScalarBoundaryGreenForm_eq_zero_of_separated
      period hPeriod valueCoefficient normalCoefficient hNondegenerate
        field test hField hTest

/-- Canonical Dirichlet Green boundary condition. -/
def dirichletScalarGreenBoundaryCondition :
    CanonicalCutBulkScalarGreenBoundaryCondition period hPeriod :=
  separatedScalarGreenBoundaryCondition period hPeriod
    (fun _ => 1) (fun _ => 0) (by
      intro base
      exact Or.inl one_ne_zero)

/-- Canonical Neumann Green boundary condition. -/
def neumannScalarGreenBoundaryCondition :
    CanonicalCutBulkScalarGreenBoundaryCondition period hPeriod :=
  separatedScalarGreenBoundaryCondition period hPeriod
    (fun _ => 0) (fun _ => 1) (by
      intro base
      exact Or.inr one_ne_zero)

/-- Canonical real Robin Green boundary condition with a possibly
base-dependent coefficient. -/
def robinScalarGreenBoundaryCondition
    (coefficient : CanonicalLatitudeBase → Real) :
    CanonicalCutBulkScalarGreenBoundaryCondition period hPeriod :=
  separatedScalarGreenBoundaryCondition period hPeriod
    (fun base => -coefficient base) (fun _ => 1) (by
      intro base
      exact Or.inr one_ne_zero)

/-- PT-fixed scalars form a second Green-isotropic sector.  Unlike the separated
conditions, isotropy here follows after integration from the exact PT-odd
boundary-current law. -/
def ptFixedScalarGreenBoundaryCondition :
    CanonicalCutBulkScalarGreenBoundaryCondition period hPeriod where
  admits := CanonicalLatitudeScalarPTFixed period hPeriod
  green_isotropic := by
    intro field test hField hTest
    unfold cutBulkGlobalScalarBoundaryGreenForm
    exact cutBulkGlobalOrientedBoundaryCurrent_zero_of_ptFixed
      period hPeriod field test hField hTest

/-- A Green-isotropic boundary condition forces the total pushed cut-bulk
divergence measure to vanish.  No Euler equation is required for this exact
cutoff-current identity. -/
theorem cutBulkCanonicalDivergenceMeasure_univ_eq_zero_of_greenBoundaryCondition
    (massSquared : Real)
    (condition : CanonicalCutBulkScalarGreenBoundaryCondition period hPeriod)
    (field test : SmoothQuotientField period hPeriod Real)
    (hField : condition.admits field) (hTest : condition.admits test) :
    cutBulkCanonicalDivergenceMeasure period hPeriod massSquared field test Set.univ = 0 := by
  have hBoundary := condition.green_isotropic field test hField hTest
  unfold cutBulkGlobalScalarBoundaryGreenForm at hBoundary
  have hTwice :
      2 * cutBulkCanonicalDivergenceMeasure period hPeriod massSquared
          field test Set.univ = 0 := by
    calc
      2 * cutBulkCanonicalDivergenceMeasure period hPeriod massSquared
            field test Set.univ =
          -cutBulkGlobalOrientedScalarCurrentIntegral period hPeriod field test :=
        cutBulkGlobalMeasuredGreenStokes period hPeriod massSquared field test
      _ = 0 := by rw [hBoundary, neg_zero]
  linarith

/-- In the latitude Euler sector, every Green-isotropic boundary condition
closes the exact metric-volume Green--Stokes formula on the genuine global
boundary. -/
theorem cutBulkGlobalMetricGreenStokes_of_greenBoundaryCondition
    (massSquared : Real)
    (condition : CanonicalCutBulkScalarGreenBoundaryCondition period hPeriod)
    (field test : SmoothQuotientField period hPeriod Real)
    (hFieldEuler : CanonicalLatitudeScalarEulerSolution period hPeriod
      massSquared field)
    (hTestEuler : CanonicalLatitudeScalarEulerSolution period hPeriod
      massSquared test)
    (hField : condition.admits field) (hTest : condition.admits test) :
    2 * canonicalLatitudeCenteredMetricCutoffDivergenceIntegral period hPeriod
          massSquared field test =
      -cutBulkGlobalOrientedScalarCurrentIntegral period hPeriod field test := by
  apply (cutBulkGlobalMetricGreenStokes_iff_orientedBoundary_zero
    period hPeriod massSquared field test hFieldEuler hTestEuler).2
  have hBoundary := condition.green_isotropic field test hField hTest
  exact hBoundary

/-- Formal symmetry of the metric Euler pairing: its antisymmetric Green term
vanishes on every common Green-isotropic boundary condition. -/
theorem canonicalLatitudeCenteredMetricCutoffDivergenceIntegral_eq_zero_of_greenBoundaryCondition
    (massSquared : Real)
    (condition : CanonicalCutBulkScalarGreenBoundaryCondition period hPeriod)
    (field test : SmoothQuotientField period hPeriod Real)
    (hFieldEuler : CanonicalLatitudeScalarEulerSolution period hPeriod
      massSquared field)
    (hTestEuler : CanonicalLatitudeScalarEulerSolution period hPeriod
      massSquared test)
    (hField : condition.admits field) (hTest : condition.admits test) :
    canonicalLatitudeCenteredMetricCutoffDivergenceIntegral period hPeriod
      massSquared field test = 0 := by
  have hBoundary := condition.green_isotropic field test hField hTest
  unfold cutBulkGlobalScalarBoundaryGreenForm at hBoundary
  have hGreen := cutBulkGlobalMetricGreenStokes_of_greenBoundaryCondition
    period hPeriod massSquared condition field test hFieldEuler hTestEuler
      hField hTest
  rw [hBoundary, neg_zero] at hGreen
  linarith

/-- Full smooth Green-domain certificate. -/
theorem cutBulkGlobalScalarGreenBoundaryCondition_certificate
    (massSquared : Real)
    (condition : CanonicalCutBulkScalarGreenBoundaryCondition period hPeriod)
    (field test : SmoothQuotientField period hPeriod Real)
    (hFieldEuler : CanonicalLatitudeScalarEulerSolution period hPeriod
      massSquared field)
    (hTestEuler : CanonicalLatitudeScalarEulerSolution period hPeriod
      massSquared test)
    (hField : condition.admits field) (hTest : condition.admits test) :
    cutBulkGlobalScalarBoundaryGreenForm period hPeriod field test = 0 ∧
      cutBulkCanonicalDivergenceMeasure period hPeriod massSquared
          field test Set.univ = 0 ∧
      canonicalLatitudeCenteredMetricCutoffDivergenceIntegral period hPeriod
          massSquared field test = 0 := by
  exact ⟨condition.green_isotropic field test hField hTest,
    cutBulkCanonicalDivergenceMeasure_univ_eq_zero_of_greenBoundaryCondition
      period hPeriod massSquared condition field test hField hTest,
    canonicalLatitudeCenteredMetricCutoffDivergenceIntegral_eq_zero_of_greenBoundaryCondition
      period hPeriod massSquared condition field test hFieldEuler hTestEuler
        hField hTest⟩

/-- Dirichlet specialization of the generic formal-symmetry certificate. -/
theorem cutBulkGlobalDirichletScalarGreen_certificate
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real)
    (hFieldEuler : CanonicalLatitudeScalarEulerSolution period hPeriod
      massSquared field)
    (hTestEuler : CanonicalLatitudeScalarEulerSolution period hPeriod
      massSquared test)
    (hField : CanonicalLatitudeScalarDirichletBoundaryCondition period hPeriod field)
    (hTest : CanonicalLatitudeScalarDirichletBoundaryCondition period hPeriod test) :
    cutBulkGlobalScalarBoundaryGreenForm period hPeriod field test = 0 ∧
      cutBulkCanonicalDivergenceMeasure period hPeriod massSquared
          field test Set.univ = 0 ∧
      canonicalLatitudeCenteredMetricCutoffDivergenceIntegral period hPeriod
          massSquared field test = 0 :=
  cutBulkGlobalScalarGreenBoundaryCondition_certificate period hPeriod
    massSquared (dirichletScalarGreenBoundaryCondition period hPeriod)
      field test hFieldEuler hTestEuler hField hTest

/-- Neumann specialization of the generic formal-symmetry certificate. -/
theorem cutBulkGlobalNeumannScalarGreen_certificate
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real)
    (hFieldEuler : CanonicalLatitudeScalarEulerSolution period hPeriod
      massSquared field)
    (hTestEuler : CanonicalLatitudeScalarEulerSolution period hPeriod
      massSquared test)
    (hField : CanonicalLatitudeScalarNeumannBoundaryCondition period hPeriod field)
    (hTest : CanonicalLatitudeScalarNeumannBoundaryCondition period hPeriod test) :
    cutBulkGlobalScalarBoundaryGreenForm period hPeriod field test = 0 ∧
      cutBulkCanonicalDivergenceMeasure period hPeriod massSquared
          field test Set.univ = 0 ∧
      canonicalLatitudeCenteredMetricCutoffDivergenceIntegral period hPeriod
          massSquared field test = 0 :=
  cutBulkGlobalScalarGreenBoundaryCondition_certificate period hPeriod
    massSquared (neumannScalarGreenBoundaryCondition period hPeriod)
      field test hFieldEuler hTestEuler hField hTest

/-- Robin specialization for an arbitrary real boundary coefficient. -/
theorem cutBulkGlobalRobinScalarGreen_certificate
    (coefficient : CanonicalLatitudeBase → Real)
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real)
    (hFieldEuler : CanonicalLatitudeScalarEulerSolution period hPeriod
      massSquared field)
    (hTestEuler : CanonicalLatitudeScalarEulerSolution period hPeriod
      massSquared test)
    (hField : CanonicalLatitudeScalarRobinBoundaryCondition period hPeriod
      coefficient field)
    (hTest : CanonicalLatitudeScalarRobinBoundaryCondition period hPeriod
      coefficient test) :
    cutBulkGlobalScalarBoundaryGreenForm period hPeriod field test = 0 ∧
      cutBulkCanonicalDivergenceMeasure period hPeriod massSquared
          field test Set.univ = 0 ∧
      canonicalLatitudeCenteredMetricCutoffDivergenceIntegral period hPeriod
          massSquared field test = 0 :=
  cutBulkGlobalScalarGreenBoundaryCondition_certificate period hPeriod
    massSquared (robinScalarGreenBoundaryCondition period hPeriod coefficient)
      field test hFieldEuler hTestEuler hField hTest

/-- PT-fixed specialization. -/
theorem cutBulkGlobalPTFixedScalarGreen_certificate
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real)
    (hFieldEuler : CanonicalLatitudeScalarEulerSolution period hPeriod
      massSquared field)
    (hTestEuler : CanonicalLatitudeScalarEulerSolution period hPeriod
      massSquared test)
    (hField : CanonicalLatitudeScalarPTFixed period hPeriod field)
    (hTest : CanonicalLatitudeScalarPTFixed period hPeriod test) :
    cutBulkGlobalScalarBoundaryGreenForm period hPeriod field test = 0 ∧
      cutBulkCanonicalDivergenceMeasure period hPeriod massSquared
          field test Set.univ = 0 ∧
      canonicalLatitudeCenteredMetricCutoffDivergenceIntegral period hPeriod
          massSquared field test = 0 :=
  cutBulkGlobalScalarGreenBoundaryCondition_certificate period hPeriod
    massSquared (ptFixedScalarGreenBoundaryCondition period hPeriod)
      field test hFieldEuler hTestEuler hField hTest

end
end P0EFTJanusMappingTorusCutBulkGlobalScalarGreenBoundaryDomain4D
end JanusFormal
