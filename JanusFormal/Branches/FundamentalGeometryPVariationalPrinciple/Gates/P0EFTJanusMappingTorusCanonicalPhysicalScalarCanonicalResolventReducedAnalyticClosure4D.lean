import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalReducedPDEClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarCompletedBoundaryTriplePositiveShiftedForm4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarCompletedBoundaryTripleSelfAdjointResolvent4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarFiniteRankRellich4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetRellichCompactness4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarCompletedBoundaryTripleEigenspace4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarCompletedBoundaryTripleFredholmAlternative4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarCompletedBoundaryTripleSemiboundedSpectrum4D

/-!
# Final scalar analytic closure from one real resolvent

A positive-square decomposition of one shifted form gives a bounded real
resolvent by Lax--Milgram.  Symmetry plus this real resolvent already proves
actual Hilbert self-adjointness, so maximal-adjoint graph regularity is not an
independent input.

Finite-rank Rellich approximation makes the reference resolvent compact.  The
final analytic package therefore contains only:

* the completed physical PDE boundary package;
* a closed Lagrangian boundary condition;
* one positive shifted-form decomposition;
* one finite-rank Rellich approximation scheme.

Self-adjointness, compact resolvent, Fredholm alternative, finite multiplicity,
orthogonality, spectral completeness and the lower spectral bound are derived.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalResolventReducedAnalyticClosure4D

set_option autoImplicit false
noncomputable section

open Set Topology MeasureTheory Module End
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetGreenCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetGreenCore4D.CanonicalPhysicalScalarFirstSheetGreenCoreData
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetRellichCompactness4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalReducedPDEClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFiniteRankRellich4D
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D
open P0EFTJanusMappingTorusScalarHilbertGreenCoreLagrangianDensity4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleResolvent4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleShiftedForm4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTriplePositiveShiftedForm4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleSelfAdjointResolvent4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleCompactSpectrum4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleEigenspace4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleFredholmAlternative4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleSemiboundedSpectrum4D

universe r

variable (period : Real) (hPeriod : period ≠ 0)
variable {massSquared : Real}
variable {Regularity : Type r}
  [NormedAddCommGroup Regularity] [NormedSpace Real Regularity]
  [CompleteSpace Regularity]

private abbrev BoundaryL2 := CanonicalPhysicalScalarFirstSheetL2 period

/-- Smallest current self-adjoint compact spectral input package. -/
structure CanonicalPhysicalScalarCanonicalResolventReducedAnalyticData
    (massSquared : Real) where
  boundary : CanonicalPhysicalScalarCanonicalReducedPDEData
    period hPeriod massSquared (Regularity := Regularity)
  condition : CanonicalScalarHilbertLagrangianBoundaryCondition
    (BoundaryL2 period)
  referenceParameter : Real
  shiftedPositiveDecomposition :
    boundary.triple.LagrangianShiftedPositiveDecompositionData
      condition referenceParameter
  finiteRankRellich : CanonicalPhysicalScalarFiniteRankRellichData
    period hPeriod

namespace CanonicalPhysicalScalarCanonicalResolventReducedAnalyticData

/-- Density of the selected realization. -/
theorem denseDomain
    (analytic : CanonicalPhysicalScalarCanonicalResolventReducedAnalyticData
      period hPeriod massSquared (Regularity := Regularity)) :
    DenseRange
      (analytic.boundary.triple.lagrangianInclusion analytic.condition) :=
  P0EFTJanusMappingTorusScalarHilbertGreenCoreLagrangianDensity4D.CanonicalScalarCompletedBoundaryTripleData.lagrangianInclusion_denseRange_of_minimalCore
    (analytic.boundary.triple period hPeriod) analytic.condition
    (analytic.boundary.completedInputs period hPeriod).minimalDense

/-- Shifted-form coercivity generated by the positive decomposition. -/
def shiftedFormCoercive
    (analytic : CanonicalPhysicalScalarCanonicalResolventReducedAnalyticData
      period hPeriod massSquared (Regularity := Regularity)) :
    analytic.boundary.triple.LagrangianShiftedFormCoerciveData
      analytic.condition analytic.referenceParameter :=
  analytic.shiftedPositiveDecomposition.toShiftedFormCoerciveData
    analytic.boundary.triple analytic.condition analytic.referenceParameter

/-- Direct coercive-surjective package. -/
def coerciveSurjectiveAt
    (analytic : CanonicalPhysicalScalarCanonicalResolventReducedAnalyticData
      period hPeriod massSquared (Regularity := Regularity)) :
    analytic.boundary.triple.LagrangianCoerciveSurjectiveAt
      analytic.condition analytic.referenceParameter :=
  (analytic.shiftedFormCoercive period hPeriod).toCoerciveSurjectiveAt
    analytic.boundary.triple analytic.condition analytic.referenceParameter
    (analytic.denseDomain period hPeriod)

/-- Bounded real reference resolvent. -/
noncomputable def boundedResolvent
    (analytic : CanonicalPhysicalScalarCanonicalResolventReducedAnalyticData
      period hPeriod massSquared (Regularity := Regularity)) :
    analytic.boundary.triple.LagrangianBoundedResolventAt
      analytic.condition analytic.referenceParameter :=
  (analytic.shiftedFormCoercive period hPeriod).boundedResolvent
    analytic.boundary.triple analytic.condition analytic.referenceParameter
    (analytic.denseDomain period hPeriod)

/-- Actual Hilbert self-adjointness follows directly from the real resolvent. -/
theorem actualAdjointDomain_eq
    (analytic : CanonicalPhysicalScalarCanonicalResolventReducedAnalyticData
      period hPeriod massSquared (Regularity := Regularity)) :
    analytic.boundary.triple.actualAdjointDomain analytic.condition =
      analytic.boundary.triple.realizationDomain analytic.condition :=
  analytic.boundary.triple
    |>.actualAdjointDomain_eq_realizationDomain_of_boundedResolvent
      analytic.condition analytic.referenceParameter
      (analytic.boundedResolvent period hPeriod)

/-- Physical Rellich compactness generated by finite-rank truncations. -/
theorem rellich
    (analytic : CanonicalPhysicalScalarCanonicalResolventReducedAnalyticData
      period hPeriod massSquared (Regularity := Regularity)) :
    PhysicalH1RellichCompactness period hPeriod :=
  analytic.finiteRankRellich.rellich

/-- Compact physical reference resolvent. -/
noncomputable def compactResolvent
    (analytic : CanonicalPhysicalScalarCanonicalResolventReducedAnalyticData
      period hPeriod massSquared (Regularity := Regularity)) :
    analytic.boundary.triple.LagrangianCompactResolventAt
      analytic.condition analytic.referenceParameter :=
  analytic.boundary.geometric.greenCore.compactResolventAt
    period hPeriod analytic.boundary.completedInputs analytic.condition
    analytic.referenceParameter
    (analytic.coerciveSurjectiveAt period hPeriod)
    (analytic.rellich period hPeriod)

/-- Lower form bound generated by the positive shifted form. -/
def semibounded
    (analytic : CanonicalPhysicalScalarCanonicalResolventReducedAnalyticData
      period hPeriod massSquared (Regularity := Regularity)) :
    analytic.boundary.triple.LagrangianSemiboundedData analytic.condition :=
  (analytic.shiftedFormCoercive period hPeriod).toSemiboundedData
    analytic.boundary.triple analytic.condition analytic.referenceParameter

/-- Direct physical Fredholm alternative. -/
theorem fredholmAlternative
    (analytic : CanonicalPhysicalScalarCanonicalResolventReducedAnalyticData
      period hPeriod massSquared (Regularity := Regularity))
    (spectralParameter : Real)
    (hParameter : spectralParameter ≠ analytic.referenceParameter) :
    analytic.boundary.triple.LagrangianHasEigenvalue
        analytic.condition spectralParameter ∨
      analytic.boundary.triple.LagrangianResolventPoint
        analytic.condition spectralParameter :=
  analytic.boundary.triple.lagrangian_fredholmAlternative
    analytic.condition analytic.referenceParameter spectralParameter
    (sub_ne_zero.mpr hParameter)
    (analytic.compactResolvent period hPeriod)

/-- Finite multiplicity away from the reference parameter. -/
theorem finiteDimensional_operatorEigenspace
    (analytic : CanonicalPhysicalScalarCanonicalResolventReducedAnalyticData
      period hPeriod massSquared (Regularity := Regularity))
    (eigenvalue : Real)
    (hEigenvalue : eigenvalue ≠ analytic.referenceParameter) :
    FiniteDimensional Real
      (analytic.boundary.triple.lagrangianOperatorEigenspace
        analytic.condition eigenvalue) :=
  (analytic.compactResolvent period hPeriod)
    |>.finiteDimensional_operatorEigenspace
      analytic.boundary.triple analytic.condition
      analytic.referenceParameter eigenvalue hEigenvalue

/-- Eigenfields at distinct eigenvalues are ambient-orthogonal. -/
theorem eigenfields_orthogonal
    (analytic : CanonicalPhysicalScalarCanonicalResolventReducedAnalyticData
      period hPeriod massSquared (Regularity := Regularity))
    (firstEigenvalue secondEigenvalue : Real)
    (hDistinct : firstEigenvalue ≠ secondEigenvalue)
    (first : analytic.boundary.triple.lagrangianOperatorEigenspace
      analytic.condition firstEigenvalue)
    (second : analytic.boundary.triple.lagrangianOperatorEigenspace
      analytic.condition secondEigenvalue) :
    inner Real
        (analytic.boundary.triple.lagrangianInclusion
          analytic.condition first.1)
        (analytic.boundary.triple.lagrangianInclusion
          analytic.condition second.1) = 0 :=
  analytic.boundary.triple.lagrangianEigenfields_orthogonal
    analytic.condition firstEigenvalue secondEigenvalue hDistinct first second

/-- Every physical eigenvalue lies above the reference parameter. -/
theorem eigenvalue_ge_referenceParameter
    (analytic : CanonicalPhysicalScalarCanonicalResolventReducedAnalyticData
      period hPeriod massSquared (Regularity := Regularity))
    (eigenvalue : Real)
    (hEigenvalue : analytic.boundary.triple.LagrangianHasEigenvalue
      analytic.condition eigenvalue) :
    analytic.referenceParameter ≤ eigenvalue := by
  rcases hEigenvalue with ⟨field, hField, hEquation⟩
  exact (analytic.semibounded period hPeriod).eigenvalue_ge_lowerBound
    analytic.boundary.triple analytic.condition eigenvalue
    field hField hEquation

/-- Spectral completeness of the compact ambient reference resolvent. -/
theorem spectral_complete
    (analytic : CanonicalPhysicalScalarCanonicalResolventReducedAnalyticData
      period hPeriod massSquared (Regularity := Regularity)) :
    (⨆ eigenvalue : Real,
      Module.End.eigenspace
        ((analytic.compactResolvent period hPeriod).bounded.ambientResolvent
          analytic.boundary.triple analytic.condition
            analytic.referenceParameter).toLinearMap eigenvalue)ᗮ = ⊥ :=
  (analytic.compactResolvent period hPeriod).spectral_complete
    analytic.boundary.triple analytic.condition analytic.referenceParameter

/-- Resolvent-based final analytic certificate. -/
theorem certificate
    (analytic : CanonicalPhysicalScalarCanonicalResolventReducedAnalyticData
      period hPeriod massSquared (Regularity := Regularity)) :
    DenseRange
        (analytic.boundary.triple.lagrangianInclusion analytic.condition) ∧
      analytic.boundary.triple.actualAdjointDomain analytic.condition =
        analytic.boundary.triple.realizationDomain analytic.condition ∧
      IsCompactOperator
        (P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D.canonicalPhysicalScalarH1ToBulkL2
          period hPeriod) ∧
      (∀ spectralParameter : Real,
        spectralParameter ≠ analytic.referenceParameter →
          analytic.boundary.triple.LagrangianHasEigenvalue
              analytic.condition spectralParameter ∨
            analytic.boundary.triple.LagrangianResolventPoint
              analytic.condition spectralParameter) ∧
      (∀ eigenvalue : Real,
        eigenvalue ≠ analytic.referenceParameter →
          FiniteDimensional Real
            (analytic.boundary.triple.lagrangianOperatorEigenspace
              analytic.condition eigenvalue)) ∧
      (∀ eigenvalue : Real,
        analytic.boundary.triple.LagrangianHasEigenvalue
            analytic.condition eigenvalue →
          analytic.referenceParameter ≤ eigenvalue) :=
  ⟨analytic.denseDomain period hPeriod,
    analytic.actualAdjointDomain_eq period hPeriod,
    analytic.rellich period hPeriod,
    analytic.fredholmAlternative period hPeriod,
    analytic.finiteDimensional_operatorEigenspace period hPeriod,
    analytic.eigenvalue_ge_referenceParameter period hPeriod⟩

end CanonicalPhysicalScalarCanonicalResolventReducedAnalyticData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalResolventReducedAnalyticClosure4D
end JanusFormal
