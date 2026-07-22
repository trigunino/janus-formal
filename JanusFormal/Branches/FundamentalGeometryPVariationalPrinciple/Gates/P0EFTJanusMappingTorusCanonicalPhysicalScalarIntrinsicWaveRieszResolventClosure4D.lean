import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveRieszReducedPDEClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetRellichCompactness4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarFiniteRankRellich4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarHilbertGreenCoreLagrangianDensity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarCompletedBoundaryTriplePositiveShiftedForm4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarCompletedBoundaryTripleSelfAdjointResolvent4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarCompletedBoundaryTripleCompactSpectrum4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarCompletedBoundaryTripleEigenspace4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarCompletedBoundaryTripleFredholmAlternative4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarCompletedBoundaryTripleSemiboundedSpectrum4D

/-!
# Adjoint-free spectral closure of the Riesz physical boundary triple

The Riesz boundary construction removes the normal-trace regularity input.  The
exact energy identity still gives the physical `H¹` graph estimate, so Rellich
compactness factors every selected Lagrangian inclusion through physical `H¹`.

The final analytic input contains only:

* the Riesz-reduced PDE package;
* one closed Lagrangian condition;
* one positive-square decomposition of a real shifted form;
* finite-rank approximants converging to the physical `H¹ -> L²` inclusion.

A bounded real resolvent gives self-adjointness directly.  Compactness,
Fredholm alternative, finite multiplicity, orthogonality, spectral completeness
and the lower spectral bound follow without any normal regularity or adjoint
regularity hypothesis.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveRieszResolventClosure4D

set_option autoImplicit false
noncomputable section

open Set Topology MeasureTheory Module End
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetRellichCompactness4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveRieszReducedPDEClosure4D
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

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev BoundaryL2 := CanonicalPhysicalScalarFirstSheetL2 period

/-- Final adjoint-free analytic data over the Riesz physical boundary triple. -/
structure CanonicalPhysicalScalarIntrinsicWaveRieszResolventData
    (massSquared : Real) where
  boundary : CanonicalPhysicalScalarIntrinsicWaveRieszReducedPDEData
    period hPeriod massSquared
  condition : CanonicalScalarHilbertLagrangianBoundaryCondition
    (BoundaryL2 period)
  referenceParameter : Real
  shiftedPositiveDecomposition :
    boundary.triple.LagrangianShiftedPositiveDecompositionData
      condition referenceParameter
  finiteRankRellich : CanonicalPhysicalScalarFiniteRankRellichData
    period hPeriod

namespace CanonicalPhysicalScalarIntrinsicWaveRieszResolventData

/-- Density of every selected Riesz-completed Lagrangian realization. -/
theorem denseDomain
    (analytic : CanonicalPhysicalScalarIntrinsicWaveRieszResolventData
      period hPeriod massSquared) :
    DenseRange
      (analytic.boundary.triple.lagrangianInclusion analytic.condition) :=
  analytic.boundary.triple.lagrangianInclusion_denseRange_of_minimalCore
    analytic.condition analytic.boundary.rieszBoundaryData.minimalCoreDense

/-- Shifted coercivity generated from the positive decomposition. -/
def shiftedFormCoercive
    (analytic : CanonicalPhysicalScalarIntrinsicWaveRieszResolventData
      period hPeriod massSquared) :
    analytic.boundary.triple.LagrangianShiftedFormCoerciveData
      analytic.condition analytic.referenceParameter :=
  analytic.shiftedPositiveDecomposition.toShiftedFormCoerciveData
    analytic.boundary.triple analytic.condition analytic.referenceParameter

/-- Direct coercive-surjective shifted operator. -/
def coerciveSurjectiveAt
    (analytic : CanonicalPhysicalScalarIntrinsicWaveRieszResolventData
      period hPeriod massSquared) :
    analytic.boundary.triple.LagrangianCoerciveSurjectiveAt
      analytic.condition analytic.referenceParameter :=
  (analytic.shiftedFormCoercive period hPeriod).toCoerciveSurjectiveAt
    analytic.boundary.triple analytic.condition analytic.referenceParameter
    (analytic.denseDomain period hPeriod)

/-- Bounded real reference resolvent. -/
noncomputable def boundedResolvent
    (analytic : CanonicalPhysicalScalarIntrinsicWaveRieszResolventData
      period hPeriod massSquared) :
    analytic.boundary.triple.LagrangianBoundedResolventAt
      analytic.condition analytic.referenceParameter :=
  (analytic.shiftedFormCoercive period hPeriod).boundedResolvent
    analytic.boundary.triple analytic.condition analytic.referenceParameter
    (analytic.denseDomain period hPeriod)

/-- Actual Hilbert self-adjointness from the bounded real resolvent. -/
theorem actualAdjointDomain_eq
    (analytic : CanonicalPhysicalScalarIntrinsicWaveRieszResolventData
      period hPeriod massSquared) :
    analytic.boundary.triple.actualAdjointDomain analytic.condition =
      analytic.boundary.triple.realizationDomain analytic.condition :=
  analytic.boundary.triple
    |>.actualAdjointDomain_eq_realizationDomain_of_boundedResolvent
      analytic.condition analytic.referenceParameter
      (analytic.boundedResolvent period hPeriod)

/-- Physical Rellich compactness from finite-rank truncations. -/
theorem rellich
    (analytic : CanonicalPhysicalScalarIntrinsicWaveRieszResolventData
      period hPeriod massSquared) :
    PhysicalH1RellichCompactness period hPeriod :=
  analytic.finiteRankRellich.rellich

/-- Compactness of the selected Riesz-completed Lagrangian inclusion. -/
theorem lagrangianInclusion_compact
    (analytic : CanonicalPhysicalScalarIntrinsicWaveRieszResolventData
      period hPeriod massSquared) :
    IsCompactOperator
      (analytic.boundary.triple.lagrangianInclusion analytic.condition) :=
  (analytic.boundary.geometric.greenCore.physicalH1RegularityData
      period hPeriod analytic.boundary.graphEllipticEstimate)
    |>.lagrangianInclusion_compact
      analytic.boundary.triple analytic.condition
      (analytic.rellich period hPeriod)

/-- Coercive inverse with compact selected-domain inclusion. -/
def coerciveCompactEmbeddingAt
    (analytic : CanonicalPhysicalScalarIntrinsicWaveRieszResolventData
      period hPeriod massSquared) :
    analytic.boundary.triple.LagrangianCoerciveCompactEmbeddingAt
      analytic.condition analytic.referenceParameter where
  coercive := analytic.coerciveSurjectiveAt period hPeriod
  compact_inclusion := analytic.lagrangianInclusion_compact period hPeriod

/-- Compact physical reference resolvent. -/
noncomputable def compactResolvent
    (analytic : CanonicalPhysicalScalarIntrinsicWaveRieszResolventData
      period hPeriod massSquared) :
    analytic.boundary.triple.LagrangianCompactResolventAt
      analytic.condition analytic.referenceParameter :=
  (analytic.coerciveCompactEmbeddingAt period hPeriod)
    |>.compactResolvent analytic.boundary.triple
      analytic.condition analytic.referenceParameter

/-- Lower form bound generated by the positive shifted form. -/
def semibounded
    (analytic : CanonicalPhysicalScalarIntrinsicWaveRieszResolventData
      period hPeriod massSquared) :
    analytic.boundary.triple.LagrangianSemiboundedData analytic.condition :=
  (analytic.shiftedFormCoercive period hPeriod).toSemiboundedData
    analytic.boundary.triple analytic.condition analytic.referenceParameter

/-- Direct physical Fredholm alternative. -/
theorem fredholmAlternative
    (analytic : CanonicalPhysicalScalarIntrinsicWaveRieszResolventData
      period hPeriod massSquared)
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
    (analytic : CanonicalPhysicalScalarIntrinsicWaveRieszResolventData
      period hPeriod massSquared)
    (eigenvalue : Real)
    (hEigenvalue : eigenvalue ≠ analytic.referenceParameter) :
    FiniteDimensional Real
      (analytic.boundary.triple.lagrangianOperatorEigenspace
        analytic.condition eigenvalue) :=
  (analytic.compactResolvent period hPeriod)
    |>.finiteDimensional_operatorEigenspace
      analytic.boundary.triple analytic.condition
      analytic.referenceParameter eigenvalue hEigenvalue

/-- Eigenfields for distinct eigenvalues are ambient-orthogonal. -/
theorem eigenfields_orthogonal
    (analytic : CanonicalPhysicalScalarIntrinsicWaveRieszResolventData
      period hPeriod massSquared)
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

/-- Every eigenvalue lies above the positive-decomposition reference. -/
theorem eigenvalue_ge_referenceParameter
    (analytic : CanonicalPhysicalScalarIntrinsicWaveRieszResolventData
      period hPeriod massSquared)
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
    (analytic : CanonicalPhysicalScalarIntrinsicWaveRieszResolventData
      period hPeriod massSquared) :
    (⨆ eigenvalue : Real,
      Module.End.eigenspace
        ((analytic.compactResolvent period hPeriod).bounded.ambientResolvent
          analytic.boundary.triple analytic.condition
            analytic.referenceParameter).toLinearMap eigenvalue)ᗮ = ⊥ :=
  (analytic.compactResolvent period hPeriod).spectral_complete
    analytic.boundary.triple analytic.condition analytic.referenceParameter

/-- Riesz-reduced adjoint-free spectral certificate. -/
theorem certificate
    (analytic : CanonicalPhysicalScalarIntrinsicWaveRieszResolventData
      period hPeriod massSquared) :
    Function.Surjective analytic.boundary.completedBoundaryTrace ∧
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
              analytic.condition eigenvalue)) :=
  ⟨analytic.boundary.rieszBoundaryData.boundedSmoothExtension
      |>.rieszBoundaryTrace_surjective,
    analytic.actualAdjointDomain_eq period hPeriod,
    analytic.rellich period hPeriod,
    analytic.fredholmAlternative period hPeriod,
    analytic.finiteDimensional_operatorEigenspace period hPeriod⟩

end CanonicalPhysicalScalarIntrinsicWaveRieszResolventData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveRieszResolventClosure4D
end JanusFormal
