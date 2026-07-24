import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszPDEClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetRellichCompactness4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarFiniteCoordinateRellich4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarHilbertGreenCoreLagrangianDensity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarCompletedBoundaryTripleExternalPositiveShiftedForm4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarCompletedBoundaryTripleSelfAdjointResolvent4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarCompletedBoundaryTripleCompactSpectrum4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarCompletedBoundaryTripleEigenspace4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarCompletedBoundaryTripleFredholmAlternative4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarCompletedBoundaryTripleSemiboundedSpectrum4D

/-!
# Minimal final analytic endpoint for the physical scalar theory

The positive part of the shifted form is allowed to take values in an arbitrary
energy space, and Rellich approximants are supplied by explicit finite
coordinate factorizations

`H¹ -> ℝⁿ -> L²`.

Together with the normal/tangential Riesz PDE package, the direct analytic
input is therefore exactly:

* one closed Lagrangian boundary condition;
* coercivity of one real shifted Lagrangian form;
* one sequence of finite-coordinate approximants converging in operator norm.

The external positive-square decomposition is retained as a stronger
compatibility interface and converts automatically to direct coercivity.

Self-adjointness, compact resolvent, Fredholm alternative, finite multiplicity,
orthogonality, spectral completeness and the lower spectral bound follow.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszMinimalAnalyticClosure4D

set_option autoImplicit false
noncomputable section

open Set Topology MeasureTheory Module End
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetRellichCompactness4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetGreenCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetGreenCore4D.CanonicalPhysicalScalarFirstSheetGreenCoreData
open P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszPDEClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFiniteCoordinateRellich4D
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D
open P0EFTJanusMappingTorusScalarHilbertGreenCoreLagrangianDensity4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleResolvent4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleShiftedForm4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleExternalPositiveShiftedForm4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleSelfAdjointResolvent4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleCompactSpectrum4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleEigenspace4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleFredholmAlternative4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleSemiboundedSpectrum4D

universe e

variable (period : Real) (hPeriod : period ≠ 0)
variable {massSquared : Real}
variable {Energy : Type e}
  [NormedAddCommGroup Energy] [NormedSpace Real Energy]

local instance minimalAnalyticPhysicalH1CompleteSpace :
    CompleteSpace (CanonicalPhysicalScalarH1 period hPeriod) :=
  canonicalPhysicalScalarH1CompleteSpace period hPeriod

private abbrev BoundaryL2 := CanonicalPhysicalScalarFirstSheetL2 period

/-- Minimal analytic input when shifted coercivity is supplied directly. -/
structure CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszDirectCoerciveMinimalAnalyticData
    (massSquared : Real) where
  boundary : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszPDEData
    period hPeriod massSquared
  condition : CanonicalScalarHilbertLagrangianBoundaryCondition
    (BoundaryL2 period)
  referenceParameter : Real
  shiftedFormCoercive : boundary.triple.LagrangianShiftedFormCoerciveData
    condition referenceParameter
  finiteCoordinateRellich : CanonicalPhysicalScalarFiniteCoordinateRellichData
    period hPeriod

namespace CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszDirectCoerciveMinimalAnalyticData

/-- Density of the selected Lagrangian realization. -/
theorem denseDomain
    (analytic :
      CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszDirectCoerciveMinimalAnalyticData
        period hPeriod massSquared) :
    DenseRange
      (analytic.boundary.triple.lagrangianInclusion analytic.condition) :=
  P0EFTJanusMappingTorusScalarHilbertGreenCoreLagrangianDensity4D.CanonicalScalarCompletedBoundaryTripleData.lagrangianInclusion_denseRange_of_minimalCore
    (analytic.boundary.triple period hPeriod) analytic.condition
    ((analytic.boundary.toIntrinsicWaveRieszReducedPDEData period hPeriod).certificate
      period hPeriod).2.1

/-- Direct coercive-surjective shifted operator. -/
def coerciveSurjectiveAt
    (analytic :
      CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszDirectCoerciveMinimalAnalyticData
        period hPeriod massSquared) :
    analytic.boundary.triple.LagrangianCoerciveSurjectiveAt
      analytic.condition analytic.referenceParameter :=
  analytic.shiftedFormCoercive.toCoerciveSurjectiveAt
    analytic.boundary.triple analytic.condition analytic.referenceParameter
    (analytic.denseDomain period hPeriod)

/-- Bounded real reference resolvent. -/
noncomputable def boundedResolvent
    (analytic :
      CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszDirectCoerciveMinimalAnalyticData
        period hPeriod massSquared) :
    analytic.boundary.triple.LagrangianBoundedResolventAt
      analytic.condition analytic.referenceParameter :=
  analytic.shiftedFormCoercive.boundedResolvent
    analytic.boundary.triple analytic.condition analytic.referenceParameter
    (analytic.denseDomain period hPeriod)

/-- Actual Hilbert self-adjointness follows from the bounded real resolvent. -/
theorem actualAdjointDomain_eq
    (analytic :
      CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszDirectCoerciveMinimalAnalyticData
        period hPeriod massSquared) :
    analytic.boundary.triple.actualAdjointDomain analytic.condition =
      analytic.boundary.triple.realizationDomain analytic.condition :=
  analytic.boundary.triple
    |>.actualAdjointDomain_eq_realizationDomain_of_boundedResolvent
      analytic.condition analytic.referenceParameter
      (analytic.boundedResolvent period hPeriod)

/-- Physical Rellich compactness generated by finite coordinates. -/
theorem rellich
    (analytic :
      CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszDirectCoerciveMinimalAnalyticData
        period hPeriod massSquared) :
    PhysicalH1RellichCompactness period hPeriod :=
  analytic.finiteCoordinateRellich.rellich

/-- Compactness of the selected realization inclusion. -/
theorem lagrangianInclusion_compact
    (analytic :
      CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszDirectCoerciveMinimalAnalyticData
        period hPeriod massSquared) :
    IsCompactOperator
      (analytic.boundary.triple.lagrangianInclusion analytic.condition) :=
  ((analytic.boundary.geometric.greenCore period hPeriod).physicalH1RegularityData
      period hPeriod (analytic.boundary.graphEllipticEstimate period hPeriod))
    |>.lagrangianInclusion_compact
      (analytic.boundary.triple period hPeriod) analytic.condition
      (analytic.rellich period hPeriod)

/-- Coercive inverse with compact selected-domain inclusion. -/
def coerciveCompactEmbeddingAt
    (analytic :
      CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszDirectCoerciveMinimalAnalyticData
        period hPeriod massSquared) :
    analytic.boundary.triple.LagrangianCoerciveCompactEmbeddingAt
      analytic.condition analytic.referenceParameter where
  coercive := analytic.coerciveSurjectiveAt period hPeriod
  compact_inclusion := analytic.lagrangianInclusion_compact period hPeriod

/-- Compact physical reference resolvent. -/
noncomputable def compactResolvent
    (analytic :
      CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszDirectCoerciveMinimalAnalyticData
        period hPeriod massSquared) :
    analytic.boundary.triple.LagrangianCompactResolventAt
      analytic.condition analytic.referenceParameter :=
  (analytic.coerciveCompactEmbeddingAt period hPeriod)
    |>.compactResolvent analytic.boundary.triple
      analytic.condition analytic.referenceParameter

/-- Lower form bound generated directly by coercivity. -/
def semibounded
    (analytic :
      CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszDirectCoerciveMinimalAnalyticData
        period hPeriod massSquared) :
    analytic.boundary.triple.LagrangianSemiboundedData analytic.condition :=
  analytic.shiftedFormCoercive.toSemiboundedData
    analytic.boundary.triple analytic.condition analytic.referenceParameter

/-- Direct physical Fredholm alternative. -/
theorem fredholmAlternative
    (analytic :
      CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszDirectCoerciveMinimalAnalyticData
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
    (analytic :
      CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszDirectCoerciveMinimalAnalyticData
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

/-- Eigenfields at distinct eigenvalues are orthogonal. -/
theorem eigenfields_orthogonal
    (analytic :
      CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszDirectCoerciveMinimalAnalyticData
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

/-- Every physical eigenvalue lies above the coercive reference parameter. -/
theorem eigenvalue_ge_referenceParameter
    (analytic :
      CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszDirectCoerciveMinimalAnalyticData
        period hPeriod massSquared)
    (eigenvalue : Real)
    (hEigenvalue : analytic.boundary.triple.LagrangianHasEigenvalue
      analytic.condition eigenvalue) :
    analytic.referenceParameter ≤ eigenvalue := by
  rcases hEigenvalue with ⟨field, hField, hEquation⟩
  exact (analytic.semibounded period hPeriod).eigenvalue_ge_lowerBound
    analytic.boundary.triple analytic.condition eigenvalue
    field hField hEquation

/-- Spectral completeness of the compact reference resolvent. -/
theorem spectral_complete
    (analytic :
      CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszDirectCoerciveMinimalAnalyticData
        period hPeriod massSquared) :
    (⨆ eigenvalue : Real,
      Module.End.eigenspace
        ((analytic.compactResolvent period hPeriod).bounded.ambientResolvent
          analytic.boundary.triple analytic.condition
            analytic.referenceParameter).toLinearMap eigenvalue)ᗮ = ⊥ :=
  (analytic.compactResolvent period hPeriod).spectral_complete
    analytic.boundary.triple analytic.condition analytic.referenceParameter

/-- Direct-coercive minimal analytic certificate. -/
theorem certificate
    (analytic :
      CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszDirectCoerciveMinimalAnalyticData
        period hPeriod massSquared) :
    (∀ field test,
      (∫ parameter,
        analytic.boundary.geometric.tangentialDensity field test parameter
        ∂P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetProductCoarea4D.canonicalLatitudeCauchyJetProductMeasure
          period) = 0) ∧
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
              analytic.condition spectralParameter) :=
  ⟨analytic.boundary.geometric.toNormalTangentialSplitData
      |>.tangential_integral_eq_zero,
    (analytic.boundary.certificate period hPeriod).2.2.2.1,
    analytic.actualAdjointDomain_eq period hPeriod,
    analytic.rellich period hPeriod,
    analytic.fredholmAlternative period hPeriod⟩

end CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszDirectCoerciveMinimalAnalyticData

/-- Smallest current full analytic input package. -/
structure CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszMinimalAnalyticData
    (massSquared : Real) (Energy : Type e)
    [NormedAddCommGroup Energy] [NormedSpace Real Energy] where
  boundary : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszPDEData
    period hPeriod massSquared
  condition : CanonicalScalarHilbertLagrangianBoundaryCondition
    (BoundaryL2 period)
  referenceParameter : Real
  shiftedPositiveDecomposition :
    boundary.triple.LagrangianShiftedExternalPositiveDecompositionData
      condition referenceParameter Energy
  finiteCoordinateRellich : CanonicalPhysicalScalarFiniteCoordinateRellichData
    period hPeriod

namespace CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszMinimalAnalyticData

/-- Every external positive decomposition factors through direct coercivity. -/
def toDirectCoerciveMinimalAnalyticData
    (analytic : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszMinimalAnalyticData
      period hPeriod massSquared Energy) :
    CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszDirectCoerciveMinimalAnalyticData
      period hPeriod massSquared where
  boundary := analytic.boundary
  condition := analytic.condition
  referenceParameter := analytic.referenceParameter
  shiftedFormCoercive :=
    analytic.shiftedPositiveDecomposition.toShiftedFormCoerciveData
      analytic.boundary.triple analytic.condition analytic.referenceParameter
  finiteCoordinateRellich := analytic.finiteCoordinateRellich

/-- Density of the selected Lagrangian realization. -/
theorem denseDomain
    (analytic : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszMinimalAnalyticData
      period hPeriod massSquared Energy) :
    DenseRange
      (analytic.boundary.triple.lagrangianInclusion analytic.condition) :=
  P0EFTJanusMappingTorusScalarHilbertGreenCoreLagrangianDensity4D.CanonicalScalarCompletedBoundaryTripleData.lagrangianInclusion_denseRange_of_minimalCore
    (analytic.boundary.triple period hPeriod) analytic.condition
    ((analytic.boundary.toIntrinsicWaveRieszReducedPDEData period hPeriod).certificate
      period hPeriod).2.1

/-- Shifted coercivity generated by the external energy decomposition. -/
def shiftedFormCoercive
    (analytic : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszMinimalAnalyticData
      period hPeriod massSquared Energy) :
    analytic.boundary.triple.LagrangianShiftedFormCoerciveData
      analytic.condition analytic.referenceParameter :=
  analytic.shiftedPositiveDecomposition.toShiftedFormCoerciveData
    analytic.boundary.triple analytic.condition analytic.referenceParameter

/-- Direct coercive-surjective shifted operator. -/
def coerciveSurjectiveAt
    (analytic : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszMinimalAnalyticData
      period hPeriod massSquared Energy) :
    analytic.boundary.triple.LagrangianCoerciveSurjectiveAt
      analytic.condition analytic.referenceParameter :=
  (analytic.shiftedFormCoercive period hPeriod).toCoerciveSurjectiveAt
    analytic.boundary.triple analytic.condition analytic.referenceParameter
    (analytic.denseDomain period hPeriod)

/-- Bounded real reference resolvent. -/
noncomputable def boundedResolvent
    (analytic : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszMinimalAnalyticData
      period hPeriod massSquared Energy) :
    analytic.boundary.triple.LagrangianBoundedResolventAt
      analytic.condition analytic.referenceParameter :=
  (analytic.shiftedFormCoercive period hPeriod).boundedResolvent
    analytic.boundary.triple analytic.condition analytic.referenceParameter
    (analytic.denseDomain period hPeriod)

/-- Actual Hilbert self-adjointness follows from the bounded real resolvent. -/
theorem actualAdjointDomain_eq
    (analytic : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszMinimalAnalyticData
      period hPeriod massSquared Energy) :
    analytic.boundary.triple.actualAdjointDomain analytic.condition =
      analytic.boundary.triple.realizationDomain analytic.condition :=
  analytic.boundary.triple
    |>.actualAdjointDomain_eq_realizationDomain_of_boundedResolvent
      analytic.condition analytic.referenceParameter
      (analytic.boundedResolvent period hPeriod)

/-- Physical Rellich compactness generated by finite coordinates. -/
theorem rellich
    (analytic : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszMinimalAnalyticData
      period hPeriod massSquared Energy) :
    PhysicalH1RellichCompactness period hPeriod :=
  analytic.finiteCoordinateRellich.rellich

/-- Compactness of the selected realization inclusion. -/
theorem lagrangianInclusion_compact
    (analytic : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszMinimalAnalyticData
      period hPeriod massSquared Energy) :
    IsCompactOperator
      (analytic.boundary.triple.lagrangianInclusion analytic.condition) :=
  ((analytic.boundary.geometric.greenCore period hPeriod).physicalH1RegularityData
      period hPeriod (analytic.boundary.graphEllipticEstimate period hPeriod))
    |>.lagrangianInclusion_compact
      (analytic.boundary.triple period hPeriod) analytic.condition
      (analytic.rellich period hPeriod)

/-- Coercive inverse with compact selected-domain inclusion. -/
def coerciveCompactEmbeddingAt
    (analytic : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszMinimalAnalyticData
      period hPeriod massSquared Energy) :
    analytic.boundary.triple.LagrangianCoerciveCompactEmbeddingAt
      analytic.condition analytic.referenceParameter where
  coercive := analytic.coerciveSurjectiveAt period hPeriod
  compact_inclusion := analytic.lagrangianInclusion_compact period hPeriod

/-- Compact physical reference resolvent. -/
noncomputable def compactResolvent
    (analytic : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszMinimalAnalyticData
      period hPeriod massSquared Energy) :
    analytic.boundary.triple.LagrangianCompactResolventAt
      analytic.condition analytic.referenceParameter :=
  (analytic.coerciveCompactEmbeddingAt period hPeriod)
    |>.compactResolvent analytic.boundary.triple
      analytic.condition analytic.referenceParameter

/-- Lower form bound. -/
def semibounded
    (analytic : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszMinimalAnalyticData
      period hPeriod massSquared Energy) :
    analytic.boundary.triple.LagrangianSemiboundedData analytic.condition :=
  (analytic.shiftedFormCoercive period hPeriod).toSemiboundedData
    analytic.boundary.triple analytic.condition analytic.referenceParameter

/-- Direct Fredholm alternative. -/
theorem fredholmAlternative
    (analytic : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszMinimalAnalyticData
      period hPeriod massSquared Energy)
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
    (analytic : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszMinimalAnalyticData
      period hPeriod massSquared Energy)
    (eigenvalue : Real)
    (hEigenvalue : eigenvalue ≠ analytic.referenceParameter) :
    FiniteDimensional Real
      (analytic.boundary.triple.lagrangianOperatorEigenspace
        analytic.condition eigenvalue) :=
  (analytic.compactResolvent period hPeriod)
    |>.finiteDimensional_operatorEigenspace
      analytic.boundary.triple analytic.condition
      analytic.referenceParameter eigenvalue hEigenvalue

/-- Eigenfields at distinct eigenvalues are orthogonal. -/
theorem eigenfields_orthogonal
    (analytic : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszMinimalAnalyticData
      period hPeriod massSquared Energy)
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

/-- Every eigenvalue lies above the reference parameter. -/
theorem eigenvalue_ge_referenceParameter
    (analytic : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszMinimalAnalyticData
      period hPeriod massSquared Energy)
    (eigenvalue : Real)
    (hEigenvalue : analytic.boundary.triple.LagrangianHasEigenvalue
      analytic.condition eigenvalue) :
    analytic.referenceParameter ≤ eigenvalue := by
  rcases hEigenvalue with ⟨field, hField, hEquation⟩
  exact (analytic.semibounded period hPeriod).eigenvalue_ge_lowerBound
    analytic.boundary.triple analytic.condition eigenvalue
    field hField hEquation

/-- Spectral completeness of the compact reference resolvent. -/
theorem spectral_complete
    (analytic : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszMinimalAnalyticData
      period hPeriod massSquared Energy) :
    (⨆ eigenvalue : Real,
      Module.End.eigenspace
        ((analytic.compactResolvent period hPeriod).bounded.ambientResolvent
          analytic.boundary.triple analytic.condition
            analytic.referenceParameter).toLinearMap eigenvalue)ᗮ = ⊥ :=
  (analytic.compactResolvent period hPeriod).spectral_complete
    analytic.boundary.triple analytic.condition analytic.referenceParameter

/-- Minimal final analytic certificate. -/
theorem certificate
    (analytic : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszMinimalAnalyticData
      period hPeriod massSquared Energy) :
    (∀ field test,
      (∫ parameter,
        analytic.boundary.geometric.tangentialDensity field test parameter
        ∂P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetProductCoarea4D.canonicalLatitudeCauchyJetProductMeasure
          period) = 0) ∧
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
              analytic.condition spectralParameter) :=
  ⟨analytic.boundary.geometric.toNormalTangentialSplitData
      |>.tangential_integral_eq_zero,
    (analytic.boundary.certificate period hPeriod).2.2.2.1,
    analytic.actualAdjointDomain_eq period hPeriod,
    analytic.rellich period hPeriod,
    analytic.fredholmAlternative period hPeriod⟩

end CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszMinimalAnalyticData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszMinimalAnalyticClosure4D
end JanusFormal
