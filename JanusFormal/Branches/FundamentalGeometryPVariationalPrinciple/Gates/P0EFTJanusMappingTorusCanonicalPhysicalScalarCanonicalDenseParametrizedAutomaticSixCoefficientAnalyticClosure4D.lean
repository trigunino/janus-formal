import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalDenseParametrizedAutomaticSixCoefficientPDEClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalAutomaticSixCoefficientAnalyticClosure4D

/-!
# Analytic closure over the dense-parametrized minimal canonical package

The physical measure-faithfulness input is now supplied by a dense
measure-preserving parametrization, while the boundary construction is reduced
to one energy estimate, one normal elliptic estimate and six Euler coefficient
bounds.

This file carries that package through the actual-adjoint, shifted-form and
compact-resolvent machinery.  Beyond the dense-parametrized boundary data, the
remaining analytic inputs are exactly:

* smooth approximation of adjoint graph pairs;
* coercivity of one shifted Lagrangian form;
* compact approximation of the physical `H¹ -> L²` inclusion.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalDenseParametrizedAutomaticSixCoefficientAnalyticClosure4D

set_option autoImplicit false
noncomputable section

open Set Topology MeasureTheory
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalDenseParametrizedAutomaticSixCoefficientPDEClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalAutomaticSixCoefficientAnalyticClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarRellichApproximation4D
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleAdjointGraphRegularity4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleShiftedForm4D

universe u r

variable (period : Real) (hPeriod : period ≠ 0)
variable {massSquared : Real}
variable {Regularity : Type r}
  [NormedAddCommGroup Regularity] [NormedSpace Real Regularity]
  [CompleteSpace Regularity]

private abbrev BoundaryL2 :=
  CanonicalPhysicalScalarFirstSheetL2 period

/-- Full analytic data over the dense-parametrized minimal canonical boundary
package. -/
structure CanonicalPhysicalScalarCanonicalDenseParametrizedAutomaticSixCoefficientAnalyticData
    (Source : Type u)
    [TopologicalSpace Source] [MeasurableSpace Source]
    (sourceMeasure : Measure Source)
    (massSquared : Real) where
  boundary :
    CanonicalPhysicalScalarCanonicalDenseParametrizedAutomaticSixCoefficientPDEData
      period hPeriod Source sourceMeasure massSquared
      (Regularity := Regularity)
  condition : CanonicalScalarHilbertLagrangianBoundaryCondition
    (BoundaryL2 period)
  adjointApproximation : boundary.triple.AdjointPairSmoothApproximationData
    condition
  referenceParameter : Real
  shiftedFormCoercive : boundary.triple.LagrangianShiftedFormCoerciveData
    condition referenceParameter
  rellichApproximation : CanonicalPhysicalScalarRellichApproximationData
    period hPeriod

namespace CanonicalPhysicalScalarCanonicalDenseParametrizedAutomaticSixCoefficientAnalyticData

/-- Conversion to the established minimal canonical analytic package. -/
def toCanonicalAutomaticSixCoefficientAnalyticData
    {Source : Type u}
    [TopologicalSpace Source] [MeasurableSpace Source]
    {sourceMeasure : Measure Source}
    (analytic :
      CanonicalPhysicalScalarCanonicalDenseParametrizedAutomaticSixCoefficientAnalyticData
        period hPeriod Source sourceMeasure massSquared
        (Regularity := Regularity)) :
    CanonicalPhysicalScalarCanonicalAutomaticSixCoefficientAnalyticData
      period hPeriod massSquared (Regularity := Regularity) where
  boundary := analytic.boundary.toCanonicalAutomaticSixCoefficientPDEData
    period hPeriod
  condition := analytic.condition
  adjointApproximation := analytic.adjointApproximation
  referenceParameter := analytic.referenceParameter
  shiftedFormCoercive := analytic.shiftedFormCoercive
  rellichApproximation := analytic.rellichApproximation

/-- Actual Hilbert self-adjointness of the selected physical realization. -/
theorem actualAdjointDomain_eq
    {Source : Type u}
    [TopologicalSpace Source] [MeasurableSpace Source]
    {sourceMeasure : Measure Source}
    (analytic :
      CanonicalPhysicalScalarCanonicalDenseParametrizedAutomaticSixCoefficientAnalyticData
        period hPeriod Source sourceMeasure massSquared
        (Regularity := Regularity)) :
    analytic.boundary.triple.actualAdjointDomain analytic.condition =
      analytic.boundary.triple.realizationDomain analytic.condition :=
  (analytic.toCanonicalAutomaticSixCoefficientAnalyticData period hPeriod)
    |>.actualAdjointDomain_eq period hPeriod

/-- Compact physical reference resolvent. -/
noncomputable def compactResolvent
    {Source : Type u}
    [TopologicalSpace Source] [MeasurableSpace Source]
    {sourceMeasure : Measure Source}
    (analytic :
      CanonicalPhysicalScalarCanonicalDenseParametrizedAutomaticSixCoefficientAnalyticData
        period hPeriod Source sourceMeasure massSquared
        (Regularity := Regularity)) :=
  (analytic.toCanonicalAutomaticSixCoefficientAnalyticData period hPeriod)
    |>.compactResolvent period hPeriod

/-- Direct physical Fredholm alternative. -/
theorem fredholmAlternative
    {Source : Type u}
    [TopologicalSpace Source] [MeasurableSpace Source]
    {sourceMeasure : Measure Source}
    (analytic :
      CanonicalPhysicalScalarCanonicalDenseParametrizedAutomaticSixCoefficientAnalyticData
        period hPeriod Source sourceMeasure massSquared
        (Regularity := Regularity))
    (spectralParameter : Real)
    (hParameter : spectralParameter ≠ analytic.referenceParameter) :
    analytic.boundary.triple.LagrangianHasEigenvalue
        analytic.condition spectralParameter ∨
      analytic.boundary.triple.LagrangianResolventPoint
        analytic.condition spectralParameter :=
  (analytic.toCanonicalAutomaticSixCoefficientAnalyticData period hPeriod)
    |>.fredholmAlternative period hPeriod spectralParameter hParameter

/-- Finite multiplicity away from the reference parameter. -/
theorem finiteDimensional_operatorEigenspace
    {Source : Type u}
    [TopologicalSpace Source] [MeasurableSpace Source]
    {sourceMeasure : Measure Source}
    (analytic :
      CanonicalPhysicalScalarCanonicalDenseParametrizedAutomaticSixCoefficientAnalyticData
        period hPeriod Source sourceMeasure massSquared
        (Regularity := Regularity))
    (eigenvalue : Real)
    (hEigenvalue : eigenvalue ≠ analytic.referenceParameter) :
    FiniteDimensional Real
      (analytic.boundary.triple.lagrangianOperatorEigenspace
        analytic.condition eigenvalue) :=
  (analytic.toCanonicalAutomaticSixCoefficientAnalyticData period hPeriod)
    |>.finiteDimensional_operatorEigenspace
      period hPeriod eigenvalue hEigenvalue

/-- Every physical eigenvalue lies above the coercive reference parameter. -/
theorem eigenvalue_ge_referenceParameter
    {Source : Type u}
    [TopologicalSpace Source] [MeasurableSpace Source]
    {sourceMeasure : Measure Source}
    (analytic :
      CanonicalPhysicalScalarCanonicalDenseParametrizedAutomaticSixCoefficientAnalyticData
        period hPeriod Source sourceMeasure massSquared
        (Regularity := Regularity))
    (eigenvalue : Real)
    (hEigenvalue : analytic.boundary.triple.LagrangianHasEigenvalue
      analytic.condition eigenvalue) :
    analytic.referenceParameter ≤ eigenvalue :=
  (analytic.toCanonicalAutomaticSixCoefficientAnalyticData period hPeriod)
    |>.eigenvalue_ge_referenceParameter period hPeriod eigenvalue hEigenvalue

/-- Dense-parametrized minimal analytic certificate. -/
theorem certificate
    {Source : Type u}
    [TopologicalSpace Source] [MeasurableSpace Source]
    {sourceMeasure : Measure Source}
    (analytic :
      CanonicalPhysicalScalarCanonicalDenseParametrizedAutomaticSixCoefficientAnalyticData
        period hPeriod Source sourceMeasure massSquared
        (Regularity := Regularity)) :
    (P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D.intrinsicCanonicalLorentzVolumeMeasure
        period hPeriod).IsOpenPosMeasure ∧
      Function.Surjective
        (P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D.canonicalScalarGreenCoreCompletedBoundaryTrace
          (analytic.boundary.geometric.greenCore period hPeriod).core
          ((analytic.boundary.completedInputs period hPeriod).traceBound
            period hPeriod
            (analytic.boundary.geometric.greenCore period hPeriod))) ∧
      analytic.boundary.triple.actualAdjointDomain analytic.condition =
        analytic.boundary.triple.realizationDomain analytic.condition ∧
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
  ⟨analytic.boundary.geometric.physicalMeasureOpenPositive,
    (analytic.toCanonicalAutomaticSixCoefficientAnalyticData period hPeriod
      |>.certificate period hPeriod).1,
    analytic.actualAdjointDomain_eq period hPeriod,
    analytic.fredholmAlternative period hPeriod,
    analytic.finiteDimensional_operatorEigenspace period hPeriod,
    analytic.eigenvalue_ge_referenceParameter period hPeriod⟩

end CanonicalPhysicalScalarCanonicalDenseParametrizedAutomaticSixCoefficientAnalyticData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalDenseParametrizedAutomaticSixCoefficientAnalyticClosure4D
end JanusFormal
