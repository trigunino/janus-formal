import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetDirectAnalyticClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarCompletedBoundaryTripleShiftedForm4D

/-!
# Physical scalar analytic closure from one coercive shifted form

For the corrected physical boundary triple, minimal-core density supplies domain
density.  Coercivity of the canonical shifted form at one real parameter then
supplies by Lax--Milgram:

* surjectivity of the shifted operator;
* a bounded reference resolvent;
* the lower form bound `A >= referenceParameter`.

Physical Rellich compactness makes that resolvent compact.  Therefore the only
additional operator-theoretic input is maximal regularity for the true Hilbert
adjoint.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetShiftedFormClosure4D

set_option autoImplicit false
noncomputable section

open Set Topology Module End
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetGreenCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetGreenCore4D.CanonicalPhysicalScalarFirstSheetGreenCoreData
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetRellichCompactness4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetDirectAnalyticClosure4D
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D
open P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleActualAdjoint4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleResolvent4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleCompactSpectrum4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleFredholmAlternative4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleSemiboundedSpectrum4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleAnalyticClosure4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleShiftedForm4D

variable (period : Real) (hPeriod : period ≠ 0) {massSquared : Real}

private abbrev BoundaryL2 := CanonicalPhysicalScalarFirstSheetL2 period

/-- Minimal final analytic inputs for one physical scalar boundary condition. -/
structure CanonicalPhysicalScalarFirstSheetShiftedFormData
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (inputs : green.CompletedBoundaryTripleInputs period hPeriod) where
  condition : CanonicalScalarHilbertLagrangianBoundaryCondition
    (BoundaryL2 period)
  adjointRegularity :
    (inputs.triple period hPeriod green).MaximalAdjointRegularity condition
  referenceParameter : Real
  shiftedFormCoercive :
    (inputs.triple period hPeriod green).LagrangianShiftedFormCoerciveData
      condition referenceParameter
  rellich : PhysicalH1RellichCompactness period hPeriod

namespace CanonicalPhysicalScalarFirstSheetShiftedFormData

/-- Density of the realization is automatic from the common minimal core. -/
theorem denseDomain
    {green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared}
    {inputs : green.CompletedBoundaryTripleInputs period hPeriod}
    (analytic : CanonicalPhysicalScalarFirstSheetShiftedFormData
      period hPeriod green inputs) :
    DenseRange ((inputs.triple period hPeriod green).lagrangianInclusion
      analytic.condition) :=
  P0EFTJanusMappingTorusScalarHilbertGreenCoreLagrangianDensity4D.CanonicalScalarCompletedBoundaryTripleData.lagrangianInclusion_denseRange_of_minimalCore
    (inputs.triple period hPeriod green) analytic.condition inputs.minimalDense

/-- Lax--Milgram coercive-surjective shifted operator. -/
def coerciveSurjectiveAt
    {green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared}
    {inputs : green.CompletedBoundaryTripleInputs period hPeriod}
    (analytic : CanonicalPhysicalScalarFirstSheetShiftedFormData
      period hPeriod green inputs) :
    (inputs.triple period hPeriod green).LagrangianCoerciveSurjectiveAt
      analytic.condition analytic.referenceParameter :=
  analytic.shiftedFormCoercive.toCoerciveSurjectiveAt
    (inputs.triple period hPeriod green) analytic.condition analytic.referenceParameter
    (analytic.denseDomain period hPeriod)

/-- Compact physical reference resolvent. -/
noncomputable def compactResolvent
    {green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared}
    {inputs : green.CompletedBoundaryTripleInputs period hPeriod}
    (analytic : CanonicalPhysicalScalarFirstSheetShiftedFormData
      period hPeriod green inputs) :
    (inputs.triple period hPeriod green).LagrangianCompactResolventAt
      analytic.condition analytic.referenceParameter :=
  green.compactResolventAt period hPeriod inputs analytic.condition
    analytic.referenceParameter
    (analytic.coerciveSurjectiveAt period hPeriod) analytic.rellich

/-- The coercive reference shift gives the operator lower bound at the same
parameter. -/
def semibounded
    {green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared}
    {inputs : green.CompletedBoundaryTripleInputs period hPeriod}
    (analytic : CanonicalPhysicalScalarFirstSheetShiftedFormData
      period hPeriod green inputs) :
    (inputs.triple period hPeriod green).LagrangianSemiboundedData
      analytic.condition :=
  analytic.shiftedFormCoercive.toSemiboundedData
    (inputs.triple period hPeriod green) analytic.condition analytic.referenceParameter

/-- Conversion to the direct physical analytic closure. -/
noncomputable def toDirectAnalyticData
    {green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared}
    {inputs : green.CompletedBoundaryTripleInputs period hPeriod}
    (analytic : CanonicalPhysicalScalarFirstSheetShiftedFormData
      period hPeriod green inputs) :
    CanonicalPhysicalScalarFirstSheetDirectAnalyticData
      period hPeriod green inputs where
  condition := analytic.condition
  adjointRegularity := analytic.adjointRegularity
  referenceParameter := analytic.referenceParameter
  coercive := analytic.coerciveSurjectiveAt period hPeriod
  rellich := analytic.rellich
  semibounded := analytic.semibounded period hPeriod

/-- Actual physical Hilbert self-adjointness. -/
theorem actualAdjointDomain_eq
    {green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared}
    {inputs : green.CompletedBoundaryTripleInputs period hPeriod}
    (analytic : CanonicalPhysicalScalarFirstSheetShiftedFormData
      period hPeriod green inputs) :
    (inputs.triple period hPeriod green).actualAdjointDomain analytic.condition =
      (inputs.triple period hPeriod green).realizationDomain analytic.condition :=
  (analytic.toDirectAnalyticData period hPeriod).actualAdjointDomain_eq
    period hPeriod

/-- Physical Fredholm alternative. -/
theorem fredholmAlternative
    {green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared}
    {inputs : green.CompletedBoundaryTripleInputs period hPeriod}
    (analytic : CanonicalPhysicalScalarFirstSheetShiftedFormData
      period hPeriod green inputs)
    (spectralParameter : Real)
    (hParameter : spectralParameter ≠ analytic.referenceParameter) :
    (inputs.triple period hPeriod green).LagrangianHasEigenvalue
        analytic.condition spectralParameter ∨
      (inputs.triple period hPeriod green).LagrangianResolventPoint
        analytic.condition spectralParameter :=
  (analytic.toDirectAnalyticData period hPeriod).fredholmAlternative
    period hPeriod spectralParameter hParameter

/-- Every physical eigenvalue lies above the coercive reference parameter. -/
theorem eigenvalue_ge_referenceParameter
    {green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared}
    {inputs : green.CompletedBoundaryTripleInputs period hPeriod}
    (analytic : CanonicalPhysicalScalarFirstSheetShiftedFormData
      period hPeriod green inputs)
    (eigenvalue : Real)
    (hEigenvalue : (inputs.triple period hPeriod green).LagrangianHasEigenvalue
      analytic.condition eigenvalue) :
    analytic.referenceParameter ≤ eigenvalue := by
  have hLower :=
    (analytic.toDirectAnalyticData period hPeriod).eigenvalue_ge_lowerBound
      period hPeriod eigenvalue hEigenvalue
  exact hLower

/-- Spectral completeness of the physical compact resolvent. -/
theorem spectral_complete
    {green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared}
    {inputs : green.CompletedBoundaryTripleInputs period hPeriod}
    (analytic : CanonicalPhysicalScalarFirstSheetShiftedFormData
      period hPeriod green inputs) :
    (⨆ eigenvalue : Real,
      Module.End.eigenspace
        ((analytic.compactResolvent period hPeriod).bounded.ambientResolvent
          (inputs.triple period hPeriod green) analytic.condition
            analytic.referenceParameter).toLinearMap eigenvalue)ᗮ = ⊥ :=
  (analytic.toDirectAnalyticData period hPeriod).spectral_complete
    period hPeriod

/-- Minimal physical shifted-form closure certificate. -/
theorem certificate
    {green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared}
    {inputs : green.CompletedBoundaryTripleInputs period hPeriod}
    (analytic : CanonicalPhysicalScalarFirstSheetShiftedFormData
      period hPeriod green inputs) :
    DenseRange ((inputs.triple period hPeriod green).lagrangianInclusion
        analytic.condition) ∧
      (inputs.triple period hPeriod green).actualAdjointDomain analytic.condition =
        (inputs.triple period hPeriod green).realizationDomain analytic.condition ∧
      (∀ spectralParameter : Real,
        spectralParameter ≠ analytic.referenceParameter →
          (inputs.triple period hPeriod green).LagrangianHasEigenvalue
              analytic.condition spectralParameter ∨
            (inputs.triple period hPeriod green).LagrangianResolventPoint
              analytic.condition spectralParameter) ∧
      (∀ eigenvalue : Real,
        (inputs.triple period hPeriod green).LagrangianHasEigenvalue
            analytic.condition eigenvalue →
          analytic.referenceParameter ≤ eigenvalue) :=
  ⟨analytic.denseDomain period hPeriod,
    analytic.actualAdjointDomain_eq period hPeriod,
    analytic.fredholmAlternative period hPeriod,
    analytic.eigenvalue_ge_referenceParameter period hPeriod⟩

end CanonicalPhysicalScalarFirstSheetShiftedFormData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetShiftedFormClosure4D
end JanusFormal
