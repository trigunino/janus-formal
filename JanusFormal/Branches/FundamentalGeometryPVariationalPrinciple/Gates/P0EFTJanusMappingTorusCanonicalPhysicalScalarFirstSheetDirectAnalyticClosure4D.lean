import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetRellichCompactness4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarCompletedBoundaryTripleActualAdjoint4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarCompletedBoundaryTripleAnalyticClosure4D

/-!
# Direct physical scalar analytic closure

The physical completed boundary triple now supports its own resolvent and
spectral calculus.  The final analytic inputs for one physical boundary
condition are therefore reduced to:

* maximal regularity for the true Hilbert adjoint;
* coercivity and surjectivity of one shifted realization;
* the canonical physical Rellich compactness theorem;
* a lower quadratic-form bound.

Minimal-core density and the graph/trace completion are already contained in the
physical boundary-triple input.  The resulting closure gives actual
self-adjointness, compact resolvent, Fredholm alternative, spectral completeness
and the lower spectral bound directly on the corrected completed graph.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetDirectAnalyticClosure4D

set_option autoImplicit false
noncomputable section

open Set Topology Module End
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetGreenCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetRellichCompactness4D
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D
open P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleActualAdjoint4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleResolvent4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleCompactSpectrum4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleFredholmAlternative4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleSemiboundedSpectrum4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleAnalyticClosure4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev BoundaryL2 := CanonicalPhysicalScalarFirstSheetL2 period

/-- Final direct physical scalar analytic inputs. -/
structure CanonicalPhysicalScalarFirstSheetDirectAnalyticData
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (inputs : green.CompletedBoundaryTripleInputs period hPeriod) where
  condition : CanonicalScalarHilbertLagrangianBoundaryCondition
    (BoundaryL2 period)
  adjointRegularity : (inputs.triple green).MaximalAdjointRegularity condition
  referenceParameter : Real
  coercive : (inputs.triple green).LagrangianCoerciveSurjectiveAt
    condition referenceParameter
  rellich : PhysicalH1RellichCompactness period hPeriod
  semibounded : (inputs.triple green).LagrangianSemiboundedData condition

namespace CanonicalPhysicalScalarFirstSheetDirectAnalyticData

/-- Direct compact physical reference resolvent. -/
noncomputable def compactResolvent
    {green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared}
    {inputs : green.CompletedBoundaryTripleInputs period hPeriod}
    (analytic : CanonicalPhysicalScalarFirstSheetDirectAnalyticData
      period hPeriod green inputs) :
    (inputs.triple green).LagrangianCompactResolventAt
      analytic.condition analytic.referenceParameter :=
  green.compactResolventAt period hPeriod inputs analytic.condition
    analytic.referenceParameter analytic.coercive analytic.rellich

/-- Conversion to the generic direct analytic closure. -/
noncomputable def toGeneric
    {green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared}
    {inputs : green.CompletedBoundaryTripleInputs period hPeriod}
    (analytic : CanonicalPhysicalScalarFirstSheetDirectAnalyticData
      period hPeriod green inputs) :
    (inputs.triple green).LagrangianAnalyticClosureData
      analytic.condition where
  minimalDense := inputs.minimalDense
  adjointRegularity := analytic.adjointRegularity
  referenceParameter := analytic.referenceParameter
  compactResolvent := analytic.compactResolvent period hPeriod
  semibounded := analytic.semibounded

/-- Density of the physical realization domain. -/
theorem denseDomain
    {green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared}
    {inputs : green.CompletedBoundaryTripleInputs period hPeriod}
    (analytic : CanonicalPhysicalScalarFirstSheetDirectAnalyticData
      period hPeriod green inputs) :
    DenseRange ((inputs.triple green).lagrangianInclusion
      analytic.condition) :=
  (analytic.toGeneric period hPeriod).denseDomain
    (inputs.triple green) analytic.condition

/-- Actual physical Hilbert adjoint domain equality. -/
theorem actualAdjointDomain_eq
    {green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared}
    {inputs : green.CompletedBoundaryTripleInputs period hPeriod}
    (analytic : CanonicalPhysicalScalarFirstSheetDirectAnalyticData
      period hPeriod green inputs) :
    (inputs.triple green).actualAdjointDomain analytic.condition =
      (inputs.triple green).realizationDomain analytic.condition :=
  (analytic.toGeneric period hPeriod).actualAdjointDomain_eq
    (inputs.triple green) analytic.condition

/-- Physical Fredholm alternative away from the reference parameter. -/
theorem fredholmAlternative
    {green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared}
    {inputs : green.CompletedBoundaryTripleInputs period hPeriod}
    (analytic : CanonicalPhysicalScalarFirstSheetDirectAnalyticData
      period hPeriod green inputs)
    (spectralParameter : Real)
    (hParameter : spectralParameter ≠ analytic.referenceParameter) :
    (inputs.triple green).LagrangianHasEigenvalue
        analytic.condition spectralParameter ∨
      (inputs.triple green).LagrangianResolventPoint
        analytic.condition spectralParameter :=
  (analytic.toGeneric period hPeriod).fredholmAlternative
    (inputs.triple green) analytic.condition spectralParameter hParameter

/-- Physical lower spectral bound. -/
theorem eigenvalue_ge_lowerBound
    {green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared}
    {inputs : green.CompletedBoundaryTripleInputs period hPeriod}
    (analytic : CanonicalPhysicalScalarFirstSheetDirectAnalyticData
      period hPeriod green inputs)
    (eigenvalue : Real)
    (hEigenvalue : (inputs.triple green).LagrangianHasEigenvalue
      analytic.condition eigenvalue) :
    analytic.semibounded.lowerBound ≤ eigenvalue :=
  (analytic.toGeneric period hPeriod).eigenvalue_ge_lowerBound
    (inputs.triple green) analytic.condition eigenvalue hEigenvalue

/-- Spectral completeness of the direct physical compact resolvent. -/
theorem spectral_complete
    {green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared}
    {inputs : green.CompletedBoundaryTripleInputs period hPeriod}
    (analytic : CanonicalPhysicalScalarFirstSheetDirectAnalyticData
      period hPeriod green inputs) :
    (⨆ eigenvalue : Real,
      Module.End.eigenspace
        ((analytic.compactResolvent period hPeriod).bounded.ambientResolvent
          (inputs.triple green) analytic.condition
            analytic.referenceParameter).toLinearMap eigenvalue)ᗮ = ⊥ :=
  (analytic.toGeneric period hPeriod).spectral_complete
    (inputs.triple green) analytic.condition

/-- Direct physical analytic-closure certificate. -/
theorem certificate
    {green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared}
    {inputs : green.CompletedBoundaryTripleInputs period hPeriod}
    (analytic : CanonicalPhysicalScalarFirstSheetDirectAnalyticData
      period hPeriod green inputs) :
    DenseRange ((inputs.triple green).lagrangianInclusion
        analytic.condition) ∧
      (inputs.triple green).actualAdjointDomain analytic.condition =
        (inputs.triple green).realizationDomain analytic.condition ∧
      (∀ spectralParameter : Real,
        spectralParameter ≠ analytic.referenceParameter →
          (inputs.triple green).LagrangianHasEigenvalue
              analytic.condition spectralParameter ∨
            (inputs.triple green).LagrangianResolventPoint
              analytic.condition spectralParameter) ∧
      (∀ eigenvalue : Real,
        (inputs.triple green).LagrangianHasEigenvalue
            analytic.condition eigenvalue →
          analytic.semibounded.lowerBound ≤ eigenvalue) ∧
      (⨆ eigenvalue : Real,
        Module.End.eigenspace
          ((analytic.compactResolvent period hPeriod).bounded.ambientResolvent
            (inputs.triple green) analytic.condition
              analytic.referenceParameter).toLinearMap eigenvalue)ᗮ = ⊥ :=
  (analytic.toGeneric period hPeriod).certificate
    (inputs.triple green) analytic.condition

end CanonicalPhysicalScalarFirstSheetDirectAnalyticData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetDirectAnalyticClosure4D
end JanusFormal
