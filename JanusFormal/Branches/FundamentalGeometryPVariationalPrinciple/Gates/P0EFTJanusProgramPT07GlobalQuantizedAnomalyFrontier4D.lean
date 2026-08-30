import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalAnomalyFrontier4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT07TruncatedD10CharacteristicCancellation4D

/-!
# Integrated quantized T07 anomaly frontier

This façade combines the existing spectral/heat anomaly frontier with the
quantized families-index constraint and its exact multiplicity-aware D10
cutoff realization.  It is deliberately a frontier certificate: the integral
characteristic-number comparison is input, not yet computed from the full
geometric Janus family, and no equivariant determinant/gerbe trivialization is
manufactured.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT07GlobalQuantizedAnomalyFrontier4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusProgramPGlobalAnomalyFrontier4D
open P0EFTJanusProgramPT07QuantizedPTFamiliesIndexConstraint4D
open P0EFTJanusProgramPT07TruncatedD10CharacteristicCancellation4D

/-- One coherent T07 support package over the same spectral data and
quantized local families-index representative. -/
structure ProgramPT07GlobalQuantizedAnomalyFrontierCertificate4D
    {Base Tangent : Type*}
    (spectral : ProductThroatSpectralData)
    (quantized : QuantizedGeometricFamiliesIndexData4D Base Tangent) where
  spectralHeat : ProgramPGlobalAnomalyFrontierCertificate4D.{0} spectral
  familiesIndexConstraint :
    ProgramPT07QuantizedPTFamiliesIndexConstraintCertificate4D quantized
  exactD10Cutoffs :
    ProgramPT07TruncatedD10CharacteristicCancellationCertificate4D
      quantized spectral

/-- Assemble the integrated frontier from the three independently compiled
certificates. -/
def programPT07GlobalQuantizedAnomalyFrontierCertificate4D
    {Base Tangent : Type*}
    (spectral : ProductThroatSpectralData)
    (quantized : QuantizedGeometricFamiliesIndexData4D Base Tangent) :
    ProgramPT07GlobalQuantizedAnomalyFrontierCertificate4D
      spectral quantized where
  spectralHeat := programPGlobalAnomalyFrontierCertificate4D spectral
  familiesIndexConstraint :=
    programPT07QuantizedPTFamiliesIndexConstraintCertificate4D quantized
  exactD10Cutoffs :=
    programPT07TruncatedD10CharacteristicCancellationCertificate4D
      quantized spectral

/-- The integrated certificate exposes an effective discrete constraint at
every nonzero characteristic-number evaluation. -/
theorem global_quantized_anomaly_discrete_constraint
    {Base Tangent : Type*}
    {spectral : ProductThroatSpectralData}
    {quantized : QuantizedGeometricFamiliesIndexData4D Base Tangent}
    (certificate : ProgramPT07GlobalQuantizedAnomalyFrontierCertificate4D
      spectral quantized)
    (multiplicity : Sector → ℕ)
    (base : Base) (first second : Tangent)
    (hNonzero : quantized.characteristicNumber base first second ≠ 0) :
    totalPTLocalFamiliesIndexCurvature quantized multiplicity base first second = 0 ↔
      multiplicity .plus = multiplicity .minus :=
  certificate.familiesIndexConstraint.discreteConstraint multiplicity base
    first second hNonzero

/-- Public integrated T07 frontier checkpoint. -/
theorem t07_global_quantized_anomaly_frontier_gate
    {Base Tangent : Type*}
    (spectral : ProductThroatSpectralData)
    (quantized : QuantizedGeometricFamiliesIndexData4D Base Tangent) :
    Nonempty (ProgramPT07GlobalQuantizedAnomalyFrontierCertificate4D
      spectral quantized) :=
  ⟨programPT07GlobalQuantizedAnomalyFrontierCertificate4D
    spectral quantized⟩

end
end P0EFTJanusProgramPT07GlobalQuantizedAnomalyFrontier4D
end JanusFormal
