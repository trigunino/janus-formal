import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetProfileIntegrability4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetPDEClosure4D

/-!
# Reduced explicit Cauchy-jet PDE closure

The fixed value and normal profiles are bounded and compactly supported, so their
squares are integrable with respect to the weighted normal coarea measure.  The
profile-moment field can therefore be removed from the physical PDE input.

The only extension-specific analytic statement that remains is the product
estimate for the Euler residual of the explicit Cauchy jet.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetReducedPDEClosure4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetProfileIntegrability4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetCompatibilityGreenCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetCompatibilityBridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetGeometricGreenCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetEulerL2Reduction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEnergyGarding4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarNormalEllipticRegularity4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetPDEClosure4D
open P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D

universe x y r

variable (period : Real) (hPeriod : period ≠ 0)
variable {Regularity : Type r}
  [NormedAddCommGroup Regularity] [NormedSpace Real Regularity]
  [CompleteSpace Regularity]

/-- Explicit-Cauchy PDE data after the fixed profile integrals have been
closed. -/
structure CanonicalPhysicalScalarCauchyJetReducedPDEData
    (massSquared : Real)
    (ValueCore : Type x) (NormalCore : Type y)
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore] where
  geometric : CanonicalPhysicalScalarCauchyJetCompatibilityData
    period hPeriod massSquared ValueCore NormalCore
  gardingEnergy : geometric.greenCore.EnergyGardingData period hPeriod
  normalRegularity : geometric.greenCore.NormalEllipticRegularityData
    period hPeriod (Regularity := Regularity)
  eulerRealization : geometric.toCauchyJetGeometricData.CauchyJetEulerProductRealizationData
    period hPeriod
  eulerEstimate : geometric.toCauchyJetGeometricData.CauchyJetEulerProductEstimateData
    period hPeriod eulerRealization

namespace CanonicalPhysicalScalarCauchyJetReducedPDEData

/-- Conversion to the complete four-layer PDE package. -/
def toPDEData
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (reduced : CanonicalPhysicalScalarCauchyJetReducedPDEData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity)) :
    CanonicalPhysicalScalarCauchyJetPDEData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity) where
  geometric := reduced.geometric
  gardingEnergy := reduced.gardingEnergy
  normalRegularity := reduced.normalRegularity
  profile := canonicalLatitudeCauchyJetProfileIntegrabilityData
  eulerRealization := reduced.eulerRealization
  eulerEstimate := reduced.eulerEstimate

/-- Genuine completed physical boundary triple. -/
def triple
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (reduced : CanonicalPhysicalScalarCauchyJetReducedPDEData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity)) :=
  reduced.toPDEData.triple

/-- Complete physical boundary input. -/
def completedInputs
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (reduced : CanonicalPhysicalScalarCauchyJetReducedPDEData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity)) :=
  reduced.toPDEData.completedInputs

/-- Bounded completed Cauchy extension. -/
def completedExtension
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (reduced : CanonicalPhysicalScalarCauchyJetReducedPDEData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity)) :=
  reduced.toPDEData.completedExtension

/-- Reduced PDE boundary certificate. -/
theorem certificate
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (reduced : CanonicalPhysicalScalarCauchyJetReducedPDEData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity)) :
    reduced.geometric.greenCore.MinimalCoreDense period hPeriod ∧
      Function.Injective
        (canonicalScalarGreenCoreGraphInclusion
          reduced.geometric.greenCore.core) ∧
      Function.Surjective
        (canonicalScalarGreenCoreCompletedBoundaryTrace
          reduced.geometric.greenCore.core
          (reduced.completedInputs.traceBound reduced.geometric.greenCore)) ∧
      (∀ boundary,
        canonicalScalarGreenCoreCompletedBoundaryTrace
            reduced.geometric.greenCore.core
            (reduced.completedInputs.traceBound reduced.geometric.greenCore)
            (reduced.completedExtension boundary) = boundary) :=
  ⟨(reduced.toPDEData.certificate).2.1,
    (reduced.toPDEData.certificate).2.2.1,
    (reduced.toPDEData.certificate).2.2.2.1,
    (reduced.toPDEData.certificate).2.2.2.2⟩

end CanonicalPhysicalScalarCauchyJetReducedPDEData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetReducedPDEClosure4D
end JanusFormal
