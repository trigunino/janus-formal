import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalInteriorCauchyJetGreenCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalDenseParametrizedAutomaticSixCoefficientPDEClosure4D

/-!
# Minimal canonical PDE closure over the open fundamental strip

The physical source, source measure, open positivity, measure preservation and
density of the physical parametrization are all theorems of the open
fundamental-strip construction.

The remaining PDE inputs are therefore exactly:

* Euler overlap compatibility, boundary-core density and the Green-divergence
  identity;
* one first-jet energy estimate;
* one normal elliptic regularity estimate;
* six tangential Euler coefficient estimates.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalInteriorAutomaticSixCoefficientPDEClosure4D

set_option autoImplicit false
noncomputable section

open Set Topology MeasureTheory
open P0EFTJanusMappingTorusCanonicalLorentzInteriorDenseParametrization4D
open P0EFTJanusMappingTorusCanonicalLorentzInteriorDenseRange4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalInteriorCauchyJetGreenCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalDenseParametrizedAutomaticSixCoefficientPDEClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarAutomaticGardingEnergy4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarNormalEllipticRegularity4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetEulerSixCoefficientClosure4D
open P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D

universe r

variable (period : Real) (hPeriod : period ≠ 0)
variable {Regularity : Type r}
  [NormedAddCommGroup Regularity] [NormedSpace Real Regularity]
  [CompleteSpace Regularity]

/-- Minimal completed-boundary data with physical full support discharged. -/
structure CanonicalPhysicalScalarCanonicalInteriorAutomaticSixCoefficientPDEData
    (massSquared : Real) where
  geometric : CanonicalPhysicalScalarCanonicalInteriorCauchyJetData
    period hPeriod massSquared
  energy : geometric.greenCore.AutomaticEnergyGardingData period hPeriod
  normalRegularity : geometric.greenCore.NormalEllipticRegularityData
    period hPeriod (Regularity := Regularity)
  eulerCoefficients :
    geometric.toCanonicalCauchyJetCompatibilityData.toCompatibilityData.toCauchyJetGeometricData.CauchyJetEulerSixCoefficientData
      period hPeriod
      geometric.toCanonicalCauchyJetCompatibilityData.toCompatibilityData.toCauchyJetGeometricData.canonicalEulerProductRealization

namespace CanonicalPhysicalScalarCanonicalInteriorAutomaticSixCoefficientPDEData

/-- Conversion to the generic dense-parametrized minimal PDE package. -/
def toDenseParametrizedAutomaticSixCoefficientPDEData
    (data : CanonicalPhysicalScalarCanonicalInteriorAutomaticSixCoefficientPDEData
      period hPeriod massSquared (Regularity := Regularity)) :
    CanonicalPhysicalScalarCanonicalDenseParametrizedAutomaticSixCoefficientPDEData
      period hPeriod
      (CanonicalLorentzInteriorParameter period)
      (canonicalLorentzInteriorMeasure period)
      massSquared (Regularity := Regularity) where
  geometric := data.geometric.toDenseParametrizedCauchyJetData
  energy := data.energy
  normalRegularity := data.normalRegularity
  eulerCoefficients := data.eulerCoefficients

/-- Correct completed physical boundary triple. -/
def triple
    (data : CanonicalPhysicalScalarCanonicalInteriorAutomaticSixCoefficientPDEData
      period hPeriod massSquared (Regularity := Regularity)) :=
  data.toDenseParametrizedAutomaticSixCoefficientPDEData.triple

/-- Completed physical boundary inputs. -/
def completedInputs
    (data : CanonicalPhysicalScalarCanonicalInteriorAutomaticSixCoefficientPDEData
      period hPeriod massSquared (Regularity := Regularity)) :=
  data.toDenseParametrizedAutomaticSixCoefficientPDEData.completedInputs

/-- Bounded right inverse of the completed Cauchy trace. -/
def completedExtension
    (data : CanonicalPhysicalScalarCanonicalInteriorAutomaticSixCoefficientPDEData
      period hPeriod massSquared (Regularity := Regularity)) :=
  data.toDenseParametrizedAutomaticSixCoefficientPDEData.completedExtension

/-- Physical graph-elliptic estimate generated from the single component-energy
pairing estimate. -/
def graphEllipticEstimate
    (data : CanonicalPhysicalScalarCanonicalInteriorAutomaticSixCoefficientPDEData
      period hPeriod massSquared (Regularity := Regularity)) :=
  data.toDenseParametrizedAutomaticSixCoefficientPDEData.graphEllipticEstimate

/-- Open-fundamental-strip minimal PDE certificate. -/
theorem certificate
    (data : CanonicalPhysicalScalarCanonicalInteriorAutomaticSixCoefficientPDEData
      period hPeriod massSquared (Regularity := Regularity)) :
    DenseRange (canonicalLorentzInteriorPhysicalMap period hPeriod) ∧
      (P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D.intrinsicCanonicalLorentzVolumeMeasure
          period hPeriod).IsOpenPosMeasure ∧
      Function.Injective
        (canonicalScalarGreenCoreGraphInclusion
          data.geometric.greenCore.core) ∧
      Function.Surjective
        (canonicalScalarGreenCoreCompletedBoundaryTrace
          data.geometric.greenCore.core
          (data.completedInputs.traceBound data.geometric.greenCore)) ∧
      (∀ boundary,
        canonicalScalarGreenCoreCompletedBoundaryTrace
            data.geometric.greenCore.core
            (data.completedInputs.traceBound data.geometric.greenCore)
            (data.completedExtension boundary) = boundary) :=
  ⟨canonicalLorentzInteriorPhysicalMap_denseRange period hPeriod,
    data.toDenseParametrizedAutomaticSixCoefficientPDEData.certificate.1,
    data.toDenseParametrizedAutomaticSixCoefficientPDEData.certificate.2.2.1,
    data.toDenseParametrizedAutomaticSixCoefficientPDEData.certificate.2.2.2.1,
    data.toDenseParametrizedAutomaticSixCoefficientPDEData.certificate.2.2.2.2⟩

end CanonicalPhysicalScalarCanonicalInteriorAutomaticSixCoefficientPDEData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalInteriorAutomaticSixCoefficientPDEClosure4D
end JanusFormal
