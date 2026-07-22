import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalInteriorCauchyJetGreenCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalDenseParametrizedAutomaticSixCoefficientPDEClosure4D

/-!
# Minimal canonical PDE closure over the open fundamental strip

This is the concrete form of the dense-parametrized minimal boundary package.
The source type, source measure, open positivity and measure preservation are all
fixed by the open fundamental-strip construction.  The only remaining support
input is density of that explicit physical map.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalInteriorAutomaticSixCoefficientPDEClosure4D

set_option autoImplicit false
noncomputable section

open Set Topology MeasureTheory
open P0EFTJanusMappingTorusCanonicalLorentzInteriorDenseParametrization4D
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

/-- Minimal completed-boundary data with the physical measure source fixed to the
open fundamental strip. -/
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
  ⟨data.geometric.interiorDenseRange.denseRange,
    data.toDenseParametrizedAutomaticSixCoefficientPDEData.certificate.1,
    data.toDenseParametrizedAutomaticSixCoefficientPDEData.certificate.2.2.1,
    data.toDenseParametrizedAutomaticSixCoefficientPDEData.certificate.2.2.2.1,
    data.toDenseParametrizedAutomaticSixCoefficientPDEData.certificate.2.2.2.2⟩

end CanonicalPhysicalScalarCanonicalInteriorAutomaticSixCoefficientPDEData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalInteriorAutomaticSixCoefficientPDEClosure4D
end JanusFormal
