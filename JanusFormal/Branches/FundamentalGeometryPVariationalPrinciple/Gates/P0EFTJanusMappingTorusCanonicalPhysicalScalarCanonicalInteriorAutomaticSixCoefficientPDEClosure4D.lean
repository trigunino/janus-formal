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
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetGeometricGreenCore4D
open P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D

universe r

variable (period : Real) (hPeriod : period ≠ 0)
variable {massSquared : Real}
variable {Regularity : Type r}
  [NormedAddCommGroup Regularity] [NormedSpace Real Regularity]
  [CompleteSpace Regularity]

/-- Minimal completed-boundary data with physical full support discharged. -/
structure CanonicalPhysicalScalarCanonicalInteriorAutomaticSixCoefficientPDEData
    (massSquared : Real) where
  geometric : CanonicalPhysicalScalarCanonicalInteriorCauchyJetData
    period hPeriod massSquared
  energy : (geometric.greenCore period hPeriod).AutomaticEnergyGardingData period hPeriod
  normalRegularity : (geometric.greenCore period hPeriod).NormalEllipticRegularityData
    period hPeriod (Regularity := Regularity)
  eulerCoefficients :
    (((geometric.toCanonicalCauchyJetCompatibilityData period hPeriod)
      |>.toCompatibilityData period hPeriod).toCauchyJetGeometricData
      period hPeriod).CauchyJetEulerSixCoefficientData
      period hPeriod
      ((((geometric.toCanonicalCauchyJetCompatibilityData period hPeriod)
        |>.toCompatibilityData period hPeriod).toCauchyJetGeometricData
        period hPeriod).canonicalEulerProductRealization period hPeriod)

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
  geometric := data.geometric.toDenseParametrizedCauchyJetData period hPeriod
  energy := data.energy
  normalRegularity := data.normalRegularity
  eulerCoefficients := data.eulerCoefficients

/-- Correct completed physical boundary triple. -/
def triple
    (data : CanonicalPhysicalScalarCanonicalInteriorAutomaticSixCoefficientPDEData
      period hPeriod massSquared (Regularity := Regularity)) :=
  (data.toDenseParametrizedAutomaticSixCoefficientPDEData period hPeriod).triple
    period hPeriod

/-- Completed physical boundary inputs. -/
def completedInputs
    (data : CanonicalPhysicalScalarCanonicalInteriorAutomaticSixCoefficientPDEData
      period hPeriod massSquared (Regularity := Regularity)) :=
  (data.toDenseParametrizedAutomaticSixCoefficientPDEData period hPeriod).completedInputs
    period hPeriod

/-- Bounded right inverse of the completed Cauchy trace. -/
def completedExtension
    (data : CanonicalPhysicalScalarCanonicalInteriorAutomaticSixCoefficientPDEData
      period hPeriod massSquared (Regularity := Regularity)) :=
  (data.toDenseParametrizedAutomaticSixCoefficientPDEData period hPeriod).completedExtension
    period hPeriod

/-- Physical graph-elliptic estimate generated from the single component-energy
pairing estimate. -/
def graphEllipticEstimate
    (data : CanonicalPhysicalScalarCanonicalInteriorAutomaticSixCoefficientPDEData
      period hPeriod massSquared (Regularity := Regularity)) :=
  (data.toDenseParametrizedAutomaticSixCoefficientPDEData period hPeriod).graphEllipticEstimate
    period hPeriod

/-- Open-fundamental-strip minimal PDE certificate. -/
theorem certificate
    (data : CanonicalPhysicalScalarCanonicalInteriorAutomaticSixCoefficientPDEData
      period hPeriod massSquared (Regularity := Regularity)) :
    DenseRange (canonicalLorentzInteriorPhysicalMap period hPeriod) ∧
      (P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D.intrinsicCanonicalLorentzVolumeMeasure
          period hPeriod).IsOpenPosMeasure ∧
      Function.Injective
        (canonicalScalarGreenCoreGraphInclusion
          (data.geometric.greenCore period hPeriod).core) ∧
      Function.Surjective
        (canonicalScalarGreenCoreCompletedBoundaryTrace
          (data.geometric.greenCore period hPeriod).core
          ((data.completedInputs period hPeriod).traceBound period hPeriod
            (data.geometric.greenCore period hPeriod))) ∧
      (∀ boundary,
        canonicalScalarGreenCoreCompletedBoundaryTrace
            (data.geometric.greenCore period hPeriod).core
            ((data.completedInputs period hPeriod).traceBound period hPeriod
              (data.geometric.greenCore period hPeriod))
            (data.completedExtension period hPeriod boundary) = boundary) :=
  ⟨canonicalLorentzInteriorPhysicalMap_denseRange period hPeriod,
    ((data.toDenseParametrizedAutomaticSixCoefficientPDEData period hPeriod).certificate
      period hPeriod).1,
    ((data.toDenseParametrizedAutomaticSixCoefficientPDEData period hPeriod).certificate
      period hPeriod).2.2.1,
    ((data.toDenseParametrizedAutomaticSixCoefficientPDEData period hPeriod).certificate
      period hPeriod).2.2.2.1,
    ((data.toDenseParametrizedAutomaticSixCoefficientPDEData period hPeriod).certificate
      period hPeriod).2.2.2.2⟩

end CanonicalPhysicalScalarCanonicalInteriorAutomaticSixCoefficientPDEData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalInteriorAutomaticSixCoefficientPDEClosure4D
end JanusFormal
