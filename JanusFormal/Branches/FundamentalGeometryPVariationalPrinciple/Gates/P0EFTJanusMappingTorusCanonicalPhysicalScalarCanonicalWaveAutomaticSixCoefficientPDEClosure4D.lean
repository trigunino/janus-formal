import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalWaveCauchyJetGreenCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalInteriorAutomaticSixCoefficientPDEClosure4D

/-!
# Minimal canonical PDE closure from scalar-wave naturality

Full support, smooth boundary-core density, the tubular inverse, Cauchy
extension, minimal-core density and the first elementary graph inequality are all
theorems.

The completed physical boundary triple is now assembled from:

* naturality of the scalar wave operator on the total holonomic atlas;
* the global Euler-skew/divergence integral identity;
* one first-jet energy estimate;
* one normal elliptic regularity estimate;
* six tangential Euler coefficient estimates for the explicit Cauchy lift.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalWaveAutomaticSixCoefficientPDEClosure4D

set_option autoImplicit false
noncomputable section

open Set Topology MeasureTheory
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalWaveCauchyJetGreenCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalInteriorAutomaticSixCoefficientPDEClosure4D
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

/-- Minimal canonical PDE data after reducing Euler overlap compatibility to
wave naturality. -/
structure CanonicalPhysicalScalarCanonicalWaveAutomaticSixCoefficientPDEData
    (massSquared : Real) where
  geometric : CanonicalPhysicalScalarCanonicalWaveCauchyJetData
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

namespace CanonicalPhysicalScalarCanonicalWaveAutomaticSixCoefficientPDEData

/-- Conversion to the established canonical minimal PDE package. -/
def toCanonicalInteriorAutomaticSixCoefficientPDEData
    (data : CanonicalPhysicalScalarCanonicalWaveAutomaticSixCoefficientPDEData
      period hPeriod massSquared (Regularity := Regularity)) :
    CanonicalPhysicalScalarCanonicalInteriorAutomaticSixCoefficientPDEData
      period hPeriod massSquared (Regularity := Regularity) where
  geometric := data.geometric.toCanonicalInteriorCauchyJetData period hPeriod
  energy := data.energy
  normalRegularity := data.normalRegularity
  eulerCoefficients := data.eulerCoefficients

/-- Correct completed physical boundary triple. -/
def triple
    (data : CanonicalPhysicalScalarCanonicalWaveAutomaticSixCoefficientPDEData
      period hPeriod massSquared (Regularity := Regularity)) :=
  (data.toCanonicalInteriorAutomaticSixCoefficientPDEData period hPeriod).triple
    period hPeriod

/-- Completed physical boundary inputs. -/
def completedInputs
    (data : CanonicalPhysicalScalarCanonicalWaveAutomaticSixCoefficientPDEData
      period hPeriod massSquared (Regularity := Regularity)) :=
  (data.toCanonicalInteriorAutomaticSixCoefficientPDEData period hPeriod).completedInputs
    period hPeriod

/-- Bounded right inverse of the completed Cauchy trace. -/
def completedExtension
    (data : CanonicalPhysicalScalarCanonicalWaveAutomaticSixCoefficientPDEData
      period hPeriod massSquared (Regularity := Regularity)) :=
  (data.toCanonicalInteriorAutomaticSixCoefficientPDEData period hPeriod).completedExtension
    period hPeriod

/-- Physical graph-elliptic estimate. -/
def graphEllipticEstimate
    (data : CanonicalPhysicalScalarCanonicalWaveAutomaticSixCoefficientPDEData
      period hPeriod massSquared (Regularity := Regularity)) :=
  (data.toCanonicalInteriorAutomaticSixCoefficientPDEData period hPeriod).graphEllipticEstimate
    period hPeriod

/-- Wave-natural minimal PDE certificate. -/
theorem certificate
    (data : CanonicalPhysicalScalarCanonicalWaveAutomaticSixCoefficientPDEData
      period hPeriod massSquared (Regularity := Regularity)) :
    (∀ field : SmoothScalarField
        period hPeriod,
      P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerAtlas4D.CanonicalPhysicalScalarEulerAtlasCompatible
        period hPeriod massSquared field) ∧
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
  ⟨(data.geometric.certificate period hPeriod).1,
    ((data.toCanonicalInteriorAutomaticSixCoefficientPDEData period hPeriod).certificate
      period hPeriod).2.2.1,
    ((data.toCanonicalInteriorAutomaticSixCoefficientPDEData period hPeriod).certificate
      period hPeriod).2.2.2.1,
    ((data.toCanonicalInteriorAutomaticSixCoefficientPDEData period hPeriod).certificate
      period hPeriod).2.2.2.2⟩

end CanonicalPhysicalScalarCanonicalWaveAutomaticSixCoefficientPDEData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalWaveAutomaticSixCoefficientPDEClosure4D
end JanusFormal
