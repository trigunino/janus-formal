import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalWaveExactEnergyPDEClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCompletedNormalRegularity4D

/-!
# Reduced canonical physical scalar PDE closure

This is the smallest current boundary-theory interface.

Already discharged:

* full support of the physical Lorentz volume;
* smooth bulk `L²` density and minimal-core density;
* smooth periodic and antiperiodic boundary-core density;
* the tubular inverse and global smooth Cauchy extension;
* all fixed normal profile moments;
* the first elementary `H¹` graph inequality;
* all six coefficient constants and integrability estimates;
* all normal-regularity constants and extension arguments.

The remaining PDE data are:

* scalar-wave naturality and the global Euler-divergence identity;
* one exact first-jet energy identity with a bounded zeroth-order operator;
* one bounded completed-graph regularity map with bounded normal trace;
* six bounded boundary coefficient operators and their exact residual expansion.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalReducedPDEClosure4D

set_option autoImplicit false
noncomputable section

open Set Topology MeasureTheory
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalWaveCauchyJetGreenCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalWaveExactEnergyPDEClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarGardingIdentity4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCompletedNormalRegularity4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetGeometricGreenCore4D
open P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D

universe r

variable (period : Real) (hPeriod : period ≠ 0)
variable {massSquared : Real}
variable {Regularity : Type r}
  [NormedAddCommGroup Regularity] [NormedSpace Real Regularity]
  [CompleteSpace Regularity]

/-- Smallest current canonical physical scalar boundary-theory package. -/
structure CanonicalPhysicalScalarCanonicalReducedPDEData
    (massSquared : Real) where
  geometric : CanonicalPhysicalScalarCanonicalWaveCauchyJetData
    period hPeriod massSquared
  energyIdentity : (geometric.greenCore period hPeriod).ExactEnergyGardingIdentityData
    period hPeriod
  completedNormalRegularity : (geometric.greenCore period hPeriod).CompletedNormalRegularityData
    period hPeriod (Regularity := Regularity)
  eulerCoefficients :
    geometric.toCanonicalCauchyJetCompatibilityData.toCompatibilityData.toCauchyJetGeometricData.CauchyJetEulerSixBoundedCoefficientData
      period hPeriod
      geometric.toCanonicalCauchyJetCompatibilityData.toCompatibilityData.toCauchyJetGeometricData.canonicalEulerProductRealization

namespace CanonicalPhysicalScalarCanonicalReducedPDEData

/-- Conversion to the exact-energy PDE package. -/
def toWaveExactEnergyPDEData
    (data : CanonicalPhysicalScalarCanonicalReducedPDEData
      period hPeriod massSquared (Regularity := Regularity)) :
    CanonicalPhysicalScalarCanonicalWaveExactEnergyPDEData
      period hPeriod massSquared (Regularity := Regularity) where
  geometric := data.geometric
  energyIdentity := data.energyIdentity
  normalRegularity :=
    { smoothRegularity :=
        data.completedNormalRegularity.smoothRegularity period hPeriod
          (data.geometric.greenCore period hPeriod)
      normalTrace := data.completedNormalRegularity.normalTrace
      normal_agrees := data.completedNormalRegularity.normal_agrees
      ellipticConstant :=
        ‖data.completedNormalRegularity.completedRegularity‖ ^ 2
      ellipticConstant_nonnegative := sq_nonneg _
      elliptic_bound_sq := by
        intro field
        have hBound := data.completedNormalRegularity.smoothRegularity_bound_sq
          period hPeriod (data.geometric.greenCore period hPeriod) field
        have hGraphSq :
            ‖canonicalScalarGreenCoreToGraph
                (data.geometric.greenCore period hPeriod).core field‖ ^ 2 =
              ‖(data.geometric.greenCore period hPeriod).core.inclusion field‖ ^ 2 +
                ‖(data.geometric.greenCore period hPeriod).core.operator field‖ ^ 2 := by
          exact WithLp.prod_norm_sq_eq_of_L2
            (canonicalScalarGreenCoreToGraph
              (data.geometric.greenCore period hPeriod).core field).1
        rw [hGraphSq] at hBound
        exact hBound }
  eulerCoefficients := data.eulerCoefficients

/-- Correct completed physical boundary triple. -/
def triple
    (data : CanonicalPhysicalScalarCanonicalReducedPDEData
      period hPeriod massSquared (Regularity := Regularity)) :=
  (data.toWaveExactEnergyPDEData period hPeriod).triple period hPeriod

/-- Completed physical boundary inputs. -/
def completedInputs
    (data : CanonicalPhysicalScalarCanonicalReducedPDEData
      period hPeriod massSquared (Regularity := Regularity)) :=
  (data.toWaveExactEnergyPDEData period hPeriod).completedInputs period hPeriod

/-- Completed physical Cauchy trace. -/
def completedBoundaryTrace
    (data : CanonicalPhysicalScalarCanonicalReducedPDEData
      period hPeriod massSquared (Regularity := Regularity)) :=
  canonicalScalarGreenCoreCompletedBoundaryTrace
    (data.geometric.greenCore period hPeriod).core
    ((data.completedInputs period hPeriod).traceBound period hPeriod
      (data.geometric.greenCore period hPeriod))

/-- Bounded right inverse of the completed Cauchy trace. -/
def completedExtension
    (data : CanonicalPhysicalScalarCanonicalReducedPDEData
      period hPeriod massSquared (Regularity := Regularity)) :=
  (data.toWaveExactEnergyPDEData period hPeriod).completedExtension period hPeriod

/-- Physical graph-elliptic estimate. -/
def graphEllipticEstimate
    (data : CanonicalPhysicalScalarCanonicalReducedPDEData
      period hPeriod massSquared (Regularity := Regularity)) :=
  data.energyIdentity.toGraphEllipticEstimate period hPeriod
    (data.geometric.greenCore period hPeriod)

/-- Complete physical normal graph estimate. -/
def normalGraphEstimate
    (data : CanonicalPhysicalScalarCanonicalReducedPDEData
      period hPeriod massSquared (Regularity := Regularity)) :=
  data.completedNormalRegularity.toNormalGraphEstimate period hPeriod
    (data.geometric.greenCore period hPeriod)

/-- Reduced physical PDE certificate. -/
theorem certificate
    (data : CanonicalPhysicalScalarCanonicalReducedPDEData
      period hPeriod massSquared (Regularity := Regularity)) :
    (P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D.intrinsicCanonicalLorentzVolumeMeasure
        period hPeriod).IsOpenPosMeasure ∧
      DenseRange
        (P0EFTJanusMappingTorusCanonicalLatitudeSmoothBoundaryCores4D.canonicalLatitudeSmoothPeriodicValueEmbedding
          period) ∧
      DenseRange
        (P0EFTJanusMappingTorusCanonicalLatitudeSmoothBoundaryCores4D.canonicalLatitudeSmoothAntiperiodicNormalEmbedding
          period) ∧
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
  ⟨P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerCanonicalFullSupport4D.intrinsicCanonicalLorentzVolumeMeasure_isOpenPosMeasure
      period hPeriod,
    (data.geometric.certificate period hPeriod).2.1,
    (data.geometric.certificate period hPeriod).2.2.1,
    ((data.toWaveExactEnergyPDEData period hPeriod).certificate period hPeriod).2.1,
    ((data.toWaveExactEnergyPDEData period hPeriod).certificate period hPeriod).2.2,
    (((data.toWaveExactEnergyPDEData period hPeriod).toWaveBoundedCoefficientPDEData
      period hPeriod).certificate period hPeriod).2.2⟩

end CanonicalPhysicalScalarCanonicalReducedPDEData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalReducedPDEClosure4D
end JanusFormal
