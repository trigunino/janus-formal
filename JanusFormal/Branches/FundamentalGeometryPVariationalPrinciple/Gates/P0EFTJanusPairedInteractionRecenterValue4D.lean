import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPairedInteractionMetricCenterSylvester4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalInteractionC24D

/-! # Exact interaction value at the reconstructed paired centre

At an admissible smooth point the completed relative matrix is exactly the
relative matrix at zero of the reconstructed regular bases. Consequently the
selected root, fixed-volume density and native action have the same values.
This is a value identity; no equality of nearby action germs or derivatives
is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusPairedInteractionRecenterValue4D
set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 600000
noncomputable section
open MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusConvexHelmholtzReconstruction
open P0EFTJanusReciprocalBimetricPotential
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixInverse4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalComponentPDEBlockPairing4D
open P0EFTJanusProgramPGeneralMetricC2IntegratedVolume4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootLift4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartRegularMetric4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartGeometry4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalMetricCoreProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalRelativeMetricCoreProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedRelativeMatrixCore4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedRelativeMatrixC2Exact4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongMetricTotalEulerReduction4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalInteractionC24D
open P0EFTJanusPairedInteractionMetricCenterSylvester4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
private abbrev C2Scalar := CanonicalPhysicalScalarC2JetCore period hPeriod
local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _
local instance : BorelSpace (EffectiveQuotient period hPeriod) where measurable_eq := rfl
local instance : NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (C2Scalar period hPeriod) := inferInstance
local instance : CompleteSpace (C2Scalar period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod

/-- Native relative-core coordinates of the two genuine smooth variations. -/
def pairedInteractionSmoothCore
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (plusVariation minusVariation : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    RegularGeneralMetricC2PairedRelativeCore period hPeriod plusBase minusBase :=
  ((regularGeneralMetricSmoothC2Variation period hPeriod plusBase plusVariation,
    regularGeneralMetricSmoothC2Variation period hPeriod minusBase minusVariation),
   (regularGeneralMetricC2VariationMatrix period hPeriod plusBase plusVariation,
    regularGeneralMetricC2VariationMatrix period hPeriod plusBase minusVariation -
      regularGeneralMetricC2VariationMatrix period hPeriod plusBase plusVariation))

/-- This native point is the actual projection of a pure physical metric variation. -/
theorem pairedInteractionSmoothCore_eq_projected
    (configuration : GlobalFieldConfiguration period hPeriod)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (plusVariation minusVariation : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    pairedInteractionSmoothCore period hPeriod plusBase minusBase plusVariation minusVariation =
      globalMinimalPhysicalPairedRelativeMetricCoreLinearMap period hPeriod configuration plusBase minusBase
        (regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection period hPeriod configuration
          (fun sector => match sector with | .plus => plusVariation | .minus => minusVariation)) := rfl

theorem pairedInteractionRelativeMatrix_zero
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod) :
    regularGeneralMetricC2PairedRelativeMatrix period hPeriod plusBase minusBase 0 =
      regularGeneralMetricC2VariationMatrix period hPeriod plusBase
        (minusBase.metric.tensor - plusBase.metric.tensor) := by
  unfold regularGeneralMetricC2PairedRelativeMatrix
  simp only [Prod.snd_zero, Prod.fst_zero,
    regularGeneralMetricC2IdentityRootInverseC2Matrix_zero, add_zero,
    c2FiniteMatrixProduct_identity_right, c2FiniteMatrixProduct_identity_left]

section Recenter
variable (configuration : GlobalFieldConfiguration period hPeriod)
  (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
  (plusVariation minusVariation : SmoothSymmetricCovariantTwoTensor period hPeriod)
  (hAdmissible : RegularGeneralMetricC2PairedLorentzChartAdmissible period hPeriod
    plusBase minusBase plusVariation minusVariation)

local notation "newPlus" => regularGeneralMetricC2PairedPlusMetric period hPeriod
  plusBase minusBase plusVariation minusVariation hAdmissible
local notation "newMinus" => regularGeneralMetricC2PairedMinusMetric period hPeriod
  plusBase minusBase plusVariation minusVariation hAdmissible
local notation "oldPoint" => pairedInteractionSmoothCore period hPeriod
  plusBase minusBase plusVariation minusVariation

include configuration in
/-- The exact C² sandwich is the new centre's relative matrix, not merely a similar matrix. -/
theorem pairedInteractionRelativeMatrix_recenter_value :
    regularGeneralMetricC2PairedRelativeMatrix period hPeriod plusBase minusBase oldPoint =
      regularGeneralMetricC2PairedRelativeMatrix period hPeriod newPlus newMinus 0 := by
  let direction := regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection period hPeriod configuration
    (fun sector => match sector with | .plus => plusVariation | .minus => minusVariation)
  have hRelative : (newMinus).metric.tensor - (newPlus).metric.tensor =
      regularGeneralMetricC2PairedRelativeTensor period hPeriod plusBase minusBase
        plusVariation minusVariation := by
    change (regularGeneralMetricC2LorentzChartMetric period hPeriod minusBase
        minusVariation hAdmissible.minus_mem).tensor -
      (regularGeneralMetricC2LorentzChartMetric period hPeriod plusBase
        plusVariation hAdmissible.plus_mem).tensor = _
    rw [regularGeneralMetricC2LorentzChartMetric_tensor,
      regularGeneralMetricC2LorentzChartMetric_tensor]
    rfl
  rw [pairedInteractionRelativeMatrix_zero, hRelative,
    pairedInteractionSmoothCore_eq_projected period hPeriod configuration]
  exact regularGeneralMetricC2PairedRelativeMatrix_projected_exact period hPeriod
    configuration plusBase minusBase direction hAdmissible.plus_mem

include configuration in
/-- Identical branch inputs give identical selected roots; no principal-root equivariance is assumed. -/
theorem pairedInteractionRelativeRoot_recenter_value :
    regularGeneralMetricC2PairedRelativeRoot period hPeriod plusBase minusBase oldPoint =
      regularGeneralMetricC2PairedRelativeRoot period hPeriod newPlus newMinus 0 := by
  exact congrArg (P0EFTJanusMappingTorusCanonicalPhysicalC2IdentityRootBranch4D.c2IdentityRootBranch
    period hPeriod)
    (pairedInteractionRelativeMatrix_recenter_value period hPeriod configuration
      plusBase minusBase plusVariation minusVariation hAdmissible)

/-- The reconstructed frame retains the exact fixed plus-volume field. -/
theorem pairedInteractionRecenterPlus_volume : (newPlus).volume = plusBase.volume := rfl

include configuration in
/-- Equality of the full completed interaction densities, with the original volume and couplings. -/
theorem pairedInteractionC2Density_recenter_value
    (interactionScale : Real) (coefficients : PotentialCoefficients) :
    regularGeneralMetricC2PairedInteractionC2Density period hPeriod plusBase minusBase
        interactionScale coefficients oldPoint =
      regularGeneralMetricC2PairedInteractionC2Density period hPeriod newPlus newMinus
        interactionScale coefficients 0 := by
  unfold regularGeneralMetricC2PairedInteractionC2Density
  rw [pairedInteractionRelativeRoot_recenter_value period hPeriod configuration
    plusBase minusBase plusVariation minusVariation hAdmissible]
  rfl

include configuration in
/-- Equality of native action values for every finite measure, strictly at the two stated points. -/
theorem pairedInteractionC2Action_recenter_value
    (measure : Measure (EffectiveQuotient period hPeriod)) [IsFiniteMeasure measure]
    (interactionScale : Real) (coefficients : PotentialCoefficients) :
    regularGeneralMetricC2PairedInteractionC2Action period hPeriod plusBase minusBase measure
        interactionScale coefficients oldPoint =
      regularGeneralMetricC2PairedInteractionC2Action period hPeriod newPlus newMinus measure
        interactionScale coefficients 0 := by
  exact congrArg (canonicalPhysicalC2ScalarIntegralCLM period hPeriod measure)
    (pairedInteractionC2Density_recenter_value period hPeriod configuration
      plusBase minusBase plusVariation minusVariation hAdmissible interactionScale coefficients)

end Recenter
end
end P0EFTJanusPairedInteractionRecenterValue4D
end JanusFormal
