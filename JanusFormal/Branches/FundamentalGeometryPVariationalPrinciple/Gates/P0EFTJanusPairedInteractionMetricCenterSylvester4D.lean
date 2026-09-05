import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPairedStrongMaxwellMetricTransportDerivative4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongInteractionDerivative4D

/-! # Interaction root velocity on authentic metric tests at the chart centre

The completed relative matrix has velocity
`Hminus - Hplus - (Hplus * C + C * Hplus) / 2` at zero, where `C` is
the fixed-plus representation of the difference of the two base metrics.
The selected interaction root velocity solves its exact Sylvester equation.
This algebra does not vary the fixed `plusBase.volume` in the action.
-/

namespace JanusFormal
namespace P0EFTJanusPairedInteractionMetricCenterSylvester4D

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 600000

noncomputable section
open Set
open scoped Manifold ContDiff
open P0EFTJanusConvexHelmholtzReconstruction
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixInverse4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2IdentityRootBranch4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2IdentityRootDerivative4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphProjections4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalComponentPDEBlockPairing4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootLift4D
open P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootInverseCore4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartCenter4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalRelativeMetricCoreProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedRelativeMatrixCore4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedRelativeMatrixDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomainOpen4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalInteractionC24D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC0FirstJetProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLocalEuler4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongMetricTotalEulerReduction4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongInteractionDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedRelativeRootSpectralDerivative4D
open P0EFTJanusPairedStrongMaxwellMetricTransportDerivative4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace
attribute [local instance 1900]
  P0EFTJanusProgramPRegularGeneralMetricC2PairedInteractionActionDerivative4D.relativeCoreNormedAddCommGroup
  P0EFTJanusProgramPRegularGeneralMetricC2PairedInteractionActionDerivative4D.relativeCoreNormedSpace

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
private abbrev C2Scalar := CanonicalPhysicalScalarC2JetCore period hPeriod
private abbrev C2Matrix := C2FiniteMatrix period hPeriod 4
private abbrev RelativeCore
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod) :=
  RegularGeneralMetricC2PairedRelativeCore period hPeriod plusBase minusBase

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _
local instance : BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl
local instance : NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (C2Scalar period hPeriod) := inferInstance
local instance : CompleteSpace (C2Scalar period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod

theorem regularGeneralMetricC2IdentityRootInverseC2Matrix_zero :
    regularGeneralMetricC2IdentityRootInverseC2Matrix period hPeriod 0 =
      c2FiniteMatrixIdentity period hPeriod 4 := by
  have hInverse := regularGeneralMetricC2IdentityRoot_mul_inverseC2Matrix
    period hPeriod 0 (zero_mem_c2IdentityRootInvertiblePerturbationDomain period hPeriod)
  simpa only [c2IdentityRootBranch_zero, c2FiniteMatrixProduct_identity_left] using hInverse

theorem regularGeneralMetricC2IdentityRootInverseDerivative_zero_apply
    (hZero : (0 : C2Matrix period hPeriod) ∈
      c2IdentityRootInvertiblePerturbationDomain period hPeriod)
    (direction : C2Matrix period hPeriod) :
    regularGeneralMetricC2IdentityRootInverseDerivative period hPeriod 0 hZero direction =
      -((1 / 2 : Real) • direction) := by
  rw [regularGeneralMetricC2IdentityRootInverseDerivative_apply,
    regularGeneralMetricC2IdentityRootInverseC2Matrix_zero,
    c2IdentityRootDerivative_zero_apply,
    c2FiniteMatrixProduct_identity_right, c2FiniteMatrixProduct_identity_left]

/-- The two inverse-root transport terms and the direct cross-metric term.
The uncollected expression preserves the order of matrix multiplication. -/
def pairedInteractionMetricCenterVelocity
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (plusDirection crossDirection : C2Matrix period hPeriod) : C2Matrix period hPeriod :=
  let product := c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) 4
  let baseRelative := regularGeneralMetricC2VariationMatrix period hPeriod plusBase
    (minusBase.metric.tensor - plusBase.metric.tensor)
  product baseRelative (-((1 / 2 : Real) • plusDirection)) + crossDirection +
    product (-((1 / 2 : Real) • plusDirection)) baseRelative

theorem regularGeneralMetricC2PairedRelativeMatrixDerivative_zero_apply
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (hZero : (0 : RelativeCore period hPeriod plusBase minusBase) ∈
      regularGeneralMetricC2PairedRelativeMatrixDomain period hPeriod plusBase minusBase)
    (direction : RelativeCore period hPeriod plusBase minusBase) :
    regularGeneralMetricC2PairedRelativeMatrixDerivative period hPeriod
        plusBase minusBase 0 hZero direction =
      pairedInteractionMetricCenterVelocity period hPeriod plusBase minusBase
        direction.2.1 direction.2.2 := by
  simp only [regularGeneralMetricC2PairedRelativeMatrixDerivative,
    regularGeneralMetricC2PairedInverseRootOnCore,
    regularGeneralMetricC2PairedInverseRootOnCoreDerivative,
    regularGeneralMetricC2PairedRelativeRightProduct,
    regularGeneralMetricC2PairedRelativeRightProductDerivative,
    regularGeneralMetricC2PairedAffineRelativeMatrix,
    regularGeneralMetricC2PairedAffineRelativeMatrixDerivative,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.zero_apply,
    regularGeneralMetricC2PairedRelativePlusProjection_apply,
    regularGeneralMetricC2PairedRelativeCrossProjection_apply, zero_add, add_zero]
  change _ = pairedInteractionMetricCenterVelocity period hPeriod plusBase minusBase
    direction.2.1 direction.2.2
  simp only [regularGeneralMetricC2IdentityRootInverseC2Matrix_zero,
    regularGeneralMetricC2IdentityRootInverseDerivative_zero_apply,
    c2FiniteMatrixProduct_identity_left, c2FiniteMatrixProduct_identity_right,
    pairedInteractionMetricCenterVelocity]

/-- The root velocity of the actual paired interaction satisfies the exact
Sylvester equation, with every relative-matrix transport term identified. -/
theorem regularGeneralMetricC2PairedRelativeRootDerivative_zero_sylvester
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (hZero : (0 : RelativeCore period hPeriod plusBase minusBase) ∈
      regularGeneralMetricC2PairedLorentzMatrixDomain period hPeriod plusBase minusBase)
    (direction : RelativeCore period hPeriod plusBase minusBase) :
    c2FiniteMatrixSylvester period hPeriod 4
        (regularGeneralMetricC2PairedRelativeRoot period hPeriod plusBase minusBase 0)
        (regularGeneralMetricC2PairedRelativeRootDerivative period hPeriod
          plusBase minusBase 0 hZero direction) =
      pairedInteractionMetricCenterVelocity period hPeriod plusBase minusBase
        direction.2.1 direction.2.2 := by
  have hSylvester := c2IdentityRootDerivative_sylvester period hPeriod
    (regularGeneralMetricC2PairedRelativeMatrix period hPeriod plusBase minusBase 0)
    hZero.2.2.2.1
    (regularGeneralMetricC2PairedRelativeMatrixDerivative period hPeriod
      plusBase minusBase 0 hZero.2.1 direction)
  exact hSylvester.trans
    (regularGeneralMetricC2PairedRelativeMatrixDerivative_zero_apply
      period hPeriod plusBase minusBase hZero.2.1 direction)

section StrongMetricTest
variable {couplings : GlobalCandidateAActionCouplings}
  {NonNullFace NullFace : Type*} [Fintype NonNullFace] [Fintype NullFace]
  (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
  (data : GlobalCandidateAActionData period hPeriod configuration.physical
    couplings NonNullFace NullFace)
  (analysis : GlobalAnalysisData period hPeriod configuration.physical)
  (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
    period hPeriod couplings.matterMassSquared)
  (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)

local instance : NormedAddCommGroup
    (GlobalMinimalPhysicalFieldTangent period hPeriod configuration.physical) :=
  globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup period hPeriod
    configuration data analysis realization plusBase minusBase
    (canonicalDivergenceFreeLLFrame period hPeriod)
local instance : NormedSpace Real
    (GlobalMinimalPhysicalFieldTangent period hPeriod configuration.physical) :=
  globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period hPeriod
    configuration data analysis realization plusBase minusBase
    (canonicalDivergenceFreeLLFrame period hPeriod)

/-- The pre-existing compatibility of the two base metrics supplies the
centre hypothesis used below; no new root admissibility is assumed. -/
theorem pairedStrongInteraction_zero_mem_lorentzMatrixDomain
    (hBase : RegularGeneralMetricC2PairedLorentzChartBaseCompatible
      period hPeriod plusBase minusBase) :
    (0 : RelativeCore period hPeriod plusBase minusBase) ∈
      regularGeneralMetricC2PairedLorentzMatrixDomain
        period hPeriod plusBase minusBase := by
  have hPoint := zero_mem_regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain
    period hPeriod configuration.physical plusBase minusBase hBase
  have hCore :=
    (globalMetricPerturbationPairLorentzChartAdmissible_iff_mem_matrixDomain
      period hPeriod configuration.physical plusBase minusBase 0).1 hPoint
  simpa only [map_zero] using hCore

/-- The velocity formula on the genuine strong-chart metric direction. -/
theorem pairedStrongInteraction_relativeMatrixDerivative_zero
    (hZero : (0 : RelativeCore period hPeriod plusBase minusBase) ∈
      regularGeneralMetricC2PairedRelativeMatrixDomain period hPeriod plusBase minusBase)
    (test : GlobalMinimalPhysicalMetricTest period hPeriod) :
    let projection := globalMinimalPhysicalPairedMetricGaugeLLStrongMetricCLM
      period hPeriod configuration data analysis realization plusBase minusBase
    let direction := regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection
      period hPeriod configuration.physical test
    regularGeneralMetricC2PairedRelativeMatrixDerivative period hPeriod
        plusBase minusBase 0 hZero (projection direction) =
      pairedInteractionMetricCenterVelocity period hPeriod plusBase minusBase
        (regularGeneralMetricC2VariationMatrix period hPeriod plusBase (test .plus))
        (regularGeneralMetricC2VariationMatrix period hPeriod plusBase (test .minus) -
          regularGeneralMetricC2VariationMatrix period hPeriod plusBase (test .plus)) := by
  dsimp only
  rw [regularGeneralMetricC2PairedRelativeMatrixDerivative_zero_apply,
    regularGeneralMetricC2PairedMinimalPhysicalStrongInteractionMetricCore_plus,
    regularGeneralMetricC2PairedMinimalPhysicalStrongInteractionMetricCore_cross]

/-- The selected interaction root is differentiated on authentic independent
plus/minus tensor tests, with no assumption on the direction's volume trace. -/
theorem pairedStrongInteraction_rootDerivative_zero_sylvester
    (hZero : (0 : RelativeCore period hPeriod plusBase minusBase) ∈
      regularGeneralMetricC2PairedLorentzMatrixDomain period hPeriod plusBase minusBase)
    (test : GlobalMinimalPhysicalMetricTest period hPeriod) :
    let projection := globalMinimalPhysicalPairedMetricGaugeLLStrongMetricCLM
      period hPeriod configuration data analysis realization plusBase minusBase
    let direction := regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection
      period hPeriod configuration.physical test
    c2FiniteMatrixSylvester period hPeriod 4
        (regularGeneralMetricC2PairedRelativeRoot period hPeriod plusBase minusBase 0)
        (regularGeneralMetricC2PairedRelativeRootDerivative period hPeriod
          plusBase minusBase 0 hZero (projection direction)) =
      pairedInteractionMetricCenterVelocity period hPeriod plusBase minusBase
        (regularGeneralMetricC2VariationMatrix period hPeriod plusBase (test .plus))
        (regularGeneralMetricC2VariationMatrix period hPeriod plusBase (test .minus) -
          regularGeneralMetricC2VariationMatrix period hPeriod plusBase (test .plus)) := by
  dsimp only
  rw [regularGeneralMetricC2PairedRelativeRootDerivative_zero_sylvester,
    regularGeneralMetricC2PairedMinimalPhysicalStrongInteractionMetricCore_plus,
    regularGeneralMetricC2PairedMinimalPhysicalStrongInteractionMetricCore_cross]

/-- The same exact equation after evaluating at each spacetime point. -/
theorem pairedStrongInteraction_rootDerivative_zero_sylvester_pointwise
    (hZero : (0 : RelativeCore period hPeriod plusBase minusBase) ∈
      regularGeneralMetricC2PairedLorentzMatrixDomain period hPeriod plusBase minusBase)
    (test : GlobalMinimalPhysicalMetricTest period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    let projection := globalMinimalPhysicalPairedMetricGaugeLLStrongMetricCLM
      period hPeriod configuration data analysis realization plusBase minusBase
    let direction := regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection
      period hPeriod configuration.physical test
    let root := c2FiniteMatrixValueAt period hPeriod 4
      (regularGeneralMetricC2PairedRelativeRoot period hPeriod plusBase minusBase 0) point
    let velocity := c2FiniteMatrixValueAt period hPeriod 4
      (regularGeneralMetricC2PairedRelativeRootDerivative period hPeriod
        plusBase minusBase 0 hZero (projection direction)) point
    root * velocity + velocity * root =
      c2FiniteMatrixValueAt period hPeriod 4
        (pairedInteractionMetricCenterVelocity period hPeriod plusBase minusBase
          (regularGeneralMetricC2VariationMatrix period hPeriod plusBase (test .plus))
          (regularGeneralMetricC2VariationMatrix period hPeriod plusBase (test .minus) -
            regularGeneralMetricC2VariationMatrix period hPeriod plusBase (test .plus))) point := by
  have hEquation := pairedStrongInteraction_rootDerivative_zero_sylvester
    period hPeriod configuration data analysis realization plusBase minusBase hZero test
  have hValue := congrArg
    (fun matrix => c2FiniteMatrixValueAt period hPeriod 4 matrix point) hEquation
  simpa only [c2FiniteMatrixSylvester, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.flip_apply, c2FiniteMatrixValueAt_add,
    c2FiniteMatrixValueAt_product] using hValue

end StrongMetricTest
end
end P0EFTJanusPairedInteractionMetricCenterSylvester4D
end JanusFormal
