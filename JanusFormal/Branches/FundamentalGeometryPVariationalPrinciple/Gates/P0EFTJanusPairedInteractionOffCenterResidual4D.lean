import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPairedInteractionDerivativeRecenter4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPairedStrongInteractionResidualPairing4D

/-! # Concrete interaction residual at an arbitrary admissible smooth shift

The exact native derivative transport identifies the off-centre derivative
with the pairing of the two smooth interaction tensors at the reconstructed
metrics. All root admissibility follows from the original smooth shift.
-/

namespace JanusFormal
namespace P0EFTJanusPairedInteractionOffCenterResidual4D
set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 600000
noncomputable section
open Set MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusConvexHelmholtzReconstruction
open P0EFTJanusReciprocalBimetricPotential
open P0EFTJanusMatrixInteractionFrechetNoether
open P0EFTJanusPositiveRawSplitCharpolyContDiffLocalRootBranch4D
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVFirstLevel4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVIntegratedMaster4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixInverse4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphProjections4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalComponentPDEBlockPairing4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootLift4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartGeometry4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalRelativeMetricCoreProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomainOpen4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalInteractionC24D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC0FirstJetProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalNineBlockC24D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLocalEuler4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongMetricTotalEulerReduction4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongInteractionDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedRelativeRootSpectralDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedInteractionActionDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMetricResidualTestSeparation4D
open P0EFTJanusPairedInteractionMetricCenterSylvester4D
open P0EFTJanusPairedInteractionSmoothMetricResidual4D
open P0EFTJanusPairedStrongInteractionResidualPairing4D
open P0EFTJanusPairedInteractionRecenterValue4D
open P0EFTJanusPairedInteractionDerivativeRecenter4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace
attribute [local instance 1900]
  P0EFTJanusProgramPRegularGeneralMetricC2PairedInteractionActionDerivative4D.relativeCoreNormedAddCommGroup
  P0EFTJanusProgramPRegularGeneralMetricC2PairedInteractionActionDerivative4D.relativeCoreNormedSpace

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
private abbrev Matrix4 := Matrix (Fin 4) (Fin 4) Real
private abbrev C2Scalar := CanonicalPhysicalScalarC2JetCore period hPeriod
private abbrev C2Matrix := C2FiniteMatrix period hPeriod 4
private abbrev RelativeCore (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod) :=
  RegularGeneralMetricC2PairedRelativeCore period hPeriod plusBase minusBase
local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _
local instance : BorelSpace (EffectiveQuotient period hPeriod) where measurable_eq := rfl
local instance : IsFiniteMeasure (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod
local instance : NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (C2Scalar period hPeriod) := inferInstance
local instance : CompleteSpace (C2Scalar period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod
local instance : NormedRing Matrix4 := Matrix.frobeniusNormedRing
local instance : NormedAlgebra Real Matrix4 := Matrix.frobeniusNormedAlgebra
@[reducible] local instance canonicalMatrixNormedAddCommGroup : NormedAddCommGroup Matrix4 :=
  NonUnitalNormedRing.toNormedAddCommGroup
local instance : AddCommGroup Matrix4 := canonicalMatrixNormedAddCommGroup.toAddCommGroup
local instance canonicalMatrixPseudoMetricSpace : PseudoMetricSpace Matrix4 :=
  canonicalMatrixNormedAddCommGroup.toPseudoMetricSpace
local instance canonicalMatrixUniformSpace : UniformSpace Matrix4 :=
  canonicalMatrixPseudoMetricSpace.toUniformSpace
local instance : TopologicalSpace Matrix4 := canonicalMatrixUniformSpace.toTopologicalSpace
@[reducible] local instance canonicalMatrixNormedSpace : NormedSpace Real Matrix4 :=
  NormedAlgebra.toNormedSpace Matrix4
local instance : Module Real Matrix4 := canonicalMatrixNormedSpace.toModule
local instance : CompleteSpace Matrix4 := FiniteDimensional.complete Real Matrix4

attribute [local irreducible] regularGeneralMetricC2PairedInteractionC2ActionDerivative
  regularGeneralMetricC2PairedRelativeRootDerivative regularGeneralMetricC2PairedLorentzMatrixDomain

private theorem matrixValue_sylvester (root velocity : C2Matrix period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    c2FiniteMatrixValueAt period hPeriod 4
        (c2FiniteMatrixSylvester period hPeriod 4 root velocity) point =
      c2FiniteMatrixValueAt period hPeriod 4 root point *
          c2FiniteMatrixValueAt period hPeriod 4 velocity point +
        c2FiniteMatrixValueAt period hPeriod 4 velocity point *
          c2FiniteMatrixValueAt period hPeriod 4 root point := by
  change c2FiniteMatrixValueAt period hPeriod 4
    (c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) 4 root velocity +
      c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) 4 velocity root) point = _
  rw [c2FiniteMatrixValueAt_add, c2FiniteMatrixValueAt_product,
    c2FiniteMatrixValueAt_product]

private theorem centerSpectralDensity_eq_pairing_of_sylvester
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (hRoot : RegularGeneralMetricC2IdentityRootAdmissible period hPeriod plusBase
      (minusBase.metric.tensor - plusBase.metric.tensor))
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (test : GlobalMinimalPhysicalMetricTest period hPeriod)
    (point : EffectiveQuotient period hPeriod) (velocity : Matrix4)
    (hEquation : canonicalSylvesterOperator
        (pairedInteractionCenterRoot period hPeriod plusBase minusBase point) velocity =
      pairedInteractionMetricMatrixVelocity period hPeriod plusBase minusBase .plus point
        (fun row column => (test .plus).tensor point (plusBase.frame row point) (plusBase.frame column point)) +
      pairedInteractionMetricMatrixVelocity period hPeriod plusBase minusBase .minus point
        (fun row column => (test .minus).tensor point (plusBase.frame row point) (plusBase.frame column point))) :
    (-interactionScale * plusBase.volume point) * matrixSpectralPotentialDerivative coefficients
        (pairedInteractionCenterRoot period hPeriod plusBase minusBase point) velocity =
      generalMetricTensorPairPairingAt period hPeriod (plusBase.metric, minusBase.metric)
        (pairedInteractionSmoothMetricResidualPair period hPeriod plusBase minusBase hRoot
          interactionScale coefficients) (globalMinimalPhysicalMetricTestPair period hPeriod test) point := by
  unfold generalMetricTensorPairPairingAt pairedInteractionSmoothMetricResidualPair
    globalMinimalPhysicalMetricTestPair
  rw [pairedInteractionSmoothMetricResidual_pairing period hPeriod plusBase minusBase _ _ _ .plus,
    pairedInteractionSmoothMetricResidual_pairing period hPeriod plusBase minusBase _ _ _ .minus]
  exact pairedInteractionCovectors_eq_spectral_of_sylvester period hPeriod plusBase minusBase
    hRoot interactionScale coefficients point _ _ velocity hEquation

private theorem nativeCenterRootDerivative_sylvester_valueAt
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (hZero : (0 : RelativeCore period hPeriod plusBase minusBase) ∈
      regularGeneralMetricC2PairedLorentzMatrixDomain period hPeriod plusBase minusBase)
    (test : GlobalMinimalPhysicalMetricTest period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    canonicalSylvesterOperator (pairedInteractionCenterRoot period hPeriod plusBase minusBase point)
        (c2FiniteMatrixValueAt period hPeriod 4
          (regularGeneralMetricC2PairedRelativeRootDerivative period hPeriod plusBase minusBase 0 hZero
            (pairedInteractionSmoothCore period hPeriod plusBase minusBase (test .plus) (test .minus))) point) =
      pairedInteractionMetricMatrixVelocity period hPeriod plusBase minusBase .plus point
        (fun row column => (test .plus).tensor point (plusBase.frame row point) (plusBase.frame column point)) +
      pairedInteractionMetricMatrixVelocity period hPeriod plusBase minusBase .minus point
        (fun row column => (test .minus).tensor point (plusBase.frame row point) (plusBase.frame column point)) := by
  let direction := pairedInteractionSmoothCore period hPeriod plusBase minusBase (test .plus) (test .minus)
  have hEquation := congrArg (fun matrix => c2FiniteMatrixValueAt period hPeriod 4 matrix point)
    (regularGeneralMetricC2PairedRelativeRootDerivative_zero_sylvester
      period hPeriod plusBase minusBase hZero direction)
  have hRoot := pairedInteractionRoot_zero_value period hPeriod plusBase minusBase point
  have hVelocity := pairedInteractionCenterVelocity_value_eq_sector_sum period hPeriod
    plusBase minusBase (test .plus) (test .minus) point
  rw [matrixValue_sylvester, hRoot] at hEquation
  exact hEquation.trans hVelocity

/-- A centre's native spectral density is represented by the two constructed
tensors using only its actual root-domain membership. -/
theorem pairedInteractionNativeCenter_spectralDensity_eq_pairing
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (hZero : (0 : RelativeCore period hPeriod plusBase minusBase) ∈
      regularGeneralMetricC2PairedLorentzMatrixDomain period hPeriod plusBase minusBase)
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (test : GlobalMinimalPhysicalMetricTest period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    (-interactionScale * plusBase.volume point) * matrixSpectralPotentialDerivative coefficients
        (c2FiniteMatrixValueAt period hPeriod 4
          (regularGeneralMetricC2PairedRelativeRoot period hPeriod plusBase minusBase 0) point)
        (c2FiniteMatrixValueAt period hPeriod 4
          (regularGeneralMetricC2PairedRelativeRootDerivative period hPeriod plusBase minusBase 0 hZero
            (pairedInteractionSmoothCore period hPeriod plusBase minusBase (test .plus) (test .minus))) point) =
      generalMetricTensorPairPairingAt period hPeriod (plusBase.metric, minusBase.metric)
        (pairedInteractionSmoothMetricResidualPair period hPeriod plusBase minusBase
          (pairedInteractionCenter_rootAdmissible period hPeriod plusBase minusBase hZero)
          interactionScale coefficients) (globalMinimalPhysicalMetricTestPair period hPeriod test) point := by
  let velocity := c2FiniteMatrixValueAt period hPeriod 4
    (regularGeneralMetricC2PairedRelativeRootDerivative period hPeriod plusBase minusBase 0 hZero
      (pairedInteractionSmoothCore period hPeriod plusBase minusBase (test .plus) (test .minus))) point
  exact (congrArg (fun root => (-interactionScale * plusBase.volume point) *
    matrixSpectralPotentialDerivative coefficients root velocity)
      (pairedInteractionRoot_zero_value period hPeriod plusBase minusBase point)).trans
    (centerSpectralDensity_eq_pairing_of_sylvester period hPeriod plusBase minusBase
      (pairedInteractionCenter_rootAdmissible period hPeriod plusBase minusBase hZero)
      interactionScale coefficients test point velocity
      (nativeCenterRootDerivative_sylvester_valueAt period hPeriod plusBase minusBase hZero test point))

/-- The canonical native action derivative at any admissible centre is its
concrete tensor pairing, without an independent base-compatibility premise. -/
theorem pairedInteractionNativeCenterActionDerivative_eq_metricResidualPairing
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (hZero : (0 : RelativeCore period hPeriod plusBase minusBase) ∈
      regularGeneralMetricC2PairedLorentzMatrixDomain period hPeriod plusBase minusBase)
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (test : GlobalMinimalPhysicalMetricTest period hPeriod) :
    regularGeneralMetricC2PairedInteractionC2ActionDerivative period hPeriod plusBase minusBase
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) interactionScale coefficients 0 hZero
        (pairedInteractionSmoothCore period hPeriod plusBase minusBase (test .plus) (test .minus)) =
      regularGeneralMetricC2PairedMetricResidualPairing period hPeriod (plusBase.metric, minusBase.metric)
        (pairedInteractionSmoothMetricResidualPair period hPeriod plusBase minusBase
          (pairedInteractionCenter_rootAdmissible period hPeriod plusBase minusBase hZero)
          interactionScale coefficients) test := by
  exact (regularGeneralMetricC2PairedInteractionC2ActionDerivative_apply period hPeriod
    plusBase minusBase (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
    interactionScale coefficients 0 hZero
    (pairedInteractionSmoothCore period hPeriod plusBase minusBase (test .plus) (test .minus))).trans
      (congrArg (fun integrand : EffectiveQuotient period hPeriod → Real =>
        ∫ point, integrand point ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod))
        (funext (pairedInteractionNativeCenter_spectralDensity_eq_pairing period hPeriod
          plusBase minusBase hZero interactionScale coefficients test)))

section OffCenter
variable (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
  (plusVariation minusVariation : SmoothSymmetricCovariantTwoTensor period hPeriod)
  (hAdmissible : RegularGeneralMetricC2PairedLorentzChartAdmissible period hPeriod
    plusBase minusBase plusVariation minusVariation)

local notation "newPlus" => regularGeneralMetricC2PairedPlusMetric period hPeriod
  plusBase minusBase plusVariation minusVariation hAdmissible
local notation "newMinus" => regularGeneralMetricC2PairedMinusMetric period hPeriod
  plusBase minusBase plusVariation minusVariation hAdmissible
local notation "oldPoint" => pairedInteractionSmoothCore period hPeriod
  plusBase minusBase plusVariation minusVariation
local notation "hNew" => pairedInteractionRecenter_zero_mem_lorentzMatrixDomain period hPeriod
  plusBase minusBase plusVariation minusVariation hAdmissible

/-- Two explicit smooth tensors at the reconstructed metrics. Their root
admissibility is derived from the original nested chart admissibility. -/
def pairedInteractionOffCenterResidualPair (interactionScale : Real)
    (coefficients : PotentialCoefficients) :
    SmoothSymmetricCovariantTwoTensor period hPeriod ×
      SmoothSymmetricCovariantTwoTensor period hPeriod :=
  pairedInteractionSmoothMetricResidualPair period hPeriod newPlus newMinus
    (pairedInteractionCenter_rootAdmissible period hPeriod newPlus newMinus hNew)
    interactionScale coefficients

/-- Actual off-centre native interaction derivative equals the canonical
integral of the recentered smooth residual pair on every metric test. -/
theorem pairedInteractionNativeActionDerivative_offCenter_eq_metricResidualPairing
    (configuration : GlobalFieldConfiguration period hPeriod)
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (test : GlobalMinimalPhysicalMetricTest period hPeriod) :
    regularGeneralMetricC2PairedInteractionC2ActionDerivative period hPeriod plusBase minusBase
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) interactionScale coefficients oldPoint
        (pairedInteractionSmoothCore_mem_lorentzMatrixDomain period hPeriod configuration
          plusBase minusBase plusVariation minusVariation hAdmissible)
        (pairedInteractionSmoothCore period hPeriod plusBase minusBase (test .plus) (test .minus)) =
      regularGeneralMetricC2PairedMetricResidualPairing period hPeriod ((newPlus).metric, (newMinus).metric)
        (pairedInteractionOffCenterResidualPair period hPeriod plusBase minusBase
          plusVariation minusVariation hAdmissible interactionScale coefficients) test := by
  exact (pairedInteractionC2ActionDerivative_recenter period hPeriod configuration
    plusBase minusBase plusVariation minusVariation hAdmissible
    (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) interactionScale coefficients
    (test .plus) (test .minus)).trans
      (pairedInteractionNativeCenterActionDerivative_eq_metricResidualPairing period hPeriod
        newPlus newMinus hNew interactionScale coefficients test)

include hAdmissible in
/-- The physical point used below is the genuine pure metric shift. -/
theorem pairedInteractionPureMetricShift_mem_admissible
    (configuration : GlobalFieldConfiguration period hPeriod) :
    regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection period hPeriod configuration
        (fun sector => match sector with | .plus => plusVariation | .minus => minusVariation) ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration plusBase minusBase :=
  hAdmissible

private theorem dependentValue_eq {α β : Type*} {P : α → Prop}
    (f : ∀ x, P x → β) {x y : α} (hx : P x) (hy : P y) (h : x = y) :
    f x hx = f y hy := by
  cases h
  rfl

section Strong
variable {couplings : GlobalCandidateAActionCouplings}
  {NonNullFace NullFace : Type*} [Fintype NonNullFace] [Fintype NullFace]
  (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
  (data : GlobalCandidateAActionData period hPeriod configuration.physical
    couplings NonNullFace NullFace)
  (analysis : GlobalAnalysisData period hPeriod configuration.physical)
  (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
    period hPeriod couplings.matterMassSquared)

/-- The metric projection of any admissible physical point gives the same
concrete interaction residual; other physical components may vary freely. -/
theorem pairedStrongInteractionActionDerivative_atPoint_eq_metricResidualPairing
    (physicalPoint : GlobalMinimalPhysicalFieldTangent period hPeriod configuration.physical)
    (hPoint : physicalPoint ∈ regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain
      period hPeriod configuration.physical plusBase minusBase)
    (test : GlobalMinimalPhysicalMetricTest period hPeriod) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup period hPeriod
      configuration data analysis realization plusBase minusBase (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period hPeriod
      configuration data analysis realization plusBase minusBase (canonicalDivergenceFreeLLFrame period hPeriod)
    let metricShift := physicalPoint.1.completeVariation.fullMetricPerturbation
    let hShift : RegularGeneralMetricC2PairedLorentzChartAdmissible period hPeriod
      plusBase minusBase (metricShift .plus) (metricShift .minus) := hPoint
    let variedPlus := regularGeneralMetricC2PairedPlusMetric period hPeriod plusBase minusBase
      (metricShift .plus) (metricShift .minus) hShift
    let variedMinus := regularGeneralMetricC2PairedMinusMetric period hPeriod plusBase minusBase
      (metricShift .plus) (metricShift .minus) hShift
    regularGeneralMetricC2PairedMinimalPhysicalStrongInteractionActionDerivative period hPeriod
        configuration data analysis realization plusBase minusBase
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) physicalPoint hPoint
        (regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection period hPeriod configuration.physical test) =
      regularGeneralMetricC2PairedMetricResidualPairing period hPeriod (variedPlus.metric, variedMinus.metric)
        (pairedInteractionOffCenterResidualPair period hPeriod plusBase minusBase
          (metricShift .plus) (metricShift .minus) hShift
          couplings.interactionScale couplings.interactionCoefficients) test := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup period hPeriod
    configuration data analysis realization plusBase minusBase (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period hPeriod
    configuration data analysis realization plusBase minusBase (canonicalDivergenceFreeLLFrame period hPeriod)
  let projection := globalMinimalPhysicalPairedMetricGaugeLLStrongMetricCLM period hPeriod
    configuration data analysis realization plusBase minusBase
  let metricShift := physicalPoint.1.completeVariation.fullMetricPerturbation
  have hShift : RegularGeneralMetricC2PairedLorentzChartAdmissible period hPeriod
      plusBase minusBase (metricShift .plus) (metricShift .minus) := hPoint
  let nativePoint := pairedInteractionSmoothCore period hPeriod plusBase minusBase
    (metricShift .plus) (metricShift .minus)
  let direction := regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection
    period hPeriod configuration.physical test
  have hCore : projection physicalPoint ∈ regularGeneralMetricC2PairedLorentzMatrixDomain
      period hPeriod plusBase minusBase :=
    (globalMetricPerturbationPairLorentzChartAdmissible_iff_mem_matrixDomain period hPeriod
      configuration.physical plusBase minusBase physicalPoint).mp hPoint
  have hOld := pairedInteractionSmoothCore_mem_lorentzMatrixDomain period hPeriod configuration.physical
    plusBase minusBase (metricShift .plus) (metricShift .minus) hShift
  have hProjectionPoint : projection physicalPoint = nativePoint := rfl
  have hProjectionDirection : projection direction =
      pairedInteractionSmoothCore period hPeriod plusBase minusBase (test .plus) (test .minus) := rfl
  have hTransport := dependentValue_eq
    (β := RelativeCore period hPeriod plusBase minusBase →L[Real] Real)
    (P := fun core => core ∈ regularGeneralMetricC2PairedLorentzMatrixDomain period hPeriod plusBase minusBase)
    (fun core hCore => regularGeneralMetricC2PairedInteractionC2ActionDerivative period hPeriod
      plusBase minusBase (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
      couplings.interactionScale couplings.interactionCoefficients core hCore)
    hCore hOld hProjectionPoint
  have hNative := (congrArg (fun derivative : RelativeCore period hPeriod plusBase minusBase →L[Real] Real =>
    derivative (projection direction)) hTransport).trans
      (congrArg (regularGeneralMetricC2PairedInteractionC2ActionDerivative period hPeriod
        plusBase minusBase (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
        couplings.interactionScale couplings.interactionCoefficients nativePoint hOld) hProjectionDirection)
  exact (ContinuousLinearMap.comp_apply
    (regularGeneralMetricC2PairedInteractionC2ActionDerivative period hPeriod
      plusBase minusBase (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
      couplings.interactionScale couplings.interactionCoefficients (projection physicalPoint) hCore)
    projection direction).trans
      (hNative.trans (pairedInteractionNativeActionDerivative_offCenter_eq_metricResidualPairing
        period hPeriod plusBase minusBase (metricShift .plus) (metricShift .minus) hShift configuration.physical
        couplings.interactionScale couplings.interactionCoefficients test))

/-- The pure metric shift is a specialization of the arbitrary-point result. -/
theorem pairedStrongInteractionActionDerivative_offCenter_eq_metricResidualPairing
    (test : GlobalMinimalPhysicalMetricTest period hPeriod) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup period hPeriod
      configuration data analysis realization plusBase minusBase (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period hPeriod
      configuration data analysis realization plusBase minusBase (canonicalDivergenceFreeLLFrame period hPeriod)
    let shift := regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection period hPeriod
      configuration.physical (fun sector => match sector with | .plus => plusVariation | .minus => minusVariation)
    let hShift := pairedInteractionPureMetricShift_mem_admissible period hPeriod plusBase minusBase
      plusVariation minusVariation hAdmissible configuration.physical
    regularGeneralMetricC2PairedMinimalPhysicalStrongInteractionActionDerivative period hPeriod
        configuration data analysis realization plusBase minusBase
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) shift hShift
        (regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection period hPeriod configuration.physical test) =
      regularGeneralMetricC2PairedMetricResidualPairing period hPeriod ((newPlus).metric, (newMinus).metric)
        (pairedInteractionOffCenterResidualPair period hPeriod plusBase minusBase
          plusVariation minusVariation hAdmissible couplings.interactionScale couplings.interactionCoefficients) test := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup period hPeriod
    configuration data analysis realization plusBase minusBase (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period hPeriod
    configuration data analysis realization plusBase minusBase (canonicalDivergenceFreeLLFrame period hPeriod)
  exact pairedStrongInteractionActionDerivative_atPoint_eq_metricResidualPairing period hPeriod
    plusBase minusBase configuration data analysis realization
    (regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection period hPeriod configuration.physical
      (fun sector => match sector with | .plus => plusVariation | .minus => minusVariation))
    (pairedInteractionPureMetricShift_mem_admissible period hPeriod plusBase minusBase
      plusVariation minusVariation hAdmissible configuration.physical) test

end Strong
end OffCenter
end
end P0EFTJanusPairedInteractionOffCenterResidual4D
end JanusFormal
