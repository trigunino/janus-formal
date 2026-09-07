import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPairedInteractionSmoothMetricResidual4D

/-! # The actual strong interaction derivative is its smooth metric residual pairing

The root and both matrix velocities are identified with the completed C²
chart at zero. The proved Sylvester equation then identifies its derivative
with the smooth inverse-Sylvester covector, which is integrated against the
canonical measure. The fixed plus-volume factor is retained throughout.
-/
namespace JanusFormal
namespace P0EFTJanusPairedStrongInteractionResidualPairing4D
set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 600000
noncomputable section
open Set MeasureTheory
open scoped Manifold ContDiff BigOperators
open P0EFTJanusConvexHelmholtzReconstruction
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVFirstLevel4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVIntegratedMaster4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixInverse4D
open P0EFTJanusPositiveRawSplitCharpolyContDiffLocalRootBranch4D
open P0EFTJanusMatrixInteractionFrechetNoether
open P0EFTJanusReciprocalBimetricPotential
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphProjections4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalComponentPDEBlockPairing4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPRegularFrameMetricInverse4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootLift4D
open P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootSmoothLift4D
open P0EFTJanusProgramPRegularGeneralMetricC2MaxwellDensityPointwise4D
open P0EFTJanusProgramPRegularGeneralMetricC2MaxwellStressDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartCenter4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedRelativeMatrixCore4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalRelativeMetricCoreProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomainOpen4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalInteractionC24D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC0FirstJetProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLocalEuler4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalNineBlockC24D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongMetricTotalEulerReduction4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongInteractionDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedRelativeRootSpectralDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedInteractionActionDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMetricResidualTestSeparation4D
open P0EFTJanusPairedInteractionMetricCenterSylvester4D
open P0EFTJanusPairedInteractionSmoothMetricResidual4D

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
local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _
local instance : BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl
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

private def matrixValueLinearMap (point : EffectiveQuotient period hPeriod) :
    C2Matrix period hPeriod →ₗ[Real] Matrix4 where
  toFun := fun matrix => c2FiniteMatrixValueAt period hPeriod 4 matrix point
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem matrixValue_neg (matrix : C2Matrix period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    c2FiniteMatrixValueAt period hPeriod 4 (-matrix) point =
      -c2FiniteMatrixValueAt period hPeriod 4 matrix point :=
  (matrixValueLinearMap period hPeriod point).map_neg matrix

private theorem matrixValue_smul (scalar : Real) (matrix : C2Matrix period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    c2FiniteMatrixValueAt period hPeriod 4 (scalar • matrix) point =
      scalar • c2FiniteMatrixValueAt period hPeriod 4 matrix point :=
  (matrixValueLinearMap period hPeriod point).map_smul scalar matrix

private theorem matrixValue_sub (first second : C2Matrix period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    c2FiniteMatrixValueAt period hPeriod 4 (first - second) point =
      c2FiniteMatrixValueAt period hPeriod 4 first point -
        c2FiniteMatrixValueAt period hPeriod 4 second point :=
  (matrixValueLinearMap period hPeriod point).map_sub first second

/-- The completed direction evaluated at a point is the genuine raised covariant test. -/
theorem interactionVariationMatrix_valueAt_eq_inverse_mul
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    c2FiniteMatrixValueAt period hPeriod 4
        (regularGeneralMetricC2VariationMatrix period hPeriod metric tensor) point =
      regularFrameMetricInverseMatrixMap period hPeriod metric point *
        regularFrameCovariantVariationMatrixAt period hPeriod metric tensor point := by
  exact regularGeneralMetricC2RelativeMatrixAt_smooth period hPeriod metric tensor point

variable (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)

theorem pairedInteractionCenterRelativeMatrix_eq_value (point : EffectiveQuotient period hPeriod) :
    pairedInteractionCenterRelativeMatrix period hPeriod plusBase minusBase point =
      c2FiniteMatrixValueAt period hPeriod 4
        (regularGeneralMetricC2VariationMatrix period hPeriod plusBase
          (minusBase.metric.tensor - plusBase.metric.tensor)) point := by
  ext row column
  change (if row = column then (1 : Real) else 0) +
      c2FiniteMatrixValueAt period hPeriod 4
        (regularGeneralMetricC2VariationMatrix period hPeriod plusBase
          (minusBase.metric.tensor - plusBase.metric.tensor)) point row column -
        (if row = column then 1 else 0) = _
  ring

theorem pairedInteractionRoot_zero_value (point : EffectiveQuotient period hPeriod) :
    c2FiniteMatrixValueAt period hPeriod 4
        (regularGeneralMetricC2PairedRelativeRoot period hPeriod plusBase minusBase 0) point =
      pairedInteractionCenterRoot period hPeriod plusBase minusBase point := by
  unfold regularGeneralMetricC2PairedRelativeRoot regularGeneralMetricC2PairedRelativeMatrix
  simp only [Prod.fst_zero, Prod.snd_zero,
    regularGeneralMetricC2IdentityRootInverseC2Matrix_zero, add_zero,
    c2FiniteMatrixProduct_identity_left, c2FiniteMatrixProduct_identity_right]
  rfl

/-- The completed two-test velocity is exactly the sum of the two concrete
matrix velocities represented by the smooth residuals. -/
theorem pairedInteractionCenterVelocity_value_eq_sector_sum
    (plusTest minusTest : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    c2FiniteMatrixValueAt period hPeriod 4
        (pairedInteractionMetricCenterVelocity period hPeriod plusBase minusBase
          (regularGeneralMetricC2VariationMatrix period hPeriod plusBase plusTest)
          (regularGeneralMetricC2VariationMatrix period hPeriod plusBase minusTest -
            regularGeneralMetricC2VariationMatrix period hPeriod plusBase plusTest)) point =
      pairedInteractionMetricMatrixVelocity period hPeriod plusBase minusBase .plus point
          (regularFrameCovariantVariationMatrixAt period hPeriod plusBase plusTest point) +
        pairedInteractionMetricMatrixVelocity period hPeriod plusBase minusBase .minus point
          (regularFrameCovariantVariationMatrixAt period hPeriod plusBase minusTest point) := by
  have hRelative := (pairedInteractionCenterRelativeMatrix_eq_value period hPeriod
    plusBase minusBase point).symm
  simp only [pairedInteractionMetricCenterVelocity, c2FiniteMatrixValueAt_add,
    c2FiniteMatrixValueAt_product, matrixValue_neg, matrixValue_smul, matrixValue_sub]
  rw [hRelative]
  simp only [interactionVariationMatrix_valueAt_eq_inverse_mul,
    pairedInteractionMetricMatrixVelocity, neg_apply, smul_apply, add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.mul_apply', Matrix.mul_neg, Matrix.neg_mul,
    Matrix.mul_smul, Matrix.smul_mul, smul_add, sub_eq_add_neg, neg_add_rev]
  abel

theorem pairedInteractionCovectors_eq_spectral_of_sylvester
    (hRoot : RegularGeneralMetricC2IdentityRootAdmissible period hPeriod plusBase
      (minusBase.metric.tensor - plusBase.metric.tensor))
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (point : EffectiveQuotient period hPeriod) (plusMatrix minusMatrix rootVelocity : Matrix4)
    (hEquation : canonicalSylvesterOperator
        (pairedInteractionCenterRoot period hPeriod plusBase minusBase point) rootVelocity =
      pairedInteractionMetricMatrixVelocity period hPeriod plusBase minusBase .plus point plusMatrix +
        pairedInteractionMetricMatrixVelocity period hPeriod plusBase minusBase .minus point minusMatrix) :
    (-interactionScale * plusBase.volume point) * matrixSpectralPotentialDerivative coefficients
        (pairedInteractionCenterRoot period hPeriod plusBase minusBase point) rootVelocity =
      pairedInteractionMetricCovector period hPeriod plusBase minusBase interactionScale
          coefficients .plus point plusMatrix +
        pairedInteractionMetricCovector period hPeriod plusBase minusBase interactionScale
          coefficients .minus point minusMatrix := by
  have hInverse := pairedInteractionCenterSylvesterInverse_solve period hPeriod plusBase minusBase
    hRoot point _ rootVelocity hEquation
  rw [← hInverse, map_add, map_add, mul_add]
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

private theorem dependentValue_eq {α β : Type*} {P : α → Prop}
    (f : ∀ x, P x → β) {x y : α} (hx : P x) (hy : P y) (h : x = y) :
    f x hx = f y hy := by
  cases h
  rfl

theorem pairedStrongInteraction_spectralDensity_eq_residualPairing
    (hZero : (0 : RegularGeneralMetricC2PairedRelativeCore period hPeriod plusBase minusBase) ∈
      regularGeneralMetricC2PairedLorentzMatrixDomain period hPeriod plusBase minusBase)
    (test : GlobalMinimalPhysicalMetricTest period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup period hPeriod
      configuration data analysis realization plusBase minusBase (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period hPeriod
      configuration data analysis realization plusBase minusBase (canonicalDivergenceFreeLLFrame period hPeriod)
    let projection := globalMinimalPhysicalPairedMetricGaugeLLStrongMetricCLM period hPeriod
      configuration data analysis realization plusBase minusBase
    let direction := regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection
      period hPeriod configuration.physical test
    let hRoot := pairedInteractionCenter_rootAdmissible period hPeriod plusBase minusBase hZero
    (-couplings.interactionScale * plusBase.volume point) *
        matrixSpectralPotentialDerivative couplings.interactionCoefficients
          (c2FiniteMatrixValueAt period hPeriod 4
            (regularGeneralMetricC2PairedRelativeRoot period hPeriod plusBase minusBase 0) point)
          (c2FiniteMatrixValueAt period hPeriod 4
            (regularGeneralMetricC2PairedRelativeRootDerivative period hPeriod plusBase minusBase
              0 hZero (projection direction)) point) =
      generalMetricTensorPairPairingAt period hPeriod (plusBase.metric, minusBase.metric)
        (pairedInteractionSmoothMetricResidualPair period hPeriod plusBase minusBase hRoot
          couplings.interactionScale couplings.interactionCoefficients)
        (globalMinimalPhysicalMetricTestPair period hPeriod test) point := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup period hPeriod
    configuration data analysis realization plusBase minusBase (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period hPeriod
    configuration data analysis realization plusBase minusBase (canonicalDivergenceFreeLLFrame period hPeriod)
  dsimp only
  unfold generalMetricTensorPairPairingAt pairedInteractionSmoothMetricResidualPair
    globalMinimalPhysicalMetricTestPair
  dsimp only
  rw [pairedInteractionSmoothMetricResidual_pairing period hPeriod plusBase minusBase _ _ _ .plus,
    pairedInteractionSmoothMetricResidual_pairing period hPeriod plusBase minusBase _ _ _ .minus,
    pairedInteractionRoot_zero_value]
  apply pairedInteractionCovectors_eq_spectral_of_sylvester
    period hPeriod plusBase minusBase
      (pairedInteractionCenter_rootAdmissible period hPeriod plusBase minusBase hZero)
  have hEquation := pairedStrongInteraction_rootDerivative_zero_sylvester_pointwise period hPeriod
    configuration data analysis realization plusBase minusBase hZero test point
  dsimp only at hEquation
  rw [pairedInteractionRoot_zero_value, pairedInteractionCenterVelocity_value_eq_sector_sum] at hEquation
  exact hEquation

attribute [local irreducible]
  regularGeneralMetricC2PairedInteractionC2ActionDerivative
  regularGeneralMetricC2PairedRelativeRootDerivative
  regularGeneralMetricC2PairedLorentzMatrixDomain

/-- Centre transport is checked before the integrated spectral formula. -/
theorem pairedStrongInteractionActionDerivative_zero_eq_native
    (hBase : RegularGeneralMetricC2PairedLorentzChartBaseCompatible
      period hPeriod plusBase minusBase)
    (direction : GlobalMinimalPhysicalFieldTangent period hPeriod configuration.physical) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup period hPeriod
      configuration data analysis realization plusBase minusBase (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period hPeriod
      configuration data analysis realization plusBase minusBase (canonicalDivergenceFreeLLFrame period hPeriod)
    let measure := intrinsicCanonicalLorentzVolumeMeasure period hPeriod
    let hPoint := zero_mem_regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
      configuration.physical plusBase minusBase hBase
    let hZero := pairedStrongInteraction_zero_mem_lorentzMatrixDomain period hPeriod
      configuration plusBase minusBase hBase
    regularGeneralMetricC2PairedMinimalPhysicalStrongInteractionActionDerivative period hPeriod
        configuration data analysis realization plusBase minusBase
        measure 0 hPoint direction =
      regularGeneralMetricC2PairedInteractionC2ActionDerivative period hPeriod
        plusBase minusBase measure couplings.interactionScale couplings.interactionCoefficients
        0 hZero (globalMinimalPhysicalPairedMetricGaugeLLStrongMetricCLM period hPeriod
          configuration data analysis realization plusBase minusBase direction) := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup period hPeriod
    configuration data analysis realization plusBase minusBase (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period hPeriod
    configuration data analysis realization plusBase minusBase (canonicalDivergenceFreeLLFrame period hPeriod)
  let projection := globalMinimalPhysicalPairedMetricGaugeLLStrongMetricCLM period hPeriod
    configuration data analysis realization plusBase minusBase
  have hZero := pairedStrongInteraction_zero_mem_lorentzMatrixDomain period hPeriod
    configuration plusBase minusBase hBase
  have hCore : projection 0 ∈
      regularGeneralMetricC2PairedLorentzMatrixDomain period hPeriod plusBase minusBase :=
    (globalMetricPerturbationPairLorentzChartAdmissible_iff_mem_matrixDomain
      period hPeriod configuration.physical plusBase minusBase 0).1
      (zero_mem_regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase hBase)
  have hTransport := dependentValue_eq
    (β := RegularGeneralMetricC2PairedRelativeCore period hPeriod plusBase minusBase →L[Real] Real)
    (P := fun core => core ∈ regularGeneralMetricC2PairedLorentzMatrixDomain
      period hPeriod plusBase minusBase)
    (fun core hCore => regularGeneralMetricC2PairedInteractionC2ActionDerivative
      period hPeriod plusBase minusBase (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
      couplings.interactionScale couplings.interactionCoefficients core hCore)
    hCore hZero projection.map_zero
  exact (ContinuousLinearMap.comp_apply
    (regularGeneralMetricC2PairedInteractionC2ActionDerivative period hPeriod
      plusBase minusBase (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
      couplings.interactionScale couplings.interactionCoefficients (projection 0) hCore)
    projection direction).trans
      (congrArg (fun derivative :
        RegularGeneralMetricC2PairedRelativeCore period hPeriod plusBase minusBase →L[Real] Real =>
          derivative (projection direction)) hTransport)

/-- Integrate a pointwise representation with the C² direction left abstract. -/
private theorem nativeDerivative_eq_pairing_of_pointwise
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (hZero : (0 : RegularGeneralMetricC2PairedRelativeCore period hPeriod plusBase minusBase) ∈
      regularGeneralMetricC2PairedLorentzMatrixDomain period hPeriod plusBase minusBase)
    (direction : RegularGeneralMetricC2PairedRelativeCore period hPeriod plusBase minusBase)
    (residual : SmoothSymmetricCovariantTwoTensor period hPeriod ×
      SmoothSymmetricCovariantTwoTensor period hPeriod)
    (test : GlobalMinimalPhysicalMetricTest period hPeriod)
    (hDensity : ∀ point,
      (-interactionScale * plusBase.volume point) *
        matrixSpectralPotentialDerivative coefficients
          (c2FiniteMatrixValueAt period hPeriod 4
            (regularGeneralMetricC2PairedRelativeRoot period hPeriod plusBase minusBase 0) point)
          (c2FiniteMatrixValueAt period hPeriod 4
            (regularGeneralMetricC2PairedRelativeRootDerivative period hPeriod plusBase minusBase
              0 hZero direction) point) =
      generalMetricTensorPairPairingAt period hPeriod (plusBase.metric, minusBase.metric)
        residual (globalMinimalPhysicalMetricTestPair period hPeriod test) point) :
    regularGeneralMetricC2PairedInteractionC2ActionDerivative period hPeriod plusBase minusBase
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) interactionScale coefficients
        0 hZero direction =
      regularGeneralMetricC2PairedMetricResidualPairing period hPeriod
        (plusBase.metric, minusBase.metric) residual test := by
  exact (regularGeneralMetricC2PairedInteractionC2ActionDerivative_apply period hPeriod
    plusBase minusBase (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
    interactionScale coefficients 0 hZero direction).trans
      (congrArg (fun integrand : EffectiveQuotient period hPeriod → Real =>
        ∫ point, integrand point ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod))
        (funext hDensity))

/-- The native derivative at zero is the integral of its smooth tensor pairing. -/
theorem pairedInteractionNativeActionDerivative_zero_eq_metricResidualPairing
    (hBase : RegularGeneralMetricC2PairedLorentzChartBaseCompatible
      period hPeriod plusBase minusBase)
    (test : GlobalMinimalPhysicalMetricTest period hPeriod) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup period hPeriod
      configuration data analysis realization plusBase minusBase (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period hPeriod
      configuration data analysis realization plusBase minusBase (canonicalDivergenceFreeLLFrame period hPeriod)
    let measure := intrinsicCanonicalLorentzVolumeMeasure period hPeriod
    let direction := regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection
      period hPeriod configuration.physical test
    let hZero := pairedStrongInteraction_zero_mem_lorentzMatrixDomain period hPeriod
      configuration plusBase minusBase hBase
    let hRoot := pairedInteractionCenter_rootAdmissible period hPeriod plusBase minusBase hZero
    regularGeneralMetricC2PairedInteractionC2ActionDerivative period hPeriod
        plusBase minusBase measure couplings.interactionScale couplings.interactionCoefficients
        0 hZero (globalMinimalPhysicalPairedMetricGaugeLLStrongMetricCLM period hPeriod
          configuration data analysis realization plusBase minusBase direction) =
      regularGeneralMetricC2PairedMetricResidualPairing period hPeriod
        (plusBase.metric, minusBase.metric)
        (pairedInteractionSmoothMetricResidualPair period hPeriod plusBase minusBase hRoot
          couplings.interactionScale couplings.interactionCoefficients) test := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup period hPeriod
    configuration data analysis realization plusBase minusBase (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period hPeriod
    configuration data analysis realization plusBase minusBase (canonicalDivergenceFreeLLFrame period hPeriod)
  let projection := globalMinimalPhysicalPairedMetricGaugeLLStrongMetricCLM period hPeriod
    configuration data analysis realization plusBase minusBase
  let direction := regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection
    period hPeriod configuration.physical test
  have hZero := pairedStrongInteraction_zero_mem_lorentzMatrixDomain period hPeriod
    configuration plusBase minusBase hBase
  exact nativeDerivative_eq_pairing_of_pointwise period hPeriod plusBase minusBase
    couplings.interactionScale couplings.interactionCoefficients hZero (projection direction)
    (pairedInteractionSmoothMetricResidualPair period hPeriod plusBase minusBase
      (pairedInteractionCenter_rootAdmissible period hPeriod plusBase minusBase hZero)
      couplings.interactionScale couplings.interactionCoefficients) test
    (pairedStrongInteraction_spectralDensity_eq_residualPairing period hPeriod
      plusBase minusBase configuration data analysis realization hZero test)

/-- The interaction block of the actual strong Euler operator is the
canonical integrated pairing with the two constructed smooth tensors. -/
theorem pairedStrongInteractionActionDerivative_zero_eq_metricResidualPairing
    (hBase : RegularGeneralMetricC2PairedLorentzChartBaseCompatible
      period hPeriod plusBase minusBase)
    (test : GlobalMinimalPhysicalMetricTest period hPeriod) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup period hPeriod
      configuration data analysis realization plusBase minusBase (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period hPeriod
      configuration data analysis realization plusBase minusBase (canonicalDivergenceFreeLLFrame period hPeriod)
    let measure := intrinsicCanonicalLorentzVolumeMeasure period hPeriod
    let direction := regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection
      period hPeriod configuration.physical test
    let hPoint := zero_mem_regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
      configuration.physical plusBase minusBase hBase
    let hZero := pairedStrongInteraction_zero_mem_lorentzMatrixDomain period hPeriod
      configuration plusBase minusBase hBase
    let hRoot := pairedInteractionCenter_rootAdmissible period hPeriod plusBase minusBase hZero
    regularGeneralMetricC2PairedMinimalPhysicalStrongInteractionActionDerivative period hPeriod
        configuration data analysis realization plusBase minusBase
        measure 0 hPoint direction =
      regularGeneralMetricC2PairedMetricResidualPairing period hPeriod
        (plusBase.metric, minusBase.metric)
        (pairedInteractionSmoothMetricResidualPair period hPeriod plusBase minusBase hRoot
          couplings.interactionScale couplings.interactionCoefficients) test := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup period hPeriod
    configuration data analysis realization plusBase minusBase (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period hPeriod
    configuration data analysis realization plusBase minusBase (canonicalDivergenceFreeLLFrame period hPeriod)
  exact (pairedStrongInteractionActionDerivative_zero_eq_native period hPeriod
    plusBase minusBase configuration data analysis realization hBase
      (regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection
        period hPeriod configuration.physical test)).trans
      (pairedInteractionNativeActionDerivative_zero_eq_metricResidualPairing period hPeriod
        plusBase minusBase configuration data analysis realization hBase test)

end Strong
end
end P0EFTJanusPairedStrongInteractionResidualPairing4D
end JanusFormal
