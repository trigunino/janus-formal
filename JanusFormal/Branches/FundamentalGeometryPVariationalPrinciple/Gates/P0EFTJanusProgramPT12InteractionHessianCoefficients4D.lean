import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12InteractionHessianLocality4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12InteractionGradientLocality4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12StrongInteractionHessianPullback4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12C2RootPointwiseLocality4D
namespace JanusFormal
namespace P0EFTJanusProgramPT12InteractionHessianCoefficients4D

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 600000

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology
open P0EFTJanusConvexHelmholtzReconstruction
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalEulerLagrange4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphProjections4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalComponentPDEBlockPairing4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartCenter4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalMetricGaugeCoreProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomainOpen4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalConstantBoundaryC24D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC0FirstJetProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalNineBlockC24D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLocalEuler4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedGaugeCoefficientMaxwellAction4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

attribute [local instance 1900]
  P0EFTJanusProgramPRegularGeneralMetricC2PairedInteractionActionDerivative4D.relativeCoreNormedAddCommGroup
  P0EFTJanusProgramPRegularGeneralMetricC2PairedInteractionActionDerivative4D.relativeCoreNormedSpace

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev C2Scalar :=
  CanonicalPhysicalScalarC2JetCore period hPeriod

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

@[reducible] local instance c2ScalarNormedAddCommGroup :
    NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup

@[reducible] local instance c2ScalarNormedSpace :
    NormedSpace Real (C2Scalar period hPeriod) := inferInstance

open P0EFTJanusProgramPT12ProjectedGradientDerivative4D
open P0EFTJanusProgramPT12PairedMaxwellCenterC24D
open P0EFTJanusProgramPT12PairedMaxwellHessianPullback4D
open P0EFTJanusProgramPT12MaxwellNativeMixedHessian4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongMaxwellDerivative4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusProgramPRegularFrameGaugePotentialReconstruction4D

local instance : IsFiniteMeasure (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

variable {couplings : GlobalCandidateAActionCouplings}
  {NonNullFace NullFace : Type*} [Fintype NonNullFace] [Fintype NullFace]
  (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
  (data : GlobalCandidateAActionData period hPeriod configuration.physical couplings NonNullFace NullFace)
  (analysis : GlobalAnalysisData period hPeriod configuration.physical)
  (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D period hPeriod couplings.matterMassSquared)
  (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)

open P0EFTJanusProgramPGlobalCandidateADiagonalCovariantHessianResidualBridge4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedHilbertKernelSaturation4D
open P0EFTJanusProgramPGlobalGaugeTangentIntrinsicEmbedding4D
open P0EFTJanusProgramPRegularGeneralMetricC2MaxwellStressDerivative4D
open P0EFTJanusProgramPT12JointQuotientDiffeomorphismSmoothPairing4D
open P0EFTJanusProgramPT12JointQuotientAbelianSmoothPairing4D
open P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalPairedAbelianBRSTGaugeFermion4D
open P0EFTJanusProgramPCandidateADiagonalDiffeomorphismKineticAdjointBridge4D
open P0EFTJanusProgramPT12MaxwellPhysicalCoreProjection4D
open P0EFTJanusProgramPT12StrongMaxwellActionHessian4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D

open P0EFTJanusProgramPT12PhysicalGaugeHessianReduction4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongGaugeReducedCoupledResidual4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongMaxwellWeakFirstVariation4D
open P0EFTJanusProgramPGlobalCandidateALocalPhysicalHessianSplit4D
open P0EFTJanusProgramPFullCoupledHelmholtzAssembly4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateAAbelianExtendedBulkGraphC2Chart4D

open P0EFTJanusProgramPT12StrongPhysicalGaugeGradient4D
open P0EFTJanusProgramPT12StrongMaxwellBRSTMixedHessian4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusProgramPT12DiffeomorphismL2Core4D
open P0EFTJanusProgramPT12DiffeomorphismMetricSmooth4D

open P0EFTJanusProgramPT12PhysicalMetricHessianReduction4D
open P0EFTJanusProgramPT12StrongEinsteinBRSTHessian4D
open P0EFTJanusProgramPT12StrongMaxwellBRSTMetricHessian4D

open P0EFTJanusProgramPT12StrongPhysicalBRSTMetricHessian4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalInteractionC24D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedInteractionActionDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongInteractionDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalRelativeMetricCoreProjection4D

open P0EFTJanusProgramPT12C2RootPointwiseLocality4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2IdentityRootBranch4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2IdentityRootDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedRelativeMatrixCore4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedRelativeMatrixDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedRelativeRootSpectralDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootInverseCore4D
open P0EFTJanusProgramPRegularGeneralMetricC2InverseVelocityPointwise4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D

private abbrev RelativeCore := RegularGeneralMetricC2PairedRelativeCore period hPeriod plusBase minusBase

local instance : HSMul Real (RelativeCore period hPeriod plusBase minusBase)
    (RelativeCore period hPeriod plusBase minusBase) :=
  @instHSMul Real _
    (P0EFTJanusProgramPRegularGeneralMetricC2PairedInteractionActionDerivative4D.relativeCoreNormedSpace
      period hPeriod plusBase minusBase).toModule.toSMul

open P0EFTJanusProgramPT12InteractionHessianLocality4D
open P0EFTJanusProgramPRegularGeneralMetricC2MatrixSpectralPotentialDerivative4D
open scoped BigOperators

abbrev InteractionMatrixIndex := Bool × (Fin 4 × Fin 4)

private theorem matrixValue_zero (point : EffectiveQuotient period hPeriod) :
    c2FiniteMatrixValueAt period hPeriod 4 0 point = 0 := rfl

def interactionMatrixValues (point : EffectiveQuotient period hPeriod) :
    RelativeCore period hPeriod plusBase minusBase →ₗ[Real] (InteractionMatrixIndex → Real) where
  toFun test index := if index.1 then
    c2FiniteMatrixValueAt period hPeriod 4 test.2.1 point index.2.1 index.2.2 else
    c2FiniteMatrixValueAt period hPeriod 4 test.2.2 point index.2.1 index.2.2
  map_add' left right := by ext index; cases index with | mk sector row => cases sector <;> rfl
  map_smul' scalar test := by ext index; cases index with | mk sector row => cases sector <;> rfl

def interactionMatrixBasis (index : InteractionMatrixIndex) :
    RelativeCore period hPeriod plusBase minusBase :=
  ((0, 0), if index.1 then constantC2Matrix period hPeriod (Pi.single index.2.1 (Pi.single index.2.2 1)) else 0,
    if index.1 then 0 else constantC2Matrix period hPeriod (Pi.single index.2.1 (Pi.single index.2.2 1)))

theorem interactionMatrixBasis_values (point : EffectiveQuotient period hPeriod) (index : InteractionMatrixIndex) :
    interactionMatrixValues period hPeriod plusBase minusBase point
      (interactionMatrixBasis period hPeriod plusBase minusBase index) = Pi.single index 1 := by
  ext other
  rcases index with ⟨sector, row, column⟩
  rcases other with ⟨otherSector, otherRow, otherColumn⟩
  by_cases hr : otherRow = row <;> by_cases hc : otherColumn = column <;>
    cases sector <;> cases otherSector <;>
    simp [interactionMatrixValues, interactionMatrixBasis, constantC2Matrix_valueAt,
      matrixValue_zero, Prod.mk.injEq, hr, hc]

def interactionDensityHessianCoefficient
    (core first : RelativeCore period hPeriod plusBase minusBase) (index : InteractionMatrixIndex) :
    C2Scalar period hPeriod :=
  fderiv Real (fderiv Real (regularGeneralMetricC2PairedInteractionC2Density
    period hPeriod plusBase minusBase couplings.interactionScale couplings.interactionCoefficients)) core first
    (interactionMatrixBasis period hPeriod plusBase minusBase index)

theorem interactionDensityHessian_valueAt_eq_sum
    (core first test : RelativeCore period hPeriod plusBase minusBase)
    (point : EffectiveQuotient period hPeriod)
    (hCore : core ∈ regularGeneralMetricC2PairedLorentzMatrixDomain period hPeriod plusBase minusBase) :
    canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
      (fderiv Real (fderiv Real (regularGeneralMetricC2PairedInteractionC2Density
        period hPeriod plusBase minusBase couplings.interactionScale couplings.interactionCoefficients)) core first test) point =
    ∑ index : InteractionMatrixIndex,
      interactionMatrixValues period hPeriod plusBase minusBase point test index *
      canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
        (interactionDensityHessianCoefficient period hPeriod plusBase minusBase core first index (couplings := couplings)) point := by
  let values := interactionMatrixValues period hPeriod plusBase minusBase point
  let replacement : RelativeCore period hPeriod plusBase minusBase := ∑ index : InteractionMatrixIndex,
    ((values test index) • (interactionMatrixBasis period hPeriod plusBase minusBase index) : RelativeCore period hPeriod plusBase minusBase)
  have hValues : values (test - replacement) = 0 := by
    simp only [map_sub, replacement, map_sum, map_smul]
    change values test - ∑ index : InteractionMatrixIndex,
      values test index • interactionMatrixValues period hPeriod plusBase minusBase point
        (interactionMatrixBasis period hPeriod plusBase minusBase index) = 0
    simp only [interactionMatrixBasis_values]
    ext index
    simp [Finset.sum_apply, Pi.single_apply]
  have hPlus : c2FiniteMatrixValueAt period hPeriod 4 (test - replacement).2.1 point = 0 := by
    ext row column
    exact congrFun hValues (true, row, column)
  have hCross : c2FiniteMatrixValueAt period hPeriod 4 (test - replacement).2.2 point = 0 := by
    ext row column
    exact congrFun hValues (false, row, column)
  have hZero := interactionDensityHessian_valueAt_zero period hPeriod plusBase minusBase
    core first (test - replacement) point hCore hPlus hCross (couplings := couplings)
  simp only [map_sub] at hZero
  have hEq := sub_eq_zero.mp hZero
  rw [hEq]
  simp only [replacement, map_sum, map_smul, ContinuousMap.sum_apply, ContinuousMap.smul_apply,
    smul_eq_mul, interactionDensityHessianCoefficient, values]

end
end P0EFTJanusProgramPT12InteractionHessianCoefficients4D
end JanusFormal
