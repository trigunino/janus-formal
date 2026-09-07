import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGaugeCoefficientRecenterRootTransport4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPairedInteractionMetricCenterSylvester4D

/-! # Explicit completed gauge transition and its actual metric-line derivative -/

namespace JanusFormal
namespace P0EFTJanusGaugeCoefficientRecenterDerivative4D

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 600000
noncomputable section
open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVFirstLevel4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2IdentityRootBranch4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2IdentityRootDerivative4D
open P0EFTJanusProgramPGlobalGaugeTangentIntrinsicEmbedding4D
open P0EFTJanusProgramPRegularFrameGaugePotentialReconstruction4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootLift4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartRegularMetric4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalMetricGaugeCoreProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2GaugeCoefficientFrameTransport4D
open P0EFTJanusRegularFrameGaugeCoefficientTransition4D
open P0EFTJanusPairedStrongMaxwellMetricTransportDerivative4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
private abbrev C2Scalar := CanonicalPhysicalScalarC2JetCore period hPeriod
private abbrev C2Matrix := C2FiniteMatrix period hPeriod 4
private abbrev GaugeC2Core := RegularGeneralMetricC2GaugeCoefficientCore period hPeriod
local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod
local instance : NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (C2Scalar period hPeriod) := inferInstance
local instance : CompleteSpace (C2Scalar period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod

open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2LocalRoot4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixInverse4D
open P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootInverseCore4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedRelativeMatrixDerivative4D
open P0EFTJanusProgramPRegularFrameGaugeCurvatureC0FromC2Coefficients4D
open P0EFTJanusStrongMaxwellMetricCenterFirstVariation4D
open P0EFTJanusPairedInteractionMetricCenterSylvester4D
open P0EFTJanusGaugeCoefficientRecenterRootTransport4D

/-- Transpose transport reverses the order of successive matrix actions. -/
theorem gaugeCoefficientC2CoreFrameTransport_comp
    (first second : C2Matrix period hPeriod) (coefficients : GaugeC2Core period hPeriod) :
    gaugeCoefficientC2CoreFrameTransport period hPeriod second
        (gaugeCoefficientC2CoreFrameTransport period hPeriod first coefficients) =
      gaugeCoefficientC2CoreFrameTransport period hPeriod
        (c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) 4 first second) coefficients := by
  funext baseIndex component
  simp only [gaugeCoefficientC2CoreFrameTransport, c2FiniteMatrixProduct_apply]
  simp_rw [c2ScalarProduct_sum_left, c2ScalarProduct_sum_right]
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro firstIndex _
  apply Finset.sum_congr rfl
  intro secondIndex _
  rw [← c2ScalarProduct_assoc,
    c2ScalarProduct_comm period hPeriod (second secondIndex baseIndex) (first firstIndex secondIndex)]

/-- Inverse-root transport cancels the selected root on arbitrary completed packets. -/
theorem gaugeCoefficientC2CoreFrameTransport_inverse_root
    (variation : C2Matrix period hPeriod)
    (hVariation : variation ∈ c2IdentityRootInvertiblePerturbationDomain period hPeriod)
    (coefficients : GaugeC2Core period hPeriod) :
    gaugeCoefficientC2CoreFrameTransport period hPeriod
        (regularGeneralMetricC2IdentityRootInverseC2Matrix period hPeriod variation)
        (gaugeCoefficientC2CoreFrameTransport period hPeriod
          (c2IdentityRootBranch period hPeriod variation) coefficients) = coefficients := by
  rw [gaugeCoefficientC2CoreFrameTransport_comp,
    regularGeneralMetricC2IdentityRoot_mul_inverseC2Matrix period hPeriod variation hVariation,
    gaugeCoefficientC2CoreFrameTransport_identity]

/-- Explicit completed transition, preserving the noncommuting order of all roots. -/
def gaugeCoefficientC2RecenterTransition
    (shift total increment : C2Matrix period hPeriod)
    (coefficients : GaugeC2Core period hPeriod) : GaugeC2Core period hPeriod :=
  gaugeCoefficientC2CoreFrameTransport period hPeriod
    (regularGeneralMetricC2IdentityRootInverseC2Matrix period hPeriod increment)
    (gaugeCoefficientC2CoreFrameTransport period hPeriod
      (regularGeneralMetricC2IdentityRootInverseC2Matrix period hPeriod shift)
      (gaugeCoefficientC2CoreFrameTransport period hPeriod
        (c2IdentityRootBranch period hPeriod total) coefficients))

/-- The explicit completed expression equals the actual smooth coefficient transition. -/
theorem gaugeCoefficientRecenterTransition_eq_completed
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (shift increment : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hShift : regularGeneralMetricSmoothC2Variation period hPeriod metric shift ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric)
    (hTotal : regularGeneralMetricSmoothC2Variation period hPeriod metric (shift + increment) ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric)
    (hIncrement : regularGeneralMetricSmoothC2Variation period hPeriod
        (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod metric shift hShift) increment ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod
        (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod metric shift hShift))
    (coefficients : SmoothQuotientField period hPeriod GaugeFiber) :
    let shifted := regularGeneralMetricC2LorentzChartRegularMetric period hPeriod metric shift hShift
    let originalFinal := regularGeneralMetricC2LorentzChartRegularMetric period hPeriod
      metric (shift + increment) hTotal
    let recenteredFinal := regularGeneralMetricC2LorentzChartRegularMetric period hPeriod
      shifted increment hIncrement
    smoothGaugeCoefficientC2CoreLinearMap period hPeriod
        (regularFrameGaugeCoefficientTransition period hPeriod originalFinal recenteredFinal coefficients) =
      gaugeCoefficientC2RecenterTransition period hPeriod
        (regularGeneralMetricC2VariationMatrix period hPeriod metric shift)
        (regularGeneralMetricC2VariationMatrix period hPeriod metric (shift + increment))
        (regularGeneralMetricC2VariationMatrix period hPeriod shifted increment)
        (smoothGaugeCoefficientC2CoreLinearMap period hPeriod coefficients) := by
  let shifted := regularGeneralMetricC2LorentzChartRegularMetric period hPeriod metric shift hShift
  have hShiftRoot := regularGeneralMetricC2VariationMatrix_mem_invertibleRootDomain
    period hPeriod metric shift hShift
  have hIncrementRoot := regularGeneralMetricC2VariationMatrix_mem_invertibleRootDomain
    period hPeriod shifted increment hIncrement
  have hTransport := gaugeCoefficientRecenter_rootTransport period hPeriod
    metric shift increment hShift hTotal hIncrement coefficients
  have hCancel := congrArg (fun packet : GaugeC2Core period hPeriod =>
    gaugeCoefficientC2CoreFrameTransport period hPeriod
      (regularGeneralMetricC2IdentityRootInverseC2Matrix period hPeriod
        (regularGeneralMetricC2VariationMatrix period hPeriod shifted increment))
      (gaugeCoefficientC2CoreFrameTransport period hPeriod
        (regularGeneralMetricC2IdentityRootInverseC2Matrix period hPeriod
          (regularGeneralMetricC2VariationMatrix period hPeriod metric shift)) packet)) hTransport
  rw [gaugeCoefficientC2CoreFrameTransport_inverse_root period hPeriod _ hShiftRoot,
    gaugeCoefficientC2CoreFrameTransport_inverse_root period hPeriod _ hIncrementRoot] at hCancel
  exact hCancel

/-- Continuous linear transport of a varying coefficient packet through a fixed matrix. -/
def gaugeCoefficientC2CoreFrameTransportRightCLM (root : C2Matrix period hPeriod) :
    GaugeC2Core period hPeriod →L[Real] GaugeC2Core period hPeriod :=
  ContinuousLinearMap.pi fun baseIndex => ContinuousLinearMap.pi fun component =>
    ∑ movingIndex : Fin 4,
      (canonicalPhysicalScalarC2JetCoreProduct period hPeriod (root movingIndex baseIndex)).comp
        (gaugeCoefficientC2CoreComponentCLM period hPeriod movingIndex component)

@[simp]
theorem gaugeCoefficientC2CoreFrameTransportRightCLM_apply
    (root : C2Matrix period hPeriod) (coefficients : GaugeC2Core period hPeriod) :
    gaugeCoefficientC2CoreFrameTransportRightCLM period hPeriod root coefficients =
      gaugeCoefficientC2CoreFrameTransport period hPeriod root coefficients := by
  funext baseIndex component
  simp only [gaugeCoefficientC2CoreFrameTransportRightCLM, ContinuousLinearMap.pi_apply,
    sum_apply, ContinuousLinearMap.comp_apply]
  rfl

/-- The product rule retains the coefficient derivative as well as the frame derivative. -/
theorem gaugeCoefficientC2CoreFrameTransport_hasDerivAt
    (root : Real → C2Matrix period hPeriod)
    (coefficients : Real → GaugeC2Core period hPeriod)
    (rootVelocity : C2Matrix period hPeriod) (coefficientVelocity : GaugeC2Core period hPeriod)
    (time : Real) (hRoot : HasDerivAt root rootVelocity time)
    (hCoefficients : HasDerivAt coefficients coefficientVelocity time) :
    HasDerivAt (fun current => gaugeCoefficientC2CoreFrameTransport period hPeriod
      (root current) (coefficients current))
      (gaugeCoefficientC2CoreFrameTransport period hPeriod (root time) coefficientVelocity +
        gaugeCoefficientC2CoreFrameTransport period hPeriod rootVelocity (coefficients time)) time := by
  rw [hasDerivAt_pi]
  intro baseIndex
  rw [hasDerivAt_pi]
  intro component
  have hTerm (movingIndex : Fin 4) :=
    (canonicalPhysicalScalarC2JetCoreProduct period hPeriod).hasDerivAt_of_bilinear
      (fun _ => (gaugeFrameTransportC2MatrixEntryCLM period hPeriod movingIndex baseIndex).hasFDerivAt.comp_hasDerivAt
        time hRoot)
      (fun _ => (gaugeCoefficientC2CoreComponentCLM period hPeriod movingIndex component).hasFDerivAt.comp_hasDerivAt
        time hCoefficients)
  have hSum := HasDerivAt.fun_sum (u := Finset.univ) (fun movingIndex _ => hTerm movingIndex)
  simpa only [gaugeCoefficientC2CoreFrameTransport, Pi.add_apply, Finset.sum_add_distrib,
    Function.comp_def, gaugeFrameTransportC2MatrixEntryCLM, gaugeCoefficientC2CoreComponentCLM,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply] using hSum

/-- A concrete completed coefficient transition along a fixed metric line. -/
def gaugeCoefficientC2RecenterLine
    (shift oldDirection newDirection : C2Matrix period hPeriod)
    (coefficients : GaugeC2Core period hPeriod) (time : Real) : GaugeC2Core period hPeriod :=
  gaugeCoefficientC2RecenterTransition period hPeriod shift
    (shift + time • oldDirection) (time • newDirection) coefficients

/-- Actual derivative of the explicit recentering line. The first term differentiates
the old root away from zero; the second differentiates the inverse new root at zero. -/
theorem gaugeCoefficientC2RecenterLine_hasDerivAt_zero
    (shift oldDirection newDirection : C2Matrix period hPeriod)
    (hShift : shift ∈ c2IdentityRootInvertiblePerturbationDomain period hPeriod)
    (coefficients : GaugeC2Core period hPeriod) :
    HasDerivAt (gaugeCoefficientC2RecenterLine period hPeriod shift oldDirection newDirection coefficients)
      (gaugeCoefficientC2CoreFrameTransport period hPeriod
          (regularGeneralMetricC2IdentityRootInverseC2Matrix period hPeriod shift)
          (gaugeCoefficientC2CoreFrameTransport period hPeriod
            (c2IdentityRootDerivative period hPeriod shift hShift.1 oldDirection) coefficients) +
        gaugeCoefficientC2CoreFrameTransport period hPeriod (-((1 / 2 : Real) • newDirection)) coefficients) 0 := by
  unfold gaugeCoefficientC2RecenterLine gaugeCoefficientC2RecenterTransition
  have hOldLine : HasDerivAt (fun time : Real => shift + time • oldDirection) oldDirection 0 := by
    simpa only [one_smul, zero_add] using
      (hasDerivAt_const (0 : Real) shift).fun_add ((hasDerivAt_id' (0 : Real)).smul_const oldDirection)
  have hNewLine : HasDerivAt (fun time : Real => time • newDirection) newDirection 0 := by
    simpa only [one_smul] using (hasDerivAt_id' (0 : Real)).smul_const newDirection
  have hOldRoot := (c2IdentityGaugeCoefficientTransport_hasFDerivAt period hPeriod
    shift hShift.1 coefficients).comp_hasDerivAt_of_eq 0 hOldLine (by simp)
  have hMiddle := (gaugeCoefficientC2CoreFrameTransportRightCLM period hPeriod
    (regularGeneralMetricC2IdentityRootInverseC2Matrix period hPeriod shift)).hasFDerivAt.comp_hasDerivAt 0 hOldRoot
  have hNewInverse := (regularGeneralMetricC2IdentityRootInverse_hasFDerivAt period hPeriod 0
    (zero_mem_c2IdentityRootInvertiblePerturbationDomain period hPeriod)).comp_hasDerivAt_of_eq 0 hNewLine (by simp)
  simp only [regularGeneralMetricC2IdentityRootInverseDerivative_zero_apply] at hNewInverse
  have hDerivative := gaugeCoefficientC2CoreFrameTransport_hasDerivAt period hPeriod _ _ _ _ 0
    hNewInverse hMiddle
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
    gaugeCoefficientC2CoreFrameTransportRightCLM_apply,
    gaugeCoefficientC2CoreFrameTransportLeftCLM_apply,
    zero_smul, add_zero, regularGeneralMetricC2IdentityRootInverseC2Matrix_zero,
    gaugeCoefficientC2CoreFrameTransport_identity,
    gaugeCoefficientC2CoreFrameTransport_inverse_root period hPeriod shift hShift] using hDerivative

end
end P0EFTJanusGaugeCoefficientRecenterDerivative4D
end JanusFormal
