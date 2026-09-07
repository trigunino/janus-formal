import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGaugeCoefficientRecenterDerivative4D

/-! # Native Maxwell derivatives under actual gauge-dependent recentering -/

namespace JanusFormal
namespace P0EFTJanusMobileMaxwellDerivativeRecenter4D

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 600000
noncomputable section
open MeasureTheory Filter Set
open scoped Manifold ContDiff BigOperators Topology
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

private theorem realAffineLine_hasDerivAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] (base direction : E) :
    HasDerivAt (fun time : Real => base + time • direction) direction 0 := by
  simpa only [zero_add, one_smul] using
    (hasDerivAt_const (0 : Real) base).fun_add
      ((hasDerivAt_id' (0 : Real)).smul_const direction)

private theorem realLinearLine_hasDerivAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] (direction : E) :
    HasDerivAt (fun time : Real => time • direction) direction 0 := by
  simpa only [one_smul] using (hasDerivAt_id' (0 : Real)).smul_const direction

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

open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusProgramPRegularGeneralMetricC2GaugeCoefficientMaxwellAction4D
open P0EFTJanusLorentzChartAffineRecenterGeometry4D
open P0EFTJanusMobileMaxwellActionRecenter4D
open P0EFTJanusGaugeCoefficientRecenterDerivative4D

local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _
local instance : BorelSpace (EffectiveQuotient period hPeriod) where measurable_eq := rfl

attribute [local irreducible] regularGeneralMetricC0MobileGaugeCoefficientFixedVolumeMaxwellAction
attribute [local irreducible] regularGeneralMetricC2LorentzChartDomain

private theorem smoothMetricCore_smul
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (direction : SmoothSymmetricCovariantTwoTensor period hPeriod) (time : Real) :
    regularGeneralMetricSmoothC2Variation period hPeriod metric (time • direction) =
      time • regularGeneralMetricSmoothC2Variation period hPeriod metric direction := by
  unfold regularGeneralMetricSmoothC2Variation
  rw [map_smul]

private theorem smoothMetricMatrix_affine_line
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (shift direction : SmoothSymmetricCovariantTwoTensor period hPeriod) (time : Real) :
    regularGeneralMetricC2VariationMatrix period hPeriod metric (shift + time • direction) =
      regularGeneralMetricC2VariationMatrix period hPeriod metric shift +
        time • regularGeneralMetricC2VariationMatrix period hPeriod metric direction := by
  unfold regularGeneralMetricC2VariationMatrix
  rw [regularGeneralMetricSmoothC2Variation_affine_line]
  rfl

private theorem smoothMetricMatrix_smul
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (direction : SmoothSymmetricCovariantTwoTensor period hPeriod) (time : Real) :
    regularGeneralMetricC2VariationMatrix period hPeriod metric (time • direction) =
      time • regularGeneralMetricC2VariationMatrix period hPeriod metric direction := by
  unfold regularGeneralMetricC2VariationMatrix
  rw [smoothMetricCore_smul]
  rfl

private theorem completedRecenterLine_zero
    (shift oldDirection newDirection : C2Matrix period hPeriod)
    (hShift : shift ∈ c2IdentityRootInvertiblePerturbationDomain period hPeriod)
    (coefficients : GaugeC2Core period hPeriod) :
    gaugeCoefficientC2RecenterLine period hPeriod shift oldDirection newDirection coefficients 0 =
      coefficients := by
  simp only [gaugeCoefficientC2RecenterLine, gaugeCoefficientC2RecenterTransition,
    zero_smul, add_zero, regularGeneralMetricC2IdentityRootInverseC2Matrix_zero,
    gaugeCoefficientC2CoreFrameTransport_identity,
    gaugeCoefficientC2CoreFrameTransport_inverse_root period hPeriod shift hShift]

/-- Joint differentiability follows from the genuine mobile Maxwell C² action. -/
theorem mobileMaxwellJointAction_differentiableAt
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod)) [IsFiniteMeasure measure]
    (variation : RegularGeneralMetricC2Core period hPeriod metric)
    (coefficients : GaugeC2Core period hPeriod)
    (hVariation : variation ∈ regularGeneralMetricC2LorentzChartDomain period hPeriod metric) :
    DifferentiableAt Real
      (fun input : RegularGeneralMetricC2Core period hPeriod metric × GaugeC2Core period hPeriod =>
        regularGeneralMetricC0MobileGaugeCoefficientFixedVolumeMaxwellAction period hPeriod
          metric measure input.1 input.2) (variation, coefficients) := by
  have hDomain : (variation, coefficients) ∈
      regularGeneralMetricC2MobileGaugeCoefficientMaxwellDomain period hPeriod metric := by
    change variation ∈ regularGeneralMetricC2LorentzChartDomain period hPeriod metric ∧
      coefficients ∈ (Set.univ : Set (GaugeC2Core period hPeriod))
    exact ⟨hVariation, Set.mem_univ coefficients⟩
  have hOpen : IsOpen (regularGeneralMetricC2MobileGaugeCoefficientMaxwellDomain period hPeriod metric) := by
    change IsOpen ((regularGeneralMetricC2LorentzChartDomain period hPeriod metric) ×ˢ
      (Set.univ : Set (GaugeC2Core period hPeriod)))
    exact (regularGeneralMetricC2LorentzChartDomain_isOpen period hPeriod metric).prod isOpen_univ
  have hC2 : ContDiffAt Real 2
      (fun input : RegularGeneralMetricC2Core period hPeriod metric × GaugeC2Core period hPeriod =>
        regularGeneralMetricC0MobileGaugeCoefficientFixedVolumeMaxwellAction period hPeriod
          metric measure input.1 input.2) (variation, coefficients) :=
    (regularGeneralMetricC0MobileGaugeCoefficientFixedVolumeMaxwellAction_contDiffOn_two
      period hPeriod metric measure).contDiffAt (hOpen.mem_nhds hDomain)
  exact hC2.differentiableAt (by norm_num)

/-- The actual two actions agree along the same metric line only after retaining
the complete metric-dependent gauge transition. -/
theorem mobileMaxwellAction_line_eventuallyEq_recenter
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (shift direction : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hShift : regularGeneralMetricSmoothC2Variation period hPeriod metric shift ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric)
    (measure : Measure (EffectiveQuotient period hPeriod)) [IsFiniteMeasure measure]
    (coefficients : SmoothQuotientField period hPeriod GaugeFiber) :
    let shifted := regularGeneralMetricC2LorentzChartRegularMetric period hPeriod metric shift hShift
    let packet := smoothGaugeCoefficientC2CoreLinearMap period hPeriod coefficients
    (fun time : Real => regularGeneralMetricC0MobileGaugeCoefficientFixedVolumeMaxwellAction
      period hPeriod metric measure
      (regularGeneralMetricSmoothC2Variation period hPeriod metric shift +
        time • regularGeneralMetricSmoothC2Variation period hPeriod metric direction) packet) =ᶠ[𝓝 0]
    (fun time : Real => regularGeneralMetricC0MobileGaugeCoefficientFixedVolumeMaxwellAction
      period hPeriod shifted measure
      (time • regularGeneralMetricSmoothC2Variation period hPeriod shifted direction)
      (gaugeCoefficientC2RecenterLine period hPeriod
        (regularGeneralMetricC2VariationMatrix period hPeriod metric shift)
        (regularGeneralMetricC2VariationMatrix period hPeriod metric direction)
        (regularGeneralMetricC2VariationMatrix period hPeriod shifted direction) packet time)) := by
  dsimp only
  filter_upwards [lorentzChartRecenter_line_eventually_admissible period hPeriod
    metric shift direction hShift] with time ht
  have hAction := mobileMaxwellAction_recenter period hPeriod metric shift (time • direction)
    hShift ht.1 ht.2 measure coefficients
  have hGauge := gaugeCoefficientRecenterTransition_eq_completed period hPeriod
    metric shift (time • direction) hShift ht.1 ht.2 coefficients
  dsimp only at hAction hGauge
  rw [hGauge] at hAction
  simpa only [regularGeneralMetricSmoothC2Variation_affine_line, smoothMetricCore_smul,
    smoothMetricMatrix_affine_line, smoothMetricMatrix_smul, gaugeCoefficientC2RecenterLine] using hAction

/-- Actual completed gauge velocity forced by the change of metric chart. -/
def mobileMaxwellRecenterGaugeVelocity
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (shift direction : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hShift : regularGeneralMetricSmoothC2Variation period hPeriod metric shift ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric)
    (coefficients : GaugeC2Core period hPeriod) : GaugeC2Core period hPeriod :=
  let shifted := regularGeneralMetricC2LorentzChartRegularMetric period hPeriod metric shift hShift
  let matrix := regularGeneralMetricC2VariationMatrix period hPeriod metric shift
  let hMatrix := regularGeneralMetricC2VariationMatrix_mem_invertibleRootDomain
    period hPeriod metric shift hShift
  gaugeCoefficientC2CoreFrameTransport period hPeriod
    (regularGeneralMetricC2IdentityRootInverseC2Matrix period hPeriod matrix)
    (gaugeCoefficientC2CoreFrameTransport period hPeriod
      (c2IdentityRootDerivative period hPeriod matrix hMatrix.1
        (regularGeneralMetricC2VariationMatrix period hPeriod metric direction)) coefficients) +
    gaugeCoefficientC2CoreFrameTransport period hPeriod
      (-((1 / 2 : Real) • regularGeneralMetricC2VariationMatrix period hPeriod shifted direction)) coefficients

/-- The native metric derivative away from zero becomes the genuine joint metric/gauge
derivative at the new centre. The potentially nonzero transition velocity is retained in C². -/
theorem mobileMaxwellAction_fderiv_recenter_joint
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (shift direction : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hShift : regularGeneralMetricSmoothC2Variation period hPeriod metric shift ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric)
    (measure : Measure (EffectiveQuotient period hPeriod)) [IsFiniteMeasure measure]
    (coefficients : SmoothQuotientField period hPeriod GaugeFiber) :
    let shifted := regularGeneralMetricC2LorentzChartRegularMetric period hPeriod metric shift hShift
    let packet := smoothGaugeCoefficientC2CoreLinearMap period hPeriod coefficients
    fderiv Real
        (fun variation => regularGeneralMetricC0MobileGaugeCoefficientFixedVolumeMaxwellAction
          period hPeriod metric measure variation packet)
        (regularGeneralMetricSmoothC2Variation period hPeriod metric shift)
        (regularGeneralMetricSmoothC2Variation period hPeriod metric direction) =
      fderiv Real
        (fun input : RegularGeneralMetricC2Core period hPeriod shifted × GaugeC2Core period hPeriod =>
          regularGeneralMetricC0MobileGaugeCoefficientFixedVolumeMaxwellAction period hPeriod
            shifted measure input.1 input.2)
        (0, packet)
        (regularGeneralMetricSmoothC2Variation period hPeriod shifted direction,
          mobileMaxwellRecenterGaugeVelocity period hPeriod metric shift direction hShift packet) := by
  let shifted := regularGeneralMetricC2LorentzChartRegularMetric period hPeriod metric shift hShift
  let packet := smoothGaugeCoefficientC2CoreLinearMap period hPeriod coefficients
  let base := regularGeneralMetricSmoothC2Variation period hPeriod metric shift
  let oldDirection := regularGeneralMetricSmoothC2Variation period hPeriod metric direction
  let newDirection := regularGeneralMetricSmoothC2Variation period hPeriod shifted direction
  let shiftMatrix := regularGeneralMetricC2VariationMatrix period hPeriod metric shift
  let oldMatrix := regularGeneralMetricC2VariationMatrix period hPeriod metric direction
  let newMatrix := regularGeneralMetricC2VariationMatrix period hPeriod shifted direction
  let velocity := mobileMaxwellRecenterGaugeVelocity period hPeriod metric shift direction hShift packet
  let oldAction := fun variation => regularGeneralMetricC0MobileGaugeCoefficientFixedVolumeMaxwellAction
    period hPeriod metric measure variation packet
  let newJoint := fun input : RegularGeneralMetricC2Core period hPeriod shifted × GaugeC2Core period hPeriod =>
    regularGeneralMetricC0MobileGaugeCoefficientFixedVolumeMaxwellAction period hPeriod
      shifted measure input.1 input.2
  have hMatrix := regularGeneralMetricC2VariationMatrix_mem_invertibleRootDomain
    period hPeriod metric shift hShift
  have hOldJoint := mobileMaxwellJointAction_differentiableAt period hPeriod metric measure base packet hShift
  have hOldAt : DifferentiableAt Real oldAction base := by
    have hEmbedding : DifferentiableAt Real
        (fun current : RegularGeneralMetricC2Core period hPeriod metric => (current, packet)) base :=
      differentiableAt_id.prodMk (differentiableAt_const packet)
    simpa only [Function.comp_def, oldAction] using hOldJoint.comp base hEmbedding
  have hNewAt : DifferentiableAt Real newJoint (0, packet) :=
    mobileMaxwellJointAction_differentiableAt period hPeriod shifted measure 0 packet
      (zero_mem_regularGeneralMetricC2LorentzChartDomain period hPeriod shifted)
  have hOldInput : HasDerivAt (fun time : Real => base + time • oldDirection) oldDirection 0 :=
    realAffineLine_hasDerivAt base oldDirection
  have hOldLine : HasDerivAt (fun time : Real => oldAction (base + time • oldDirection))
      (fderiv Real oldAction base oldDirection) 0 := by
    simpa only [Function.comp_def] using
      hOldAt.hasFDerivAt.comp_hasDerivAt_of_eq 0 hOldInput (by simp only [zero_smul, add_zero])
  have hMetricLine : HasDerivAt (fun time : Real => time • newDirection) newDirection 0 :=
    realLinearLine_hasDerivAt newDirection
  have hGaugeLine : HasDerivAt
      (gaugeCoefficientC2RecenterLine period hPeriod shiftMatrix oldMatrix newMatrix packet) velocity 0 :=
    gaugeCoefficientC2RecenterLine_hasDerivAt_zero period hPeriod shiftMatrix oldMatrix newMatrix hMatrix packet
  have hInput := hMetricLine.prodMk hGaugeLine
  have hCenter : (0, packet) =
      ((0 : Real) • newDirection,
        gaugeCoefficientC2RecenterLine period hPeriod shiftMatrix oldMatrix newMatrix packet 0) := by
    rw [zero_smul, completedRecenterLine_zero period hPeriod shiftMatrix oldMatrix newMatrix hMatrix]
  have hNewLine : HasDerivAt
      (fun time : Real => newJoint (time • newDirection,
        gaugeCoefficientC2RecenterLine period hPeriod shiftMatrix oldMatrix newMatrix packet time))
      (fderiv Real newJoint (0, packet) (newDirection, velocity)) 0 := by
    simpa only [Function.comp_def] using
      hNewAt.hasFDerivAt.comp_hasDerivAt_of_eq 0 hInput hCenter
  have hGerm := mobileMaxwellAction_line_eventuallyEq_recenter period hPeriod
    metric shift direction hShift measure coefficients
  exact hOldLine.unique (hNewLine.congr_of_eventuallyEq hGerm)

end
end P0EFTJanusMobileMaxwellDerivativeRecenter4D
end JanusFormal
