import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFixedVolumeEinsteinHilbertActionRecenter4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusLorentzChartAffineRecenterGeometry4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusStoredVolumePalatiniMetricResidual4D

/-!
# Native fixed-volume Einstein--Hilbert derivatives at admissible smooth points

Equality of the actual actions along a common smooth tensor line transports
the directional derivative to the new center.  The canonical consequence
retains the complete stored-volume Ricci and Palatini residual.
-/

namespace JanusFormal
namespace P0EFTJanusFixedVolumeEinsteinHilbertDerivativeRecenter4D

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 600000

noncomputable section

open MeasureTheory
open scoped Manifold ContDiff Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVFirstLevel4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVPairingRegularity4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusIntrinsicEinsteinHilbertAction4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartRegularMetric4D
open P0EFTJanusProgramPRegularGeneralMetricC2MaxwellStressDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbertFixedVariableVolumeDiscrepancy4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedFixedVolumeEinsteinHilbertC24D
open P0EFTJanusFixedVolumeEinsteinHilbertActionRecenter4D
open P0EFTJanusLorentzChartAffineRecenterGeometry4D
open P0EFTJanusStoredVolumePalatiniMetricResidual4D

private theorem hasDerivAt_action_affine_line
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {action : E → Real} {base : E} {derivative : E →L[Real] Real}
    (hAction : HasFDerivAt action derivative base) (direction : E) :
    HasDerivAt (fun t : Real => action (base + t • direction))
      (derivative direction) 0 := by
  have hLine : HasDerivAt (fun t : Real => base + t • direction) direction 0 := by
    simpa only [zero_add, one_smul] using
      (hasDerivAt_const (x := (0 : Real)) (c := base)).fun_add
        ((hasDerivAt_id' (0 : Real)).smul_const direction)
  simpa only [Function.comp_def] using
    hAction.comp_hasDerivAt_of_eq 0 hLine (by simp only [zero_smul, add_zero])

private theorem hasDerivAt_action_origin_line
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {action : E → Real} {derivative : E →L[Real] Real}
    (hAction : HasFDerivAt action derivative 0) (direction : E) :
    HasDerivAt (fun t : Real => action (t • direction)) (derivative direction) 0 := by
  simpa only [zero_add] using hasDerivAt_action_affine_line hAction direction

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

attribute [local irreducible] regularGeneralMetricC0FixedVolumeEinsteinHilbertAction

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev C2Scalar :=
  CanonicalPhysicalScalarC2JetCore period hPeriod

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

/-- The genuine completed actions agree near zero on the same affine tensor
line, expressed in the two completed cores. -/
theorem regularGeneralMetricC0FixedVolumeEinsteinHilbertAction_line_eventuallyEq_recenter
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (shift direction : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hShift : regularGeneralMetricSmoothC2Variation period hPeriod metric shift ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric)
    (measure : Measure (EffectiveQuotient period hPeriod)) [IsFiniteMeasure measure]
    (couplings : EinsteinHilbertCouplings) :
    (fun t : Real => regularGeneralMetricC0FixedVolumeEinsteinHilbertAction
      period hPeriod metric measure couplings
      (regularGeneralMetricSmoothC2Variation period hPeriod metric shift +
        t • regularGeneralMetricSmoothC2Variation period hPeriod metric direction)) =ᶠ[𝓝 0]
    (fun t : Real => regularGeneralMetricC0FixedVolumeEinsteinHilbertAction
      period hPeriod
      (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod metric shift hShift)
      measure couplings
      (t • regularGeneralMetricSmoothC2Variation period hPeriod
        (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod metric shift hShift)
        direction)) := by
  filter_upwards [lorentzChartRecenter_line_eventually_admissible period hPeriod
    metric shift direction hShift] with t ht
  have hAction := regularGeneralMetricC0FixedVolumeEinsteinHilbertAction_recenter
    period hPeriod metric shift (t • direction) hShift ht.1 ht.2 measure couplings
  rw [regularGeneralMetricSmoothC2Variation_affine_line] at hAction
  simpa only [regularGeneralMetricSmoothC2Variation, map_smul] using hAction

/-- The native derivative at an arbitrary admissible smooth shift is exactly
the derivative at zero in the reconstructed chart, on the same smooth tensor. -/
theorem regularGeneralMetricC0FixedVolumeEinsteinHilbertAction_fderiv_recenter
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (shift direction : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hShift : regularGeneralMetricSmoothC2Variation period hPeriod metric shift ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric)
    (measure : Measure (EffectiveQuotient period hPeriod)) [IsFiniteMeasure measure]
    (couplings : EinsteinHilbertCouplings) :
    fderiv Real (regularGeneralMetricC0FixedVolumeEinsteinHilbertAction
        period hPeriod metric measure couplings)
      (regularGeneralMetricSmoothC2Variation period hPeriod metric shift)
      (regularGeneralMetricSmoothC2Variation period hPeriod metric direction) =
    fderiv Real (regularGeneralMetricC0FixedVolumeEinsteinHilbertAction
        period hPeriod
        (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod metric shift hShift)
        measure couplings) 0
      (regularGeneralMetricSmoothC2Variation period hPeriod
        (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod metric shift hShift)
        direction) := by
  let recentered := regularGeneralMetricC2LorentzChartRegularMetric period hPeriod
    metric shift hShift
  let oldAction : RegularGeneralMetricC2Core period hPeriod metric → Real :=
    regularGeneralMetricC0FixedVolumeEinsteinHilbertAction
    period hPeriod metric measure couplings
  let newAction : RegularGeneralMetricC2Core period hPeriod recentered → Real :=
    regularGeneralMetricC0FixedVolumeEinsteinHilbertAction
    period hPeriod recentered measure couplings
  let base : RegularGeneralMetricC2Core period hPeriod metric :=
    regularGeneralMetricSmoothC2Variation period hPeriod metric shift
  let oldDirection : RegularGeneralMetricC2Core period hPeriod metric :=
    regularGeneralMetricSmoothC2Variation period hPeriod metric direction
  let newDirection : RegularGeneralMetricC2Core period hPeriod recentered :=
    regularGeneralMetricSmoothC2Variation period hPeriod recentered direction
  have hOldAt : HasFDerivAt oldAction (fderiv Real oldAction base) base :=
    (((regularGeneralMetricC0FixedVolumeEinsteinHilbertAction_contDiffOn_two
      period hPeriod metric measure couplings).contDiffAt
      ((regularGeneralMetricC2Domain_isOpen period hPeriod metric).mem_nhds hShift.1)
      ).differentiableAt (by norm_num)).hasFDerivAt
  have hNewAt : HasFDerivAt newAction (fderiv Real newAction 0) 0 :=
    (regularGeneralMetricC0FixedVolumeEinsteinHilbertAction_hasFDerivAt_zero
      period hPeriod recentered measure couplings).differentiableAt.hasFDerivAt
  have hOldLine : HasDerivAt (fun t : Real => oldAction (base + t • oldDirection))
      (fderiv Real oldAction base oldDirection) 0 :=
    hasDerivAt_action_affine_line hOldAt oldDirection
  have hNewLine : HasDerivAt (fun t : Real => newAction (t • newDirection))
      (fderiv Real newAction 0 newDirection) 0 :=
    hasDerivAt_action_origin_line hNewAt newDirection
  have hGerm :=
    regularGeneralMetricC0FixedVolumeEinsteinHilbertAction_line_eventuallyEq_recenter
      period hPeriod metric shift direction hShift measure couplings
  exact hOldLine.unique (hNewLine.congr_of_eventuallyEq hGerm)

/-- The full canonical residual represents the native derivative at every
admissible smooth shift, with the original stored volume and no gauge assumption. -/
theorem regularGeneralMetricC0FixedVolumeEinsteinHilbertAction_fderiv_eq_recenteredResidualIntegral
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (shift direction : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hShift : regularGeneralMetricSmoothC2Variation period hPeriod metric shift ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric)
    (couplings : EinsteinHilbertCouplings) :
    fderiv Real (regularGeneralMetricC0FixedVolumeEinsteinHilbertAction
        period hPeriod metric (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) couplings)
      (regularGeneralMetricSmoothC2Variation period hPeriod metric shift)
      (regularGeneralMetricSmoothC2Variation period hPeriod metric direction) =
    ∫ point, generalMetricTensorPairingAt period hPeriod
      (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod metric shift hShift).metric
      (regularFrameStoredVolumeEinsteinHilbertResidual period hPeriod
        (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod metric shift hShift)
        couplings.gravitationalCoupling)
      direction point ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod := by
  rw [regularGeneralMetricC0FixedVolumeEinsteinHilbertAction_fderiv_recenter
    period hPeriod metric shift direction hShift]
  rw [(regularGeneralMetricC0FixedVolumeEinsteinHilbertAction_hasFDerivAt_zero
    period hPeriod
    (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod metric shift hShift)
    (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) couplings).fderiv]
  simpa only [regularGeneralMetricSmoothC2Variation, regularGeneralMetricC2SmoothDirection] using
    regularFrameFixedVolumeEinsteinHilbertDerivative_eq_ungaugedResidualIntegral
      period hPeriod
      (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod metric shift hShift)
      couplings direction

end

end P0EFTJanusFixedVolumeEinsteinHilbertDerivativeRecenter4D
end JanusFormal
