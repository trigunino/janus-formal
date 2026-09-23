import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FullMaxwellMetricL24D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12MaxwellCoefficientQuadratic4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12QuadraticParameterDerivative4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12MaxwellStressCoefficients4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12InducedMaxwellMetricL24D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12RegularTensorCovectorL24D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusStrongMaxwellMetricResidual4D

/-! Actual L2 bound for the potential derivative of the full Maxwell metric variation. -/
namespace JanusFormal
namespace P0EFTJanusProgramPT12MaxwellMixedMetricL24D

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 600000

noncomputable section
open MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVFirstLevel4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVUltralocalMaster4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVPairingRegularity4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusProgramPGlobalGaugeTangentIntrinsicEmbedding4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2MaxwellStressDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalMetricGaugeCoreProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2GaugeCoefficientFrameTransport4D
open P0EFTJanusProgramPRegularGeneralMetricC2GaugeCoefficientMaxwellAction4D
open P0EFTJanusProgramPRegularFrameMaxwellSmoothGaugeTestSeparation4D
open P0EFTJanusProgramPRegularFrameCanonicalMaxwellVariationalResidual4D
open P0EFTJanusStrongMaxwellMetricCenterFirstVariation4D
open P0EFTJanusFixedVolumeMaxwellStressResidual4D
open P0EFTJanusMetricInducedSmoothGaugeVelocity4D
open P0EFTJanusGaugeCoefficientMaxwellIntrinsicFirstVariation4D
open P0EFTJanusMetricInducedMaxwellResidual4D

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
local instance : IsFiniteMeasure (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod
local instance : NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (C2Scalar period hPeriod) := inferInstance

open scoped InnerProductSpace
open P0EFTJanusProgramPT12RegularTensorCovectorL24D
open P0EFTJanusProgramPGlobalGeneralMetricDeDonderGraphCore4D
open P0EFTJanusStrongMaxwellMetricResidual4D

variable (metric : RegularGeneralLorentzMetric period hPeriod)
  (potential : SmoothAbelianGaugePotential period hPeriod)

open P0EFTJanusProgramPT12MaxwellStressCoefficients4D
open P0EFTJanusProgramPT12InducedMaxwellMetricL24D

open P0EFTJanusProgramPT12FullMaxwellMetricL24D
open P0EFTJanusProgramPT12MaxwellCoefficientQuadratic4D
open P0EFTJanusProgramPT12QuadraticParameterDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartDomain4D

/-- Quadratic dependence on genuine smooth potentials, retaining mobile-frame transport. -/
def smoothMobileMaxwellQuadratic (variation : RegularGeneralMetricC2Core period hPeriod metric) :
    QuadraticForm Real (SmoothAbelianGaugePotential period hPeriod) :=
  (mobileMaxwellActionQuadratic period hPeriod metric variation).comp
    ((smoothGaugeCoefficientC2CoreLinearMap period hPeriod).comp
      (gaugePotentialFrameCoefficientsLinearMap period hPeriod metric))

theorem smoothMobileMaxwellQuadratic_apply
    (variation : RegularGeneralMetricC2Core period hPeriod metric) :
    smoothMobileMaxwellQuadratic period hPeriod metric variation potential =
      regularGeneralMetricC0MobileGaugeCoefficientFixedVolumeMaxwellAction period hPeriod metric
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) variation
        (smoothGaugeCoefficientC2CoreLinearMap period hPeriod
          (gaugePotentialFrameCoefficients period hPeriod metric potential)) := by
  unfold smoothMobileMaxwellQuadratic
  rw [QuadraticMap.comp_apply, mobileMaxwellActionQuadratic_apply]
  rfl

theorem smoothMobileMaxwellQuadratic_differentiableAt :
    DifferentiableAt Real (fun variation =>
      smoothMobileMaxwellQuadratic period hPeriod metric variation potential) 0 := by
  let coefficients := smoothGaugeCoefficientC2CoreLinearMap period hPeriod
    (gaugePotentialFrameCoefficients period hPeriod metric potential)
  have hOpen : IsOpen (regularGeneralMetricC2MobileGaugeCoefficientMaxwellDomain period hPeriod metric) :=
    (regularGeneralMetricC2LorentzChartDomain_isOpen period hPeriod metric).prod isOpen_univ
  have hCenter : (0, coefficients) ∈
      regularGeneralMetricC2MobileGaugeCoefficientMaxwellDomain period hPeriod metric :=
    ⟨zero_mem_regularGeneralMetricC2LorentzChartDomain period hPeriod metric, Set.mem_univ _⟩
  have hJoint := ((regularGeneralMetricC0MobileGaugeCoefficientFixedVolumeMaxwellAction_contDiffOn_two
    period hPeriod metric (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)).contDiffAt
      (hOpen.mem_nhds hCenter)).differentiableAt (by norm_num)
  have hInput : DifferentiableAt Real
      (fun variation : RegularGeneralMetricC2Core period hPeriod metric => (variation, coefficients)) 0 :=
    differentiableAt_id.prodMk (differentiableAt_const coefficients)
  simpa only [smoothMobileMaxwellQuadratic_apply, Function.comp_def, coefficients] using hJoint.comp 0 hInput

attribute [local irreducible] smoothMobileMaxwellQuadratic

/-- Polarization of three already constructed L2 vectors. -/
def maxwellMixedMetricRiesz (direction : SmoothAbelianGaugePotential period hPeriod) :
    GlobalGeneralMetricTensorFrameL2 period hPeriod :=
  fullMaxwellMetricRiesz period hPeriod metric (potential + direction) -
    fullMaxwellMetricRiesz period hPeriod metric potential -
    fullMaxwellMetricRiesz period hPeriod metric direction

theorem fullMaxwellMetricVariation_hasDerivAt_potential
    (direction : SmoothAbelianGaugePotential period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    HasDerivAt (fun t : Real => fullMaxwellMetricVariation period hPeriod metric
      (potential + t • direction) tensor)
      (inner Real (maxwellMixedMetricRiesz period hPeriod metric potential direction)
        (globalGeneralMetricTensorFrameL2LinearMap period hPeriod tensor)) 0 := by
  have h := quadraticParameterDerivative_hasDerivAt
    (smoothMobileMaxwellQuadratic period hPeriod metric) 0
    (regularGeneralMetricC2SmoothDirection period hPeriod metric tensor) potential direction
    (smoothMobileMaxwellQuadratic_differentiableAt period hPeriod metric potential)
    (smoothMobileMaxwellQuadratic_differentiableAt period hPeriod metric direction)
    (smoothMobileMaxwellQuadratic_differentiableAt period hPeriod metric (potential + direction))
  have hEq (current : SmoothAbelianGaugePotential period hPeriod) :
      quadraticParameterDerivative (smoothMobileMaxwellQuadratic period hPeriod metric) 0
        (regularGeneralMetricC2SmoothDirection period hPeriod metric tensor) current =
      fullMaxwellMetricVariation period hPeriod metric current tensor := by
    unfold quadraticParameterDerivative fullMaxwellMetricVariation
    simp_rw [smoothMobileMaxwellQuadratic_apply]
  simp_rw [hEq] at h
  simpa only [fullMaxwellMetricVariation_eq_inner, maxwellMixedMetricRiesz, inner_sub_left] using h

/-- An actual iterated derivative, bounded by the zeroth-order metric norm. -/
theorem maxwellMixedMetricVariation_bound
    (direction : SmoothAbelianGaugePotential period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    ‖deriv (fun t : Real => fullMaxwellMetricVariation period hPeriod metric
      (potential + t • direction) tensor) 0‖ ≤
      ‖maxwellMixedMetricRiesz period hPeriod metric potential direction‖ *
        ‖globalGeneralMetricTensorFrameL2LinearMap period hPeriod tensor‖ := by
  rw [(fullMaxwellMetricVariation_hasDerivAt_potential period hPeriod metric potential direction tensor).deriv]
  exact norm_inner_le_norm _ _

end
end P0EFTJanusProgramPT12MaxwellMixedMetricL24D
end JanusFormal
