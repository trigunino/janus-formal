import Mathlib.Analysis.Calculus.ParametricIntegral
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntrinsicAbelianMaxwellAction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntrinsicEinsteinHilbertAction4D

/-!
# Genuine metric variation of the intrinsic Einstein--Maxwell bulk action

A regular line consists of actual Einstein--Hilbert metrics at every
parameter.  Its smooth velocity fields are constrained to be the derivatives
of the volume and computed scalar-curvature fields.  The Maxwell pairing is
likewise constrained chartwise to the curvature `F = dA`, and its velocity is
its actual parameter derivative.

Only the standard domination needed to exchange derivative and integral is
assumed.  No Euler coefficient is supplied independently.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusIntrinsicEinsteinMaxwellMetricVariation4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 500000

noncomputable section

open Filter MeasureTheory
open scoped Manifold ContDiff Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusAbelianGaugeNoetherOperator4D
open P0EFTJanusMappingTorusIntrinsicAbelianMaxwellCurvature4D
open P0EFTJanusMappingTorusIntrinsicAbelianMaxwellAction4D
open P0EFTJanusMappingTorusIntrinsicEinsteinHilbertAction4D

variable (period : Real) (hPeriod : period ≠ 0)

local instance localRealNormedAddCommGroup : NormedAddCommGroup Real :=
  inferInstance

local instance localRealNormedSpace : NormedSpace Real Real :=
  inferInstance

local instance localRealAddCommGroup : AddCommGroup Real :=
  localRealNormedAddCommGroup.toAddCommGroup

local instance (priority := 10000) localRealModule : Module Real Real :=
  localRealNormedSpace.toModule

abbrev Vector4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient :=
  MappingTorus (sphereData period hPeriod)

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

/-- A genuine smooth line of regular Einstein--Hilbert metrics.  The two
velocity fields are regularity witnesses tied to actual derivatives. -/
structure RegularEinsteinHilbertMetricLine where
  data : Real → RegularEinsteinHilbertMetric period hPeriod
  volume_contDiff : ∀ point,
    ContDiff Real ∞ (fun parameter => (data parameter).metric.volume point)
  scalarCurvature_contDiff : ∀ point,
    ContDiff Real ∞ (fun parameter => (data parameter).scalarCurvature point)
  volumeVelocity : Real → SmoothScalarField period hPeriod
  scalarCurvatureVelocity : Real → SmoothScalarField period hPeriod
  volumeVelocity_eq : ∀ parameter point,
    volumeVelocity parameter point =
      deriv (fun varied => (data varied).metric.volume point) parameter
  scalarCurvatureVelocity_eq : ∀ parameter point,
    scalarCurvatureVelocity parameter point =
      deriv (fun varied => (data varied).scalarCurvature point) parameter

/-- Exact pointwise first variation of the EH density. -/
def regularEinsteinHilbertMetricFirstVariationFieldAt
    (couplings : EinsteinHilbertCouplings)
    (line : RegularEinsteinHilbertMetricLine period hPeriod)
    (parameter : Real) : SmoothScalarField period hPeriod where
  toFun := fun point =>
    line.volumeVelocity parameter point *
        ((1 / (2 * couplings.gravitationalCoupling)) *
          ((line.data parameter).scalarCurvature point -
            2 * couplings.cosmologicalConstant)) +
      (line.data parameter).metric.volume point *
        ((1 / (2 * couplings.gravitationalCoupling)) *
          line.scalarCurvatureVelocity parameter point)
  contMDiff_toFun :=
    (line.volumeVelocity parameter).contMDiff_toFun.mul
        (contMDiff_const.mul
          ((line.data parameter).scalarCurvature.contMDiff_toFun.sub
            contMDiff_const)) |>.add
      ((line.data parameter).metric.volume.contMDiff_toFun.mul
        (contMDiff_const.mul
          (line.scalarCurvatureVelocity parameter).contMDiff_toFun))

/-- Pointwise derivative of the actual EH density along a regular metric
line. -/
theorem regularEinsteinHilbertDensityField_metricLine_hasDerivAt
    (couplings : EinsteinHilbertCouplings)
    (line : RegularEinsteinHilbertMetricLine period hPeriod)
    (parameter : Real) (point : EffectiveQuotient period hPeriod) :
    HasDerivAt
      (fun varied =>
        regularEinsteinHilbertDensityField period hPeriod couplings
          (line.data varied) point)
      (regularEinsteinHilbertMetricFirstVariationFieldAt period hPeriod
        couplings line parameter point)
      parameter := by
  have hVolume : HasDerivAt
      (fun varied => (line.data varied).metric.volume point)
      (deriv (fun varied => (line.data varied).metric.volume point) parameter)
      parameter :=
    ((line.volume_contDiff point).differentiable (by simp))
      |>.differentiableAt.hasDerivAt
  have hScalar : HasDerivAt
      (fun varied => (line.data varied).scalarCurvature point)
      (deriv (fun varied => (line.data varied).scalarCurvature point) parameter)
      parameter :=
    ((line.scalarCurvature_contDiff point).differentiable (by simp))
      |>.differentiableAt.hasDerivAt
  change HasDerivAt
    (fun varied =>
      (line.data varied).metric.volume point *
        ((1 / (2 * couplings.gravitationalCoupling)) *
          ((line.data varied).scalarCurvature point -
            2 * couplings.cosmologicalConstant)))
    (line.volumeVelocity parameter point *
        ((1 / (2 * couplings.gravitationalCoupling)) *
          ((line.data parameter).scalarCurvature point -
            2 * couplings.cosmologicalConstant)) +
      (line.data parameter).metric.volume point *
        ((1 / (2 * couplings.gravitationalCoupling)) *
          line.scalarCurvatureVelocity parameter point))
    parameter
  rw [line.volumeVelocity_eq, line.scalarCurvatureVelocity_eq]
  have hProduct :=
    hVolume.mul
      ((hScalar.sub_const (2 * couplings.cosmologicalConstant)).const_mul
        (1 / (2 * couplings.gravitationalCoupling)))
  convert hProduct using 1 <;> rfl

/-- EH action evaluated on the genuine metric line. -/
def intrinsicEinsteinHilbertMetricActionCurve
    (couplings : EinsteinHilbertCouplings)
    (line : RegularEinsteinHilbertMetricLine period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    (parameter : Real) : Real :=
  intrinsicEinsteinHilbertAction period hPeriod couplings
    (line.data parameter) measure

/-- Integrated exact EH first variation. -/
def intrinsicEinsteinHilbertMetricFirstVariation
    (couplings : EinsteinHilbertCouplings)
    (line : RegularEinsteinHilbertMetricLine period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod)) : Real :=
  ∫ point,
    regularEinsteinHilbertMetricFirstVariationFieldAt period hPeriod
      couplings line 0 point ∂measure

/-- Analytic domination required only for exchanging the genuine pointwise
derivative with the integral. -/
structure DominatedEinsteinHilbertMetricVariation
    (couplings : EinsteinHilbertCouplings)
    (line : RegularEinsteinHilbertMetricLine period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod)) where
  parameterDomain : Set Real
  parameterDomain_mem_nhds : parameterDomain ∈ 𝓝 (0 : Real)
  bound : EffectiveQuotient period hPeriod → Real
  derivative_norm_le : ∀ᵐ point ∂measure,
    ∀ parameter ∈ parameterDomain,
      ‖regularEinsteinHilbertMetricFirstVariationFieldAt period hPeriod
        couplings line parameter point‖ ≤ bound point
  bound_integrable : Integrable bound measure

/-- On the compact mapping torus, joint continuity of the EH first
variation automatically supplies the domination contract needed below. -/
noncomputable def dominatedEinsteinHilbertMetricVariation_of_jointContinuous
    (couplings : EinsteinHilbertCouplings)
    (line : RegularEinsteinHilbertMetricLine period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (hJoint : Continuous
      (fun input : Real × EffectiveQuotient period hPeriod =>
        regularEinsteinHilbertMetricFirstVariationFieldAt period hPeriod
          couplings line input.1 input.2)) :
    DominatedEinsteinHilbertMetricVariation period hPeriod
      couplings line measure := by
  have hCompact : IsCompact
      (Set.Icc (-1 : Real) 1 ×ˢ
        (Set.univ : Set (EffectiveQuotient period hPeriod))) :=
    isCompact_Icc.prod isCompact_univ
  let hBounded := hCompact.bddAbove_image hJoint.norm.continuousOn
  let bound : Real := Classical.choose hBounded
  have hBound := Classical.choose_spec hBounded
  exact
    { parameterDomain := Set.Icc (-1 : Real) 1
      parameterDomain_mem_nhds :=
        Icc_mem_nhds (by norm_num : (-1 : Real) < 0)
          (by norm_num : (0 : Real) < 1)
      bound := fun _ => bound
      derivative_norm_le := by
        filter_upwards with point
        intro parameter hParameter
        exact hBound (Set.mem_image_of_mem _
          (Set.mk_mem_prod hParameter (Set.mem_univ point)))
      bound_integrable := integrable_const bound }

/-- The integrated EH action differentiates along every dominated regular
metric line. -/
theorem intrinsicEinsteinHilbertMetricActionCurve_hasDerivAt
    (couplings : EinsteinHilbertCouplings)
    (line : RegularEinsteinHilbertMetricLine period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (contract : DominatedEinsteinHilbertMetricVariation period hPeriod
      couplings line measure) :
    HasDerivAt
      (intrinsicEinsteinHilbertMetricActionCurve period hPeriod
        couplings line measure)
      (intrinsicEinsteinHilbertMetricFirstVariation period hPeriod
        couplings line measure)
      0 := by
  have hDensityMeasurable : ∀ᶠ parameter in 𝓝 (0 : Real),
      AEStronglyMeasurable
        (fun point =>
          regularEinsteinHilbertDensityField period hPeriod couplings
            (line.data parameter) point)
        measure :=
    Filter.Eventually.of_forall fun parameter =>
      (regularEinsteinHilbertDensityField period hPeriod couplings
        (line.data parameter)).contMDiff_toFun.continuous.aestronglyMeasurable
  have hDensityIntegrable :
      Integrable
        (fun point =>
          regularEinsteinHilbertDensityField period hPeriod couplings
            (line.data 0) point)
        measure :=
    regularEinsteinHilbertDensityField_integrable period hPeriod couplings
      (line.data 0) measure
  have hVariationMeasurable :
      AEStronglyMeasurable
        (regularEinsteinHilbertMetricFirstVariationFieldAt period hPeriod
          couplings line 0)
        measure :=
    (regularEinsteinHilbertMetricFirstVariationFieldAt period hPeriod
      couplings line 0).contMDiff_toFun.continuous.aestronglyMeasurable
  have hPointwise : ∀ᵐ point ∂measure,
      ∀ parameter ∈ contract.parameterDomain,
        HasDerivAt
          (fun varied =>
            regularEinsteinHilbertDensityField period hPeriod couplings
              (line.data varied) point)
          (regularEinsteinHilbertMetricFirstVariationFieldAt period hPeriod
            couplings line parameter point)
          parameter :=
    Filter.Eventually.of_forall fun point parameter _ =>
      regularEinsteinHilbertDensityField_metricLine_hasDerivAt period hPeriod
        couplings line parameter point
  have hIntegral := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun parameter point =>
      regularEinsteinHilbertDensityField period hPeriod couplings
        (line.data parameter) point)
    (F' := fun parameter point =>
      regularEinsteinHilbertMetricFirstVariationFieldAt period hPeriod
        couplings line parameter point)
    (bound := contract.bound)
    contract.parameterDomain_mem_nhds hDensityMeasurable hDensityIntegrable
    hVariationMeasurable contract.derivative_norm_le
    contract.bound_integrable hPointwise
  unfold intrinsicEinsteinHilbertMetricActionCurve
    intrinsicEinsteinHilbertAction
    intrinsicEinsteinHilbertMetricFirstVariation
  exact hIntegral.2

/-- A genuine Maxwell line over a varying regular metric.  Its scalar pairing
is exactly the chartwise contraction of the derived curvature `F = dA`. -/
structure RegularIntrinsicMaxwellMetricGaugeLine
    (gravity : RegularEinsteinHilbertMetricLine period hPeriod) where
  potential : Real → SmoothAbelianGaugePotential period hPeriod
  pairing : Real → SmoothScalarField period hPeriod
  pairing_eq : ∀ parameter
      (patch : SmoothHolonomicFrameChart4 period hPeriod)
      (coordinate : Vector4),
    pairing parameter (patch.coordinateMap coordinate) =
      localMaxwellPairing period hPeriod
        (gravity.data parameter).metric.metric
        (potential parameter) (potential parameter) patch coordinate
  pairing_contDiff : ∀ point,
    ContDiff Real ∞ (fun parameter => pairing parameter point)
  pairingVelocity : Real → SmoothScalarField period hPeriod
  pairingVelocity_eq : ∀ parameter point,
    pairingVelocity parameter point =
      deriv (fun varied => pairing varied point) parameter

/-- Exact pointwise first variation of the Maxwell density when both metric
and gauge potential vary. -/
def regularMaxwellMetricGaugeFirstVariationFieldAt
    (gravity : RegularEinsteinHilbertMetricLine period hPeriod)
    (line : RegularIntrinsicMaxwellMetricGaugeLine period hPeriod gravity)
    (parameter : Real) : SmoothScalarField period hPeriod where
  toFun := fun point =>
    gravity.volumeVelocity parameter point *
        (-(1 / 4 : Real) * line.pairing parameter point) +
      (gravity.data parameter).metric.volume point *
        (-(1 / 4 : Real) * line.pairingVelocity parameter point)
  contMDiff_toFun :=
    (gravity.volumeVelocity parameter).contMDiff_toFun.mul
        (contMDiff_const.mul
          (line.pairing parameter).contMDiff_toFun) |>.add
      ((gravity.data parameter).metric.volume.contMDiff_toFun.mul
        (contMDiff_const.mul
          (line.pairingVelocity parameter).contMDiff_toFun))

theorem intrinsicMaxwellDensity_metricGaugeLine_hasDerivAt
    (gravity : RegularEinsteinHilbertMetricLine period hPeriod)
    (line : RegularIntrinsicMaxwellMetricGaugeLine period hPeriod gravity)
    (parameter : Real) (point : EffectiveQuotient period hPeriod) :
    HasDerivAt
      (fun varied =>
        (gravity.data varied).metric.volume point *
          (-(1 / 4 : Real) * line.pairing varied point))
      (regularMaxwellMetricGaugeFirstVariationFieldAt period hPeriod
        gravity line parameter point)
      parameter := by
  have hVolume : HasDerivAt
      (fun varied => (gravity.data varied).metric.volume point)
      (deriv
        (fun varied => (gravity.data varied).metric.volume point) parameter)
      parameter :=
    ((gravity.volume_contDiff point).differentiable (by simp))
      |>.differentiableAt.hasDerivAt
  have hPairing : HasDerivAt
      (fun varied => line.pairing varied point)
      (deriv (fun varied => line.pairing varied point) parameter)
      parameter :=
    ((line.pairing_contDiff point).differentiable (by simp))
      |>.differentiableAt.hasDerivAt
  change HasDerivAt
    (fun varied =>
      (gravity.data varied).metric.volume point *
        (-(1 / 4 : Real) * line.pairing varied point))
    (gravity.volumeVelocity parameter point *
        (-(1 / 4 : Real) * line.pairing parameter point) +
      (gravity.data parameter).metric.volume point *
        (-(1 / 4 : Real) * line.pairingVelocity parameter point))
    parameter
  rw [gravity.volumeVelocity_eq, line.pairingVelocity_eq]
  have hProduct :=
    hVolume.mul (hPairing.const_mul (-(1 / 4 : Real)))
  convert hProduct using 1 <;> rfl

def intrinsicMaxwellMetricGaugeActionCurve
    (gravity : RegularEinsteinHilbertMetricLine period hPeriod)
    (line : RegularIntrinsicMaxwellMetricGaugeLine period hPeriod gravity)
    (measure : Measure (EffectiveQuotient period hPeriod))
    (parameter : Real) : Real :=
  intrinsicMaxwellAction period hPeriod
    (gravity.data parameter).metric (line.pairing parameter) measure

def intrinsicMaxwellMetricGaugeFirstVariation
    (gravity : RegularEinsteinHilbertMetricLine period hPeriod)
    (line : RegularIntrinsicMaxwellMetricGaugeLine period hPeriod gravity)
    (measure : Measure (EffectiveQuotient period hPeriod)) : Real :=
  ∫ point,
    regularMaxwellMetricGaugeFirstVariationFieldAt period hPeriod
      gravity line 0 point ∂measure

structure DominatedMaxwellMetricGaugeVariation
    (gravity : RegularEinsteinHilbertMetricLine period hPeriod)
    (line : RegularIntrinsicMaxwellMetricGaugeLine period hPeriod gravity)
    (measure : Measure (EffectiveQuotient period hPeriod)) where
  parameterDomain : Set Real
  parameterDomain_mem_nhds : parameterDomain ∈ 𝓝 (0 : Real)
  bound : EffectiveQuotient period hPeriod → Real
  derivative_norm_le : ∀ᵐ point ∂measure,
    ∀ parameter ∈ parameterDomain,
      ‖regularMaxwellMetricGaugeFirstVariationFieldAt period hPeriod
        gravity line parameter point‖ ≤ bound point
  bound_integrable : Integrable bound measure

/-- Joint continuity on the compact parameter slab and mapping torus
automatically supplies the Maxwell domination contract. -/
noncomputable def dominatedMaxwellMetricGaugeVariation_of_jointContinuous
    (gravity : RegularEinsteinHilbertMetricLine period hPeriod)
    (line : RegularIntrinsicMaxwellMetricGaugeLine period hPeriod gravity)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (hJoint : Continuous
      (fun input : Real × EffectiveQuotient period hPeriod =>
        regularMaxwellMetricGaugeFirstVariationFieldAt period hPeriod
          gravity line input.1 input.2)) :
    DominatedMaxwellMetricGaugeVariation period hPeriod
      gravity line measure := by
  have hCompact : IsCompact
      (Set.Icc (-1 : Real) 1 ×ˢ
        (Set.univ : Set (EffectiveQuotient period hPeriod))) :=
    isCompact_Icc.prod isCompact_univ
  let hBounded := hCompact.bddAbove_image hJoint.norm.continuousOn
  let bound : Real := Classical.choose hBounded
  have hBound := Classical.choose_spec hBounded
  exact
    { parameterDomain := Set.Icc (-1 : Real) 1
      parameterDomain_mem_nhds :=
        Icc_mem_nhds (by norm_num : (-1 : Real) < 0)
          (by norm_num : (0 : Real) < 1)
      bound := fun _ => bound
      derivative_norm_le := by
        filter_upwards with point
        intro parameter hParameter
        exact hBound (Set.mem_image_of_mem _
          (Set.mk_mem_prod hParameter (Set.mem_univ point)))
      bound_integrable := integrable_const bound }

/-- The varying-metric Maxwell action differentiates to its actual density
derivative under the sole domination contract. -/
theorem intrinsicMaxwellMetricGaugeActionCurve_hasDerivAt
    (gravity : RegularEinsteinHilbertMetricLine period hPeriod)
    (line : RegularIntrinsicMaxwellMetricGaugeLine period hPeriod gravity)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (contract : DominatedMaxwellMetricGaugeVariation period hPeriod
      gravity line measure) :
    HasDerivAt
      (intrinsicMaxwellMetricGaugeActionCurve period hPeriod
        gravity line measure)
      (intrinsicMaxwellMetricGaugeFirstVariation period hPeriod
        gravity line measure)
      0 := by
  have hDensityMeasurable : ∀ᶠ parameter in 𝓝 (0 : Real),
      AEStronglyMeasurable
        (fun point =>
          (gravity.data parameter).metric.volume point *
            (-(1 / 4 : Real) * line.pairing parameter point))
        measure :=
    Filter.Eventually.of_forall fun parameter =>
      ((gravity.data parameter).metric.volume.contMDiff_toFun.mul
        (contMDiff_const.mul
          (line.pairing parameter).contMDiff_toFun)).continuous
            |>.aestronglyMeasurable
  have hDensityIntegrable :
      Integrable
        (fun point =>
          (gravity.data 0).metric.volume point *
            (-(1 / 4 : Real) * line.pairing 0 point))
        measure :=
    (((gravity.data 0).metric.volume.contMDiff_toFun.mul
      (contMDiff_const.mul
        (line.pairing 0).contMDiff_toFun)).continuous)
          |>.integrable_of_hasCompactSupport
            (HasCompactSupport.of_compactSpace _)
  have hVariationMeasurable :
      AEStronglyMeasurable
        (regularMaxwellMetricGaugeFirstVariationFieldAt period hPeriod
          gravity line 0)
        measure :=
    (regularMaxwellMetricGaugeFirstVariationFieldAt period hPeriod
      gravity line 0).contMDiff_toFun.continuous.aestronglyMeasurable
  have hPointwise : ∀ᵐ point ∂measure,
      ∀ parameter ∈ contract.parameterDomain,
        HasDerivAt
          (fun varied =>
            (gravity.data varied).metric.volume point *
              (-(1 / 4 : Real) * line.pairing varied point))
          (regularMaxwellMetricGaugeFirstVariationFieldAt period hPeriod
            gravity line parameter point)
          parameter :=
    Filter.Eventually.of_forall fun point parameter _ =>
      intrinsicMaxwellDensity_metricGaugeLine_hasDerivAt period hPeriod
        gravity line parameter point
  have hIntegral := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun parameter point =>
      (gravity.data parameter).metric.volume point *
        (-(1 / 4 : Real) * line.pairing parameter point))
    (F' := fun parameter point =>
      regularMaxwellMetricGaugeFirstVariationFieldAt period hPeriod
        gravity line parameter point)
    (bound := contract.bound)
    contract.parameterDomain_mem_nhds hDensityMeasurable hDensityIntegrable
    hVariationMeasurable contract.derivative_norm_le
    contract.bound_integrable hPointwise
  unfold intrinsicMaxwellMetricGaugeActionCurve intrinsicMaxwellAction
    intrinsicMaxwellMetricGaugeFirstVariation
  exact hIntegral.2

end

end P0EFTJanusMappingTorusIntrinsicEinsteinMaxwellMetricVariation4D
end JanusFormal
