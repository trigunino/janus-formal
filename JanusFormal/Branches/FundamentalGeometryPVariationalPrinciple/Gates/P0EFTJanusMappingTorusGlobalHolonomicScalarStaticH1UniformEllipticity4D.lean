import Mathlib.MeasureTheory.Function.L2Space
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGlobalHolonomicScalarStaticH1GraphBridge4D

/-!
# Uniform ellipticity reduction for the static scalar H¹ bridge

Compactness and positivity give uniform positive lower bounds for the metric
volume and inverse diagonal magnitudes.  They do not by themselves compare
the arbitrary finite smooth tangent generators used by graph H¹ with the
fixed holonomic directions used by the action.  The latter comparison is
isolated below as a pointwise uniform ellipticity contract.  From precisely
that contract, the global norm estimate and the continuous bridge follow.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusGlobalHolonomicScalarStaticH1UniformEllipticity4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff Topology ENNReal InnerProductSpace
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
open P0EFTJanusMappingTorusGlobalHolonomicScalar4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarAction4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarVariation4D
open P0EFTJanusMappingTorusAutomaticScalarIntegrability4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarWeakJacobiRiesz4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarStaticH1GraphBridge4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

/-- Compactness upgrades the pointwise-positive metric volume to a uniform
positive lower bound. -/
theorem exists_uniform_volume_lower
    (data : PositiveStaticGlobalScalarData period hPeriod) :
    ∃ lower : Real, 0 < lower ∧ ∀ point,
      lower ≤ diagonalMetricVolumeDensity period hPeriod
        data.formData.magnitude point := by
  have hContinuous := diagonalMetricVolumeDensity_continuous period hPeriod
    data.formData.magnitude
  rcases isCompact_univ.exists_forall_le' hContinuous.continuousOn
      (fun point _ => diagonalMetricVolumeDensity_pos period hPeriod data point) with
    ⟨lower, hLower, hBound⟩
  exact ⟨lower, hLower, fun point => hBound point (Set.mem_univ point)⟩

/-- Each positive inverse diagonal magnitude has a uniform positive lower
bound on the compact quotient. -/
theorem exists_uniform_inverse_magnitude_lower
    (data : PositiveStaticGlobalScalarData period hPeriod)
    (index : Fin 4) :
    ∃ lower : Real, 0 < lower ∧ ∀ point,
      lower ≤ 1 / data.formData.magnitude point index := by
  have hContinuous : Continuous
      (fun point : EffectiveQuotient period hPeriod =>
        1 / data.formData.magnitude point index) :=
    continuous_const.div
      ((continuous_apply index).comp
        data.formData.magnitude.contMDiff_toFun.continuous)
      (fun point => ne_of_gt (data.magnitude_pos point index))
  rcases isCompact_univ.exists_forall_le' hContinuous.continuousOn
      (fun point _ => one_div_pos.mpr (data.magnitude_pos point index)) with
    ⟨lower, hLower, hBound⟩
  exact ⟨lower, hLower, fun point => hBound point (Set.mem_univ point)⟩

/-- Consequently, every positive spatial kinetic coefficient has a uniform
positive lower bound. -/
theorem exists_uniform_spatial_kinetic_lower
    (data : PositiveStaticGlobalScalarData period hPeriod)
    (index : Fin 4) :
    ∃ lower : Real, 0 < lower ∧ ∀ point,
      lower ≤ diagonalMetricVolumeDensity period hPeriod
        data.formData.magnitude point *
          (1 / data.formData.magnitude point index) := by
  rcases exists_uniform_volume_lower period hPeriod data with
    ⟨volumeLower, hVolumeLower, hVolume⟩
  rcases exists_uniform_inverse_magnitude_lower period hPeriod data index with
    ⟨inverseLower, hInverseLower, hInverse⟩
  refine ⟨volumeLower * inverseLower, mul_pos hVolumeLower hInverseLower, ?_⟩
  intro point
  exact mul_le_mul (hVolume point) (hInverse point) hInverseLower.le
    (diagonalMetricVolumeDensity_pos period hPeriod data point).le

/-- The positive mass coefficient is uniformly coercive as well. -/
theorem exists_uniform_mass_lower
    (data : PositiveStaticGlobalScalarData period hPeriod) :
    ∃ lower : Real, 0 < lower ∧ ∀ point,
      lower ≤ diagonalMetricVolumeDensity period hPeriod
        data.formData.magnitude point * data.formData.massSquared := by
  rcases exists_uniform_volume_lower period hPeriod data with
    ⟨volumeLower, hVolumeLower, hVolume⟩
  refine ⟨volumeLower * data.formData.massSquared,
    mul_pos hVolumeLower data.massSquared_pos, ?_⟩
  intro point
  exact mul_le_mul_of_nonneg_right (hVolume point) data.massSquared_pos.le

/-- Pointwise positive Jacobi density in the static sector. -/
theorem staticScalarJacobiDensity_nonneg
    (data : PositiveStaticGlobalScalarData period hPeriod)
    (field : StaticGlobalScalarTest period hPeriod data)
    (point : EffectiveQuotient period hPeriod) :
    0 ≤ globalHolonomicScalarJacobiDensity period hPeriod
      data.formData.massSquared data.formData.magnitude
      field.toField field.toField point :=
  (staticScalarMassDensity_nonneg period hPeriod data field point).trans
    (staticScalarMassDensity_le_jacobi period hPeriod data field point)

/-- Square root of the nonnegative static Jacobi density. -/
def staticScalarJacobiDensityRoot
    (data : PositiveStaticGlobalScalarData period hPeriod)
    (field : StaticGlobalScalarTest period hPeriod data)
    (point : EffectiveQuotient period hPeriod) : Real :=
  Real.sqrt (globalHolonomicScalarJacobiDensity period hPeriod
    data.formData.massSquared data.formData.magnitude
    field.toField field.toField point)

theorem staticScalarJacobiDensityRoot_memLp
    (data : PositiveStaticGlobalScalarData period hPeriod)
    (field : StaticGlobalScalarTest period hPeriod data) :
    MemLp (staticScalarJacobiDensityRoot period hPeriod data field)
      (2 : ENNReal) data.formData.measure := by
  have hDensityIntegrable := data.formData.pair_integrable
    field.toField field.toField
  have hMeasurable : AEStronglyMeasurable
      (staticScalarJacobiDensityRoot period hPeriod data field)
      data.formData.measure :=
    Real.continuous_sqrt.comp_aestronglyMeasurable
      hDensityIntegrable.aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq hMeasurable]
  exact hDensityIntegrable.congr (Filter.Eventually.of_forall fun point => by
    symm
    exact Real.sq_sqrt
      (staticScalarJacobiDensity_nonneg period hPeriod data field point))

/-- The Jacobi-density square root as an actual `L2` vector. -/
def staticScalarJacobiDensityRootToL2
    (data : PositiveStaticGlobalScalarData period hPeriod)
    (field : StaticGlobalScalarTest period hPeriod data) :
    Lp Real (2 : ENNReal) data.formData.measure :=
  (staticScalarJacobiDensityRoot_memLp period hPeriod data field).toLp
    (staticScalarJacobiDensityRoot period hPeriod data field)

/-- Its `L2` norm is exactly the energy norm on the common smooth core. -/
theorem staticScalarJacobiDensityRootToL2_norm_eq_energy
    (data : PositiveStaticGlobalScalarData period hPeriod)
    (field : StaticGlobalScalarTest period hPeriod data) :
    ‖staticScalarJacobiDensityRootToL2 period hPeriod data field‖ =
      ‖staticScalarEnergyEmbedding period hPeriod data field‖ := by
  let root := staticScalarJacobiDensityRootToL2 period hPeriod data field
  have hRootSquared :
      ‖root‖ ^ 2 = globalHolonomicScalarJacobiForm period hPeriod
        data.formData field.toField field.toField := by
    rw [← real_inner_self_eq_norm_sq root, L2.inner_def]
    unfold globalHolonomicScalarJacobiForm
    apply integral_congr_ae
    filter_upwards
      [(staticScalarJacobiDensityRoot_memLp period hPeriod data field).coeFn_toLp]
      with point hPoint
    change inner Real
      ((staticScalarJacobiDensityRootToL2 period hPeriod data field) point)
      ((staticScalarJacobiDensityRootToL2 period hPeriod data field) point) = _
    have hPoint' :
        (staticScalarJacobiDensityRootToL2 period hPeriod data field :
          EffectiveQuotient period hPeriod → Real) point =
            staticScalarJacobiDensityRoot period hPeriod data field point := by
      simpa only [staticScalarJacobiDensityRootToL2] using hPoint
    rw [hPoint', real_inner_self_eq_norm_sq]
    unfold staticScalarJacobiDensityRoot
    simp only [Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sq_sqrt
      (staticScalarJacobiDensity_nonneg period hPeriod data field point)
  have hEnergySquared :
      ‖staticScalarEnergyEmbedding period hPeriod data field‖ ^ 2 =
        globalHolonomicScalarJacobiForm period hPeriod
          data.formData field.toField field.toField := by
    calc
      ‖staticScalarEnergyEmbedding period hPeriod data field‖ ^ 2 =
          ‖field‖ ^ 2 := by
            simp [staticScalarEnergyEmbedding]
      _ = inner Real field field :=
        (real_inner_self_eq_norm_sq field).symm
      _ = globalHolonomicScalarJacobiForm period hPeriod
          data.formData field.toField field.toField := rfl
  dsimp only [root] at hRootSquared ⊢
  nlinarith [norm_nonneg
    (staticScalarJacobiDensityRootToL2 period hPeriod data field),
    norm_nonneg (staticScalarEnergyEmbedding period hPeriod data field)]

/-- Minimal missing uniform ellipticity datum.  It compares the actual smooth
first jet used by graph H¹ to the square root of the already-defined positive
Jacobi density, pointwise and with one field-independent constant. -/
structure StaticScalarUniformGraphEllipticity
    (data : PositiveStaticGlobalScalarData period hPeriod)
    (frame : SmoothD8Frame period hPeriod) where
  constant : Real
  constant_nonneg : 0 ≤ constant
  pointwise_bound :
    ∀ (field : StaticGlobalScalarTest period hPeriod data) point,
      ‖smoothFirstJet period hPeriod Real frame field.toField point‖ ≤
        constant * staticScalarJacobiDensityRoot period hPeriod data field point

/-- Pointwise uniform ellipticity gives the corresponding `L2` estimate. -/
theorem smoothFirstJetToL2_norm_le_energyRoot
    (data : PositiveStaticGlobalScalarData period hPeriod)
    (frame : SmoothD8Frame period hPeriod)
    (ellipticity : StaticScalarUniformGraphEllipticity period hPeriod data frame)
    (field : StaticGlobalScalarTest period hPeriod data) :
    let _ : IsFiniteMeasure data.formData.measure := data.finiteMeasure
    ‖smoothFirstJetToL2 period hPeriod Real frame data.formData.measure
      field.toField‖ ≤
      ellipticity.constant *
        ‖staticScalarJacobiDensityRootToL2 period hPeriod data field‖ := by
  letI : IsFiniteMeasure data.formData.measure := data.finiteMeasure
  let jet := smoothFirstJet period hPeriod Real frame field.toField
  let root := staticScalarJacobiDensityRoot period hPeriod data field
  have hELp :
      eLpNorm jet (2 : ENNReal) data.formData.measure ≤
        ‖ellipticity.constant‖ₑ *
          eLpNorm root (2 : ENNReal) data.formData.measure := by
    calc
      eLpNorm jet (2 : ENNReal) data.formData.measure ≤
          eLpNorm (ellipticity.constant • root) (2 : ENNReal)
            data.formData.measure := by
        apply eLpNorm_mono_ae
        exact Filter.Eventually.of_forall fun point => by
          simpa [jet, root, Pi.smul_apply, Real.norm_eq_abs,
            staticScalarJacobiDensityRoot,
            abs_of_nonneg ellipticity.constant_nonneg,
            abs_of_nonneg (Real.sqrt_nonneg _)] using
              ellipticity.pointwise_bound field point
      _ = ‖ellipticity.constant‖ₑ *
          eLpNorm root (2 : ENNReal) data.formData.measure :=
        eLpNorm_const_smul ellipticity.constant root
          (2 : ENNReal) data.formData.measure
  have hRightFinite :
      ‖ellipticity.constant‖ₑ *
          eLpNorm root (2 : ENNReal) data.formData.measure ≠ (∞ : ENNReal) :=
    ENNReal.mul_ne_top (by simp)
      (staticScalarJacobiDensityRoot_memLp period hPeriod data field).2.ne
  have hReal := ENNReal.toReal_mono hRightFinite hELp
  simpa [jet, root, smoothFirstJetToL2,
    staticScalarJacobiDensityRootToL2, Lp.norm_toLp,
    Real.norm_eq_abs, abs_of_nonneg ellipticity.constant_nonneg] using hReal

/-- The pointwise contract discharges the raw global bridge bound. -/
theorem uniformGraphEllipticity_energyToH1GraphBound
    (data : PositiveStaticGlobalScalarData period hPeriod)
    (frame : SmoothD8Frame period hPeriod)
    (ellipticity : StaticScalarUniformGraphEllipticity period hPeriod data frame) :
    StaticScalarEnergyToH1GraphBound period hPeriod data frame := by
  refine ⟨ellipticity.constant, ?_⟩
  intro field
  have hL2 := smoothFirstJetToL2_norm_le_energyRoot period hPeriod data frame
    ellipticity field
  rw [staticScalarJacobiDensityRootToL2_norm_eq_energy period hPeriod data field]
    at hL2
  simpa [staticScalarSmoothToH1GraphClosureLinearMap,
    staticScalarSmoothToH1GraphLinearMap, smoothToH1GraphLinearMap,
    smoothFirstJetL2LinearMap] using hL2

/-- Continuous energy-to-graph bridge with the raw norm hypothesis eliminated
in favor of pointwise uniform ellipticity. -/
def staticScalarEnergyToH1GraphClosureOfUniformEllipticity
    (data : PositiveStaticGlobalScalarData period hPeriod)
    (frame : SmoothD8Frame period hPeriod)
    (ellipticity : StaticScalarUniformGraphEllipticity period hPeriod data frame) :
    StaticScalarEnergyH1 period hPeriod data →L[Real]
      StaticScalarH1GraphClosure period hPeriod data frame :=
  staticScalarEnergyToH1GraphClosure period hPeriod data frame
    (uniformGraphEllipticity_energyToH1GraphBound period hPeriod data frame
      ellipticity)

theorem staticScalarEnergyToH1GraphClosureOfUniformEllipticity_agrees_on_smooth
    (data : PositiveStaticGlobalScalarData period hPeriod)
    (frame : SmoothD8Frame period hPeriod)
    (ellipticity : StaticScalarUniformGraphEllipticity period hPeriod data frame)
    (field : StaticGlobalScalarTest period hPeriod data) :
    staticScalarEnergyToH1GraphClosureOfUniformEllipticity period hPeriod data frame
        ellipticity (staticScalarEnergyEmbedding period hPeriod data field) =
      staticScalarSmoothToH1GraphClosureLinearMap period hPeriod data frame field :=
  staticScalarEnergyToH1GraphClosure_agrees_on_smooth period hPeriod data frame
    (uniformGraphEllipticity_energyToH1GraphBound period hPeriod data frame
      ellipticity) field

end

end P0EFTJanusMappingTorusGlobalHolonomicScalarStaticH1UniformEllipticity4D
end JanusFormal
