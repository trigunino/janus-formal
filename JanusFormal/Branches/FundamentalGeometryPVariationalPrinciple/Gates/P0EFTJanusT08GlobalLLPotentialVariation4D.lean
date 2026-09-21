import Mathlib
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGlobalLLVariation4D

/-!
# T08: integrated measure-field potentials on the actual LL throat

Continuous-function integration is bounded linear on a compact space. This
gives an actual derivative of integrated power potentials, without assuming
an interchange of differentiation and integration. The result is instantiated
on the existing smooth global LL fields and their simultaneous affine curves.
The added potential changes the measure multiplier equation; invariance of
the selected old equation is not postulated as a selection principle.
-/

namespace JanusFormal
namespace P0EFTJanusT08GlobalLLPotentialVariation4D

set_option autoImplicit false
noncomputable section

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

open MeasureTheory
open scoped Topology

section CompactIntegral
variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] (mu : Measure X) [IsFiniteMeasure mu]

private theorem continuous_integrable (f : C(X, Real)) : Integrable f mu :=
  f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

/-- Integration in the uniform norm; this supplies the needed analytic
justification before any derivative is passed through the integral. -/
def continuousIntegral : C(X, Real) →L[Real] Real :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ x, f x ∂mu
      map_add' := by
        intro f g
        exact integral_add (continuous_integrable mu f) (continuous_integrable mu g)
      map_smul' := by
        intro c f
        exact integral_smul c f }
    (mu.real Set.univ) (fun f => by
      change ‖∫ x, f x ∂mu‖ ≤ mu.real Set.univ * ‖f‖
      simpa only [BoundedContinuousFunction.mkOfCompact_apply,
        BoundedContinuousFunction.norm_mkOfCompact] using
        BoundedContinuousFunction.norm_integral_le_mul_norm mu
          (BoundedContinuousFunction.mkOfCompact f))

theorem integral_power_affine_hasDerivAt (field direction : C(X, Real)) (degree : Nat) :
    HasDerivAt (fun t : Real => ∫ x, (field x + t * direction x) ^ degree ∂mu)
      (∫ x, (degree : Real) * field x ^ (degree - 1) * direction x ∂mu) 0 := by
  have hCurve : HasDerivAt (fun t : Real => field + t • direction) direction 0 := by
    simpa using ((hasDerivAt_id (0 : Real)).smul_const direction).const_add field
  have hPower := hCurve.pow degree
  have hIntegral := (continuousIntegral mu).hasFDerivAt.comp_hasDerivAt 0 hPower
  simpa [Function.comp_def, continuousIntegral, ContinuousMap.pow_apply,
    nsmul_eq_mul, mul_assoc] using hIntegral

end CompactIntegral

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusGlobalLLWorldvolume4D
open P0EFTJanusMappingTorusGlobalLLVariation4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev Throat := MappingTorus (fixedEquatorData period hPeriod)

local instance : ChartedSpace ThroatCoverModel (Throat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω (Throat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod
local instance : CompactSpace (Throat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (Throat period hPeriod) := borel _
local instance : BorelSpace (Throat period hPeriod) where measurable_eq := rfl
local instance realNormedModule : Module Real Real := NormedField.toNormedSpace.toModule

def powerPotentialDensity (coupling reference : Real) (degree : Nat)
    (fields : IndependentFields period hPeriod) (point : Throat period hPeriod) : Real :=
  coupling * (fields.llMeasure point - reference) ^ degree

def globalLLPowerAction (coupling reference : Real) (degree : Nat)
    (fields : IndependentFields period hPeriod) (mu : Measure (Throat period hPeriod)) : Real :=
  globalLLAction period hPeriod fields mu +
    ∫ point, powerPotentialDensity period hPeriod coupling reference degree fields point ∂mu

theorem powerPotentialDensity_integrable (coupling reference : Real) (degree : Nat)
    (fields : IndependentFields period hPeriod) (mu : Measure (Throat period hPeriod))
    [IsFiniteMeasure mu] :
    Integrable (powerPotentialDensity period hPeriod coupling reference degree fields) mu := by
  apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
  exact continuous_const.mul ((fields.llMeasure.contMDiff_toFun.continuous.sub continuous_const).pow degree)

theorem globalLLPowerAction_eq_integral (coupling reference : Real) (degree : Nat)
    (fields : IndependentFields period hPeriod) (mu : Measure (Throat period hPeriod))
    [IsFiniteMeasure mu] :
    globalLLPowerAction period hPeriod coupling reference degree fields mu =
      ∫ point, llWorldvolumeDensity period hPeriod fields point +
        powerPotentialDensity period hPeriod coupling reference degree fields point ∂mu := by
  exact (integral_add (llWorldvolumeDensity_integrable period hPeriod fields mu)
    (powerPotentialDensity_integrable period hPeriod coupling reference degree fields mu)).symm

def powerMeasureEuler (coupling reference : Real) (degree : Nat)
    (fields : IndependentFields period hPeriod) (point : Throat period hPeriod) : Real :=
  llMeasureEuler period hPeriod fields point +
    coupling * degree * (fields.llMeasure point - reference) ^ (degree - 1)

/-- The independent flux Euler vector is unchanged; only the multiplier's
coefficient acquires U'(chi). Both fields are varied in the same curve. -/
theorem globalLLPowerAction_affine_hasDerivAt (coupling reference : Real) (degree : Nat)
    (fields : IndependentFields period hPeriod) (variation : LLVariation period hPeriod)
    (mu : Measure (Throat period hPeriod)) [IsFiniteMeasure mu] :
    HasDerivAt
      (fun t : Real => globalLLPowerAction period hPeriod coupling reference degree
        (llAffineCurve period hPeriod fields variation t) mu)
      (∫ point, variation.measureDirection point *
          powerMeasureEuler period hPeriod coupling reference degree fields point +
        inner Real (llFieldEuler period hPeriod fields point) (variation.fieldDirection point) ∂mu) 0 := by
  let field : C(Throat period hPeriod, Real) :=
    ⟨fun point => fields.llMeasure point - reference,
      fields.llMeasure.contMDiff_toFun.continuous.sub continuous_const⟩
  let direction : C(Throat period hPeriod, Real) :=
    ⟨variation.measureDirection, variation.measureDirection.contMDiff_toFun.continuous⟩
  have hPower := (integral_power_affine_hasDerivAt mu field direction degree).const_mul coupling
  have hOriginal := globalLLAction_affine_hasDerivAt period hPeriod fields variation mu
  have hTotal := hOriginal.fun_add hPower
  convert hTotal using 1
  · ext t
    simp only [globalLLPowerAction, powerPotentialDensity, llAffineCurve]
    rw [← integral_const_mul]
    congr 1
    apply integral_congr_ae
    filter_upwards [] with point
    change coupling * (fields.llMeasure point + t * variation.measureDirection point - reference) ^ degree =
      coupling * ((fields.llMeasure point - reference) + t * variation.measureDirection point) ^ degree
    ring
  · have hIntegrable : Integrable
        (fun point => (degree : Real) * (fields.llMeasure point - reference) ^ (degree - 1) *
          variation.measureDirection point) mu := by
      apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
      exact (continuous_const.mul
        ((fields.llMeasure.contMDiff_toFun.continuous.sub continuous_const).pow _)).mul
        variation.measureDirection.contMDiff_toFun.continuous
    simp only [field, direction, ContinuousMap.coe_mk]
    rw [globalLLFirstVariation, ← integral_const_mul,
      ← integral_add (llFirstVariationDensity_continuous period hPeriod fields variation
        |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
        (hIntegrable.const_mul coupling)]
    apply integral_congr_ae
    filter_upwards [] with point
    rw [llFirstVariationDensity_eq_euler_pairing]
    dsimp [powerMeasureEuler, field, direction]
    ring

/-- On the nonzero-measure branch the actual flux equation still forces
zero flux, while a nonconstant power potential fixes the scalar reference.
This is a pointwise equation classification, not a fundamental-lemma claim
for arbitrary (possibly zero) integration measures. -/
theorem regular_power_stationary_iff (coupling reference : Real) (degree : Nat)
    (hCoupling : coupling ≠ 0) (hDegree : 2 ≤ degree)
    (fields : IndependentFields period hPeriod) (point : Throat period hPeriod)
    (hMeasure : fields.llMeasure point ≠ 0) :
    (powerMeasureEuler period hPeriod coupling reference degree fields point = 0 ∧
      llFieldEuler period hPeriod fields point = 0) ↔
      fields.llField point = 0 ∧ fields.llMeasure point = reference := by
  have hNat : degree ≠ 0 := by omega
  have hPower : degree - 1 ≠ 0 := by omega
  have hCoefficient : coupling * (degree : Real) ≠ 0 :=
    mul_ne_zero hCoupling (Nat.cast_ne_zero.mpr hNat)
  constructor
  · rintro ⟨hScalar, hFlux⟩
    have hField : fields.llField point = 0 :=
      (smul_eq_zero.mp hFlux).resolve_left (mul_ne_zero (by norm_num) hMeasure)
    have hProduct : (coupling * (degree : Real)) *
        (fields.llMeasure point - reference) ^ (degree - 1) = 0 := by
      simpa [powerMeasureEuler, llMeasureEuler, hField] using hScalar
    have hZero := (mul_eq_zero.mp hProduct).resolve_left hCoefficient
    exact ⟨hField, sub_eq_zero.mp (eq_zero_of_pow_eq_zero hZero)⟩
  · rintro ⟨hField, hReference⟩
    simp [powerMeasureEuler, llMeasureEuler, llFieldEuler, hField, hReference, hPower]

end
end P0EFTJanusT08GlobalLLPotentialVariation4D
end JanusFormal
