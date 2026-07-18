import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarRobinJunctionL2Fredholm4D

/-!
# PT covariance of the scalar Robin junction model

The actual throat PT involution pulls back the junction field and exchanges
the two bulk sectors.  Exchanging `kPlus` and `kMinus` at the same time makes
the Robin traces, flux balance, density, action, first variation and Hessian
exactly covariant.  Integrated statements use an explicitly PT-invariant
Borel measure.  The genuine throat `L2` pullback also intertwines the bounded
Hessian operators.

No averaged or modified action is introduced.  PT invariance of the measure
is an explicit analytic input; no canonical throat volume form, geometric
normal derivative, Israel condition, or null junction is supplied here.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarRobinJunctionPTCovariance4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff ENNReal InnerProduct
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusPTInvolution
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothPTInvolution
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothPTFieldAction4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusScalarRobinJunctionBalance4D
open P0EFTJanusMappingTorusScalarRobinJunctionHessian4D
open P0EFTJanusMappingTorusScalarRobinJunctionL2Fredholm4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev throatData := fixedEquatorData period hPeriod
private abbrev EffectiveThroat := MappingTorus (throatData period hPeriod)

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance effectiveThroatCompactSpace :
    CompactSpace (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod

local instance effectiveThroatMeasurableSpace :
    MeasurableSpace (EffectiveThroat period hPeriod) := borel _

local instance effectiveThroatBorelSpace :
    BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

/-- The measurable equivalence underlying the actual smooth throat PT map. -/
def robinThroatPTMeasurableEquiv :
    EffectiveThroat period hPeriod ≃ᵐ EffectiveThroat period hPeriod where
  toEquiv :=
    { toFun := fixedThroatPT period hPeriod
      invFun := fixedThroatPT period hPeriod
      left_inv := fixedThroatPT_involutive period hPeriod
      right_inv := fixedThroatPT_involutive period hPeriod }
  measurable_toFun := (continuous_fixedThroatPT period hPeriod).measurable
  measurable_invFun := (continuous_fixedThroatPT period hPeriod).measurable

/-- Ordered plus/minus smooth bulk scalars. -/
abbrev RobinBulkFields :=
  SmoothQuotientField period hPeriod Real ×
    SmoothQuotientField period hPeriod Real

/-- PT pullback together with exchange of the plus and minus sectors. -/
def robinBulkPT (fields : RobinBulkFields period hPeriod) :
    RobinBulkFields period hPeriod :=
  sectorExchange period hPeriod Real fields

@[simp]
theorem robinBulkPT_plus (fields : RobinBulkFields period hPeriod) :
    (robinBulkPT period hPeriod fields).1 =
      ptPullback period hPeriod Real fields.2 :=
  rfl

@[simp]
theorem robinBulkPT_minus (fields : RobinBulkFields period hPeriod) :
    (robinBulkPT period hPeriod fields).2 =
      ptPullback period hPeriod Real fields.1 :=
  rfl

@[simp]
theorem robinBulkPT_involutive (fields : RobinBulkFields period hPeriod) :
    robinBulkPT period hPeriod (robinBulkPT period hPeriod fields) = fields :=
  sectorExchange_involutive period hPeriod Real fields

/-- PT pullback of a smooth junction or test field on the actual throat. -/
def robinThroatPT
    (field : SmoothThroatField period hPeriod Real) :
    SmoothThroatField period hPeriod Real :=
  throatPTPullback period hPeriod Real field

@[simp]
theorem robinThroatPT_involutive
    (field : SmoothThroatField period hPeriod Real) :
    robinThroatPT period hPeriod (robinThroatPT period hPeriod field) = field :=
  throatPTPullback_involutive period hPeriod Real field

/-- The transformed plus trace is the PT pullback of the old minus trace. -/
theorem robinBulkPT_trace_plus
    (fields : RobinBulkFields period hPeriod) :
    throatTrace period hPeriod Real (robinBulkPT period hPeriod fields).1 =
      robinThroatPT period hPeriod
        (throatTrace period hPeriod Real fields.2) := by
  exact throatTrace_pt_equivariant period hPeriod Real fields.2

/-- The transformed minus trace is the PT pullback of the old plus trace. -/
theorem robinBulkPT_trace_minus
    (fields : RobinBulkFields period hPeriod) :
    throatTrace period hPeriod Real (robinBulkPT period hPeriod fields).2 =
      robinThroatPT period hPeriod
        (throatTrace period hPeriod Real fields.1) := by
  exact throatTrace_pt_equivariant period hPeriod Real fields.1

/-- The plus constitutive flux transforms into the old minus flux. -/
theorem robinFluxPlus_pt
    (kMinus : Real)
    (fields : RobinBulkFields period hPeriod)
    (junction : SmoothThroatField period hPeriod Real)
    (point : EffectiveThroat period hPeriod) :
    robinFluxPlus period hPeriod kMinus (robinBulkPT period hPeriod fields).1
        (robinThroatPT period hPeriod junction) point =
      robinFluxMinus period hPeriod kMinus fields.2 junction
        (fixedThroatPT period hPeriod point) := by
  unfold robinFluxPlus robinFluxMinus
  rw [robinBulkPT_trace_plus period hPeriod]
  rfl

/-- The minus constitutive flux transforms into the old plus flux. -/
theorem robinFluxMinus_pt
    (kPlus : Real)
    (fields : RobinBulkFields period hPeriod)
    (junction : SmoothThroatField period hPeriod Real)
    (point : EffectiveThroat period hPeriod) :
    robinFluxMinus period hPeriod kPlus (robinBulkPT period hPeriod fields).2
        (robinThroatPT period hPeriod junction) point =
      robinFluxPlus period hPeriod kPlus fields.1 junction
        (fixedThroatPT period hPeriod point) := by
  unfold robinFluxPlus robinFluxMinus
  rw [robinBulkPT_trace_minus period hPeriod]
  rfl

/-- Exchanging sectors and couplings makes the balance residual a scalar under PT. -/
theorem junctionResidual_pt
    (kPlus kMinus : Real)
    (fields : RobinBulkFields period hPeriod)
    (junction : SmoothThroatField period hPeriod Real)
    (point : EffectiveThroat period hPeriod) :
    junctionResidual period hPeriod kMinus kPlus
        (robinBulkPT period hPeriod fields).1
        (robinBulkPT period hPeriod fields).2
        (robinThroatPT period hPeriod junction) point =
      junctionResidual period hPeriod kPlus kMinus
        fields.1 fields.2 junction (fixedThroatPT period hPeriod point) := by
  unfold junctionResidual
  change
    robinFluxPlus period hPeriod kMinus (robinBulkPT period hPeriod fields).1
          (robinThroatPT period hPeriod junction) point +
        robinFluxMinus period hPeriod kPlus (robinBulkPT period hPeriod fields).2
          (robinThroatPT period hPeriod junction) point =
      robinFluxPlus period hPeriod kPlus fields.1 junction
          (fixedThroatPT period hPeriod point) +
        robinFluxMinus period hPeriod kMinus fields.2 junction
          (fixedThroatPT period hPeriod point)
  rw [robinFluxPlus_pt period hPeriod, robinFluxMinus_pt period hPeriod]
  exact add_comm _ _

/-- Pointwise Robin energy density covariance with sector/coupling exchange. -/
theorem robinJunctionDensity_pt
    (kPlus kMinus : Real)
    (fields : RobinBulkFields period hPeriod)
    (junction : SmoothThroatField period hPeriod Real)
    (point : EffectiveThroat period hPeriod) :
    robinJunctionDensity period hPeriod kMinus kPlus
        (robinBulkPT period hPeriod fields).1
        (robinBulkPT period hPeriod fields).2
        (robinThroatPT period hPeriod junction) point =
      robinJunctionDensity period hPeriod kPlus kMinus
        fields.1 fields.2 junction (fixedThroatPT period hPeriod point) := by
  unfold robinJunctionDensity
  rw [robinBulkPT_trace_plus period hPeriod,
    robinBulkPT_trace_minus period hPeriod]
  change
    kMinus / 2 *
          (junction (fixedThroatPT period hPeriod point) -
            throatTrace period hPeriod Real fields.2
              (fixedThroatPT period hPeriod point)) ^ 2 +
        kPlus / 2 *
          (junction (fixedThroatPT period hPeriod point) -
            throatTrace period hPeriod Real fields.1
              (fixedThroatPT period hPeriod point)) ^ 2 = _
  ring

/-- A PT-invariant throat measure makes the exchanged Robin action invariant. -/
theorem robinJunctionAction_pt
    (kPlus kMinus : Real)
    (fields : RobinBulkFields period hPeriod)
    (junction : SmoothThroatField period hPeriod Real)
    (mu : Measure (EffectiveThroat period hPeriod))
    (hPT : MeasurePreserving
      (robinThroatPTMeasurableEquiv period hPeriod) mu mu) :
    robinJunctionAction period hPeriod kMinus kPlus
        (robinBulkPT period hPeriod fields).1
        (robinBulkPT period hPeriod fields).2
        (robinThroatPT period hPeriod junction) mu =
      robinJunctionAction period hPeriod kPlus kMinus
        fields.1 fields.2 junction mu := by
  unfold robinJunctionAction
  calc
    (∫ point, robinJunctionDensity period hPeriod kMinus kPlus
      (robinBulkPT period hPeriod fields).1
      (robinBulkPT period hPeriod fields).2
      (robinThroatPT period hPeriod junction) point ∂mu) =
        ∫ point, robinJunctionDensity period hPeriod kPlus kMinus
          fields.1 fields.2 junction (fixedThroatPT period hPeriod point) ∂mu := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall
        (robinJunctionDensity_pt period hPeriod kPlus kMinus fields junction)
    _ = ∫ point, robinJunctionDensity period hPeriod kPlus kMinus
          fields.1 fields.2 junction point ∂mu :=
      hPT.integral_comp'
        (robinJunctionDensity period hPeriod kPlus kMinus
          fields.1 fields.2 junction)

/-- Affine junction curves commute with the actual throat PT pullback. -/
theorem junctionAffineCurve_pt
    (junction test : SmoothThroatField period hPeriod Real)
    (epsilon : Real) :
    junctionAffineCurve period hPeriod
        (robinThroatPT period hPeriod junction)
        (robinThroatPT period hPeriod test) epsilon =
      robinThroatPT period hPeriod
        (junctionAffineCurve period hPeriod junction test epsilon) := by
  apply SmoothThroatField.ext period hPeriod Real
  intro point
  rfl

/-- Pointwise first-variation covariance. -/
theorem robinFirstVariationDensity_pt
    (kPlus kMinus : Real)
    (fields : RobinBulkFields period hPeriod)
    (junction test : SmoothThroatField period hPeriod Real)
    (point : EffectiveThroat period hPeriod) :
    robinFirstVariationDensity period hPeriod kMinus kPlus
        (robinBulkPT period hPeriod fields).1
        (robinBulkPT period hPeriod fields).2
        (robinThroatPT period hPeriod junction)
        (robinThroatPT period hPeriod test) point =
      robinFirstVariationDensity period hPeriod kPlus kMinus
        fields.1 fields.2 junction test
          (fixedThroatPT period hPeriod point) := by
  unfold robinFirstVariationDensity
  rw [junctionResidual_pt period hPeriod]
  rfl

/-- Integrated first-variation covariance for a PT-invariant measure. -/
theorem robinFirstVariation_pt
    (kPlus kMinus : Real)
    (fields : RobinBulkFields period hPeriod)
    (junction test : SmoothThroatField period hPeriod Real)
    (mu : Measure (EffectiveThroat period hPeriod))
    (hPT : MeasurePreserving
      (robinThroatPTMeasurableEquiv period hPeriod) mu mu) :
    robinFirstVariation period hPeriod kMinus kPlus
        (robinBulkPT period hPeriod fields).1
        (robinBulkPT period hPeriod fields).2
        (robinThroatPT period hPeriod junction)
        (robinThroatPT period hPeriod test) mu =
      robinFirstVariation period hPeriod kPlus kMinus
        fields.1 fields.2 junction test mu := by
  unfold robinFirstVariation
  calc
    (∫ point, robinFirstVariationDensity period hPeriod kMinus kPlus
      (robinBulkPT period hPeriod fields).1
      (robinBulkPT period hPeriod fields).2
      (robinThroatPT period hPeriod junction)
      (robinThroatPT period hPeriod test) point ∂mu) =
        ∫ point, robinFirstVariationDensity period hPeriod kPlus kMinus
          fields.1 fields.2 junction test
            (fixedThroatPT period hPeriod point) ∂mu := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall
        (robinFirstVariationDensity_pt period hPeriod
          kPlus kMinus fields junction test)
    _ = ∫ point, robinFirstVariationDensity period hPeriod kPlus kMinus
          fields.1 fields.2 junction test point ∂mu :=
      hPT.integral_comp'
        (robinFirstVariationDensity period hPeriod kPlus kMinus
          fields.1 fields.2 junction test)

/-- Pointwise Hessian density covariance. -/
theorem robinHessianDensity_pt
    (kPlus kMinus : Real)
    (first second : SmoothThroatField period hPeriod Real)
    (point : EffectiveThroat period hPeriod) :
    robinHessianDensity period hPeriod kMinus kPlus
        (robinThroatPT period hPeriod first)
        (robinThroatPT period hPeriod second) point =
      robinHessianDensity period hPeriod kPlus kMinus first second
        (fixedThroatPT period hPeriod point) := by
  unfold robinHessianDensity robinThroatPT
  simp only [throatPTPullback_apply]
  ring

/-- Integrated Hessian covariance for a PT-invariant measure. -/
theorem robinHessian_pt
    (kPlus kMinus : Real)
    (first second : SmoothThroatField period hPeriod Real)
    (mu : Measure (EffectiveThroat period hPeriod))
    (hPT : MeasurePreserving
      (robinThroatPTMeasurableEquiv period hPeriod) mu mu) :
    robinHessian period hPeriod kMinus kPlus
        (robinThroatPT period hPeriod first)
        (robinThroatPT period hPeriod second) mu =
      robinHessian period hPeriod kPlus kMinus first second mu := by
  unfold robinHessian
  calc
    (∫ point, robinHessianDensity period hPeriod kMinus kPlus
      (robinThroatPT period hPeriod first)
      (robinThroatPT period hPeriod second) point ∂mu) =
        ∫ point, robinHessianDensity period hPeriod kPlus kMinus
          first second (fixedThroatPT period hPeriod point) ∂mu := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall
        (robinHessianDensity_pt period hPeriod kPlus kMinus first second)
    _ = ∫ point, robinHessianDensity period hPeriod kPlus kMinus
          first second point ∂mu :=
      hPT.integral_comp'
        (robinHessianDensity period hPeriod kPlus kMinus first second)

/-- PT pullback as a linear isometry on the genuine throat `L2` space. -/
def robinThroatPTL2Pullback
    (mu : Measure (EffectiveThroat period hPeriod))
    (hPT : MeasurePreserving
      (robinThroatPTMeasurableEquiv period hPeriod) mu mu) :
    ThroatScalarL2 period hPeriod mu →L[Real]
      ThroatScalarL2 period hPeriod mu :=
  (Lp.compMeasurePreservingₗᵢ Real
    (robinThroatPTMeasurableEquiv period hPeriod) hPT).toContinuousLinearMap

theorem robinThroatPTL2Pullback_norm
    (mu : Measure (EffectiveThroat period hPeriod))
    (hPT : MeasurePreserving
      (robinThroatPTMeasurableEquiv period hPeriod) mu mu)
    (field : ThroatScalarL2 period hPeriod mu) :
    ‖robinThroatPTL2Pullback period hPeriod mu hPT field‖ = ‖field‖ :=
  Lp.norm_compMeasurePreserving field hPT

/-- The genuine `L2` PT map intertwines the smooth throat inclusion. -/
theorem robinThroatPTL2Pullback_smooth
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu]
    (hPT : MeasurePreserving
      (robinThroatPTMeasurableEquiv period hPeriod) mu mu)
    (field : SmoothThroatField period hPeriod Real) :
    robinThroatPTL2Pullback period hPeriod mu hPT
        (smoothThroatFieldToL2 period hPeriod mu field) =
      smoothThroatFieldToL2 period hPeriod mu
        (robinThroatPT period hPeriod field) := by
  change
    Lp.compMeasurePreserving
      (robinThroatPTMeasurableEquiv period hPeriod) hPT
      ((smoothThroatField_memLp period hPeriod Real mu field).toLp field.toFun) = _
  rw [Lp.toLp_compMeasurePreserving
    (smoothThroatField_memLp period hPeriod Real mu field) hPT]
  rfl

/-- The exchanged bounded Hessian operators commute with genuine `L2` PT. -/
theorem robinL2HessianOperator_pt_intertwines
    (kPlus kMinus : Real)
    (mu : Measure (EffectiveThroat period hPeriod))
    (hPT : MeasurePreserving
      (robinThroatPTMeasurableEquiv period hPeriod) mu mu) :
    (robinThroatPTL2Pullback period hPeriod mu hPT).comp
        (robinL2HessianOperator period hPeriod kPlus kMinus mu) =
      (robinL2HessianOperator period hPeriod kMinus kPlus mu).comp
        (robinThroatPTL2Pullback period hPeriod mu hPT) := by
  apply ContinuousLinearMap.ext
  intro field
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    robinL2HessianOperator_apply, robinL2HessianOperator_apply, map_smul]
  simp only [add_comm]

/-- Closure bundle for action, first variation, Hessian and bounded operator. -/
theorem scalar_robin_junction_pt_covariance_closure
    (kPlus kMinus : Real)
    (fields : RobinBulkFields period hPeriod)
    (junction test : SmoothThroatField period hPeriod Real)
    (mu : Measure (EffectiveThroat period hPeriod))
    (hPT : MeasurePreserving
      (robinThroatPTMeasurableEquiv period hPeriod) mu mu) :
    robinJunctionAction period hPeriod kMinus kPlus
        (robinBulkPT period hPeriod fields).1
        (robinBulkPT period hPeriod fields).2
        (robinThroatPT period hPeriod junction) mu =
        robinJunctionAction period hPeriod kPlus kMinus
          fields.1 fields.2 junction mu ∧
      robinFirstVariation period hPeriod kMinus kPlus
        (robinBulkPT period hPeriod fields).1
        (robinBulkPT period hPeriod fields).2
        (robinThroatPT period hPeriod junction)
        (robinThroatPT period hPeriod test) mu =
        robinFirstVariation period hPeriod kPlus kMinus
          fields.1 fields.2 junction test mu ∧
      robinHessian period hPeriod kMinus kPlus
        (robinThroatPT period hPeriod test)
        (robinThroatPT period hPeriod test) mu =
        robinHessian period hPeriod kPlus kMinus test test mu := by
  exact ⟨robinJunctionAction_pt period hPeriod kPlus kMinus
      fields junction mu hPT,
    robinFirstVariation_pt period hPeriod kPlus kMinus
      fields junction test mu hPT,
    robinHessian_pt period hPeriod kPlus kMinus test test mu hPT⟩

end

end P0EFTJanusMappingTorusScalarRobinJunctionPTCovariance4D
end JanusFormal
