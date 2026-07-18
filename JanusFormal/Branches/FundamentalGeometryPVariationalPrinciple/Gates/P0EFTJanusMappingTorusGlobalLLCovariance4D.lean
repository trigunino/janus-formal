import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGlobalLLVariation4D

/-!
# PT covariance of the global LL worldvolume action

The actual throat PT involution acts by pullback on the three independent LL
coefficient fields.  This gate proves covariance of the selected density, its
Euler pairing and its affine variation, and invariance of the integrated
action and first variation for every explicitly PT-invariant Borel measure.
No volume form or field equation is assumed.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusGlobalLLCovariance4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff Topology
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusPTInvolution
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
open P0EFTJanusMappingTorusGlobalLLWorldvolume4D
open P0EFTJanusMappingTorusGlobalLLVariation4D

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

/-- Measurable equivalence underlying the already constructed smooth throat
PT diffeomorphism. -/
def fixedThroatPTMeasurableEquiv :
    EffectiveThroat period hPeriod ≃ᵐ EffectiveThroat period hPeriod where
  toEquiv :=
    { toFun := fixedThroatPT period hPeriod
      invFun := fixedThroatPT period hPeriod
      left_inv := fixedThroatPT_involutive period hPeriod
      right_inv := fixedThroatPT_involutive period hPeriod }
  measurable_toFun :=
    (continuous_fixedThroatPT period hPeriod).measurable
  measurable_invFun :=
    (continuous_fixedThroatPT period hPeriod).measurable

/-- Pullback of precisely the three LL coefficient fields by the actual throat
PT involution.  All bulk independent fields remain untouched. -/
def llPTPullback
    (fields : IndependentFields period hPeriod) :
    IndependentFields period hPeriod :=
  { fields with
    llAuxMetric := throatPTPullback period hPeriod LLMetricFiber fields.llAuxMetric
    llMeasure := throatPTPullback period hPeriod Real fields.llMeasure
    llField := throatPTPullback period hPeriod LLFieldFiber fields.llField }

/-- PT pullback of an independent LL tangent direction. -/
def llVariationPTPullback
    (variation : LLVariation period hPeriod) : LLVariation period hPeriod where
  measureDirection := throatPTPullback period hPeriod Real variation.measureDirection
  fieldDirection := throatPTPullback period hPeriod LLFieldFiber variation.fieldDirection

@[simp]
theorem llPTPullback_involutive
    (fields : IndependentFields period hPeriod) :
    llPTPullback period hPeriod (llPTPullback period hPeriod fields) = fields := by
  cases fields
  simp [llPTPullback, throatPTPullback_involutive]

@[simp]
theorem llVariationPTPullback_involutive
    (variation : LLVariation period hPeriod) :
    llVariationPTPullback period hPeriod
      (llVariationPTPullback period hPeriod variation) = variation := by
  cases variation
  simp [llVariationPTPullback, throatPTPullback_involutive]

/-- The scalar LL density is a genuine scalar under the throat PT pullback. -/
theorem llWorldvolumeDensity_pt
    (fields : IndependentFields period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    llWorldvolumeDensity period hPeriod
        (llPTPullback period hPeriod fields) point =
      llWorldvolumeDensity period hPeriod fields
        (fixedThroatPT period hPeriod point) := by
  rfl

/-- A PT-invariant measure makes the global LL action exactly invariant. -/
theorem globalLLAction_pt
    (fields : IndependentFields period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod))
    (hPT : MeasurePreserving
      (fixedThroatPTMeasurableEquiv period hPeriod) mu mu) :
    globalLLAction period hPeriod (llPTPullback period hPeriod fields) mu =
      globalLLAction period hPeriod fields mu := by
  unfold globalLLAction
  calc
    (∫ point, llWorldvolumeDensity period hPeriod
        (llPTPullback period hPeriod fields) point ∂mu) =
        ∫ point, llWorldvolumeDensity period hPeriod fields
          (fixedThroatPT period hPeriod point) ∂mu := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall
        (llWorldvolumeDensity_pt period hPeriod fields)
    _ = ∫ point, llWorldvolumeDensity period hPeriod fields point ∂mu :=
      hPT.integral_comp' (llWorldvolumeDensity period hPeriod fields)

/-- The pointwise first variation is covariant when both the base field and
its independent tangent direction are pulled back. -/
theorem llFirstVariationDensity_pt
    (fields : IndependentFields period hPeriod)
    (variation : LLVariation period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    llFirstVariationDensity period hPeriod
        (llPTPullback period hPeriod fields)
        (llVariationPTPullback period hPeriod variation) point =
      llFirstVariationDensity period hPeriod fields variation
        (fixedThroatPT period hPeriod point) := by
  rfl

/-- The integrated LL first variation is PT invariant. -/
theorem globalLLFirstVariation_pt
    (fields : IndependentFields period hPeriod)
    (variation : LLVariation period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod))
    (hPT : MeasurePreserving
      (fixedThroatPTMeasurableEquiv period hPeriod) mu mu) :
    globalLLFirstVariation period hPeriod
        (llPTPullback period hPeriod fields)
        (llVariationPTPullback period hPeriod variation) mu =
      globalLLFirstVariation period hPeriod fields variation mu := by
  unfold globalLLFirstVariation
  calc
    (∫ point, llFirstVariationDensity period hPeriod
        (llPTPullback period hPeriod fields)
        (llVariationPTPullback period hPeriod variation) point ∂mu) =
        ∫ point, llFirstVariationDensity period hPeriod fields variation
          (fixedThroatPT period hPeriod point) ∂mu := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall
        (llFirstVariationDensity_pt period hPeriod fields variation)
    _ = ∫ point, llFirstVariationDensity period hPeriod fields variation point
          ∂mu :=
      hPT.integral_comp'
        (llFirstVariationDensity period hPeriod fields variation)

/-- The complete affine action curve is PT invariant, not only its derivative
at the origin. -/
theorem globalLLAction_affine_pt
    (fields : IndependentFields period hPeriod)
    (variation : LLVariation period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod))
    (hPT : MeasurePreserving
      (fixedThroatPTMeasurableEquiv period hPeriod) mu mu)
    (epsilon : Real) :
    globalLLAction period hPeriod
        (llAffineCurve period hPeriod
          (llPTPullback period hPeriod fields)
          (llVariationPTPullback period hPeriod variation) epsilon) mu =
      globalLLAction period hPeriod
        (llAffineCurve period hPeriod fields variation epsilon) mu := by
  unfold globalLLAction
  calc
    (∫ point, llWorldvolumeDensity period hPeriod
        (llAffineCurve period hPeriod
          (llPTPullback period hPeriod fields)
          (llVariationPTPullback period hPeriod variation) epsilon) point ∂mu) =
        ∫ point, llWorldvolumeDensity period hPeriod
          (llAffineCurve period hPeriod fields variation epsilon)
          (fixedThroatPT period hPeriod point) ∂mu := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun point => by
        rfl
    _ = ∫ point, llWorldvolumeDensity period hPeriod
          (llAffineCurve period hPeriod fields variation epsilon) point ∂mu :=
      hPT.integral_comp'
        (llWorldvolumeDensity period hPeriod
          (llAffineCurve period hPeriod fields variation epsilon))

/-- The actual directional derivative transforms with the same PT pullback;
its value is the untransformed global Euler pairing. -/
theorem globalLLAction_affine_pt_hasDerivAt
    (fields : IndependentFields period hPeriod)
    (variation : LLVariation period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu]
    (hPT : MeasurePreserving
      (fixedThroatPTMeasurableEquiv period hPeriod) mu mu) :
    HasDerivAt
      (fun epsilon : Real => globalLLAction period hPeriod
        (llAffineCurve period hPeriod
          (llPTPullback period hPeriod fields)
          (llVariationPTPullback period hPeriod variation) epsilon) mu)
      (globalLLFirstVariation period hPeriod fields variation mu) 0 := by
  have hDerivative := globalLLAction_affine_hasDerivAt period hPeriod
    (llPTPullback period hPeriod fields)
    (llVariationPTPullback period hPeriod variation) mu
  rw [globalLLFirstVariation_pt period hPeriod fields variation mu hPT]
    at hDerivative
  exact hDerivative

/-- Both Euler coefficients commute with the actual throat PT pullback. -/
theorem llEuler_pt
    (fields : IndependentFields period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    llMeasureEuler period hPeriod (llPTPullback period hPeriod fields) point =
        llMeasureEuler period hPeriod fields
          (fixedThroatPT period hPeriod point) ∧
      llFieldEuler period hPeriod (llPTPullback period hPeriod fields) point =
        llFieldEuler period hPeriod fields
          (fixedThroatPT period hPeriod point) := by
  exact ⟨rfl, rfl⟩

/-- Consequently, the complete pointwise Euler system is PT covariant. -/
theorem llStationaryAt_pt
    (fields : IndependentFields period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    LLStationaryAt period hPeriod (llPTPullback period hPeriod fields) point ↔
      LLStationaryAt period hPeriod fields
        (fixedThroatPT period hPeriod point) := by
  rfl

/-- Closure bundle: action, differential and Euler equations all transform on
the same global D8 throat fields. -/
theorem global_ll_pt_covariance_closure
    (fields : IndependentFields period hPeriod)
    (variation : LLVariation period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod))
    (hPT : MeasurePreserving
      (fixedThroatPTMeasurableEquiv period hPeriod) mu mu) :
    globalLLAction period hPeriod (llPTPullback period hPeriod fields) mu =
        globalLLAction period hPeriod fields mu ∧
      globalLLFirstVariation period hPeriod
          (llPTPullback period hPeriod fields)
          (llVariationPTPullback period hPeriod variation) mu =
        globalLLFirstVariation period hPeriod fields variation mu ∧
      (∀ point, LLStationaryAt period hPeriod
          (llPTPullback period hPeriod fields) point ↔
        LLStationaryAt period hPeriod fields
          (fixedThroatPT period hPeriod point)) := by
  exact ⟨globalLLAction_pt period hPeriod fields mu hPT,
    globalLLFirstVariation_pt period hPeriod fields variation mu hPT,
    llStationaryAt_pt period hPeriod fields⟩

end

end P0EFTJanusMappingTorusGlobalLLCovariance4D
end JanusFormal
