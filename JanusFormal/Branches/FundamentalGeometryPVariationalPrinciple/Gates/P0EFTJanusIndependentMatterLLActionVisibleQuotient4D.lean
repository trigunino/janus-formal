import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusIndependentMatterLLInactiveQuotientHessian4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCombinedLLActionVariation4D

/-!
# One visible quotient for the same matter--LL action and Hessian

The full curve of the present sector depends on the matter pair and on the
three differential-LL slots (auxiliary metric, measure coefficient and field).
This gate bundles that exact observation as a linear projection.  Its kernel
acts trivially on the unchanged action curve, while the already proved
matter--LL Hessian vanishes on the same kernel.  The result remains sectorial:
EH, Maxwell and their gauge quotient are not supplied here.
-/

namespace JanusFormal
namespace P0EFTJanusIndependentMatterLLActionVisibleQuotient4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff
open MeasureTheory
open P0EFTJanusReflectionFixedThroat P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusInducedFieldVariation4D
open P0EFTJanusIndependentFieldVariationLinearSpace4D
open P0EFTJanusProgramPCommonGeometricDomain4D
open P0EFTJanusIndependentCompleteVariationEmbedding4D
open P0EFTJanusCompleteVariationMatterActionHessian4D
open P0EFTJanusCompleteVariationLLActionHessian4D
open P0EFTJanusCompleteVariationMatterLLActionHessian4D
open P0EFTJanusIndependentMatterLLHessianBilinear4D
open P0EFTJanusIndependentMatterLLInactiveQuotientHessian4D
open P0EFTJanusCombinedLLActionVariation4D
open P0EFTJanusCommonMatterActionVariation4D
open P0EFTJanusMappingTorusLinearizedDiffeomorphismBRST4D
open P0EFTJanusMappingTorusScalarDiffeomorphismNoetherOperator4D
open P0EFTJanusGlobalMatterMultipletActualEulerHessian4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLWeakEquation4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)

local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance : IsManifold throatCoverModelWithCorners ω
    (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _

local instance : BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

/-- Exactly the four tangent blocks read by the present matter--LL action. -/
abbrev MatterLLActionVisibleDirection :=
  (SmoothQuotientField period hPeriod MatterFiber ×
      SmoothQuotientField period hPeriod MatterFiber) ×
    (SmoothThroatField period hPeriod LLMetricFiber ×
      (SmoothThroatField period hPeriod Real ×
        SmoothThroatField period hPeriod LLFieldFiber))

/-- Linear observation of all and only the tangent blocks used by the same
matter--LL action curve. -/
def matterLLActionVisibleProjection :
    IndependentFieldVariation period hPeriod →ₗ[Real]
      MatterLLActionVisibleDirection period hPeriod where
  toFun variation :=
    ⟨variation.matter,
      ⟨variation.llAuxMetric, ⟨variation.llMeasure, variation.llField⟩⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Directions invisible to the unchanged matter--LL action curve. -/
def matterLLActionInvisibleSubmodule :
    Submodule Real (IndependentFieldVariation period hPeriod) :=
  LinearMap.ker (matterLLActionVisibleProjection period hPeriod)

theorem mem_matterLLActionInvisibleSubmodule_iff
    (variation : IndependentFieldVariation period hPeriod) :
    variation ∈ matterLLActionInvisibleSubmodule period hPeriod ↔
      variation.matter = 0 ∧ variation.llAuxMetric = 0 ∧
        variation.llMeasure = 0 ∧ variation.llField = 0 := by
  change (variation.matter,
      (variation.llAuxMetric, (variation.llMeasure, variation.llField))) = 0 ↔ _
  simp

/-- Equal visible projections give equal curves of the exact same action. -/
theorem completeVariationMatterLLActionCurve_congr_visible
    (data : MatterMultipletActionData period hPeriod)
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod))
    (first second : IndependentFieldVariation period hPeriod)
    (parameter : Real)
    (hVisible : matterLLActionVisibleProjection period hPeriod first =
      matterLLActionVisibleProjection period hPeriod second) :
    completeVariationMatterLLActionCurve period hPeriod data frame fields
        (independentCompleteVariation period hPeriod first) mu parameter =
      completeVariationMatterLLActionCurve period hPeriod data frame fields
        (independentCompleteVariation period hPeriod second) mu parameter := by
  have hMatter : first.matter = second.matter := congrArg Prod.fst hVisible
  have hAux : first.llAuxMetric = second.llAuxMetric :=
    congrArg (fun visible => visible.2.1) hVisible
  have hMeasure : first.llMeasure = second.llMeasure :=
    congrArg (fun visible => visible.2.2.1) hVisible
  have hField : first.llField = second.llField :=
    congrArg (fun visible => visible.2.2.2) hVisible
  unfold completeVariationMatterLLActionCurve
  congr 1
  · simp only [completeVariationMatterActionCurve_on_independent]
    unfold globalIndependentMatterAction
    apply congrArg (globalMatterMultipletAction period hPeriod data)
    funext index
    ext point
    simp [independentMatterScalar, selectMatterField, independentFieldCurve,
      independentMatterComponentFamily, hMatter]
  · simp only [completeVariationLLActionCurve_on_independent]
    apply globalPTSymmetricDifferentialLLAction_congr_llData period hPeriod frame
    · simp [independentFieldCurve, hAux]
    · simp [independentFieldCurve, hMeasure]
    · simp [independentFieldCurve, hField]

/-- Hence adding any kernel direction leaves the complete sectorial action
curve unchanged at every parameter. -/
theorem completeVariationMatterLLActionCurve_add_invisible
    (data : MatterMultipletActionData period hPeriod)
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod))
    (variation invisible : IndependentFieldVariation period hPeriod)
    (hInvisible : invisible ∈ matterLLActionInvisibleSubmodule period hPeriod)
    (parameter : Real) :
    completeVariationMatterLLActionCurve period hPeriod data frame fields
        (independentCompleteVariation period hPeriod (variation + invisible))
        mu parameter =
      completeVariationMatterLLActionCurve period hPeriod data frame fields
        (independentCompleteVariation period hPeriod variation) mu parameter := by
  apply completeVariationMatterLLActionCurve_congr_visible period hPeriod
  rw [map_add, LinearMap.mem_ker.mp hInvisible, add_zero]

/-- The unchanged action curve itself therefore descends to the algebraic
quotient by its exact invisible kernel. -/
def matterLLVisibleQuotientActionCurve
    (data : MatterMultipletActionData period hPeriod)
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) (parameter : Real)
    (variation : IndependentFieldVariation period hPeriod ⧸
      matterLLActionInvisibleSubmodule period hPeriod) : Real :=
  Quotient.liftOn variation
    (fun representative =>
      completeVariationMatterLLActionCurve period hPeriod data frame fields
        (independentCompleteVariation period hPeriod representative) mu parameter)
    (by
      intro first second hRelation
      apply completeVariationMatterLLActionCurve_congr_visible period hPeriod
      have hKernel : first - second ∈
          matterLLActionInvisibleSubmodule period hPeriod :=
        (Submodule.quotientRel_def
          (matterLLActionInvisibleSubmodule period hPeriod)).mp hRelation
      have hDifference :
          matterLLActionVisibleProjection period hPeriod first -
              matterLLActionVisibleProjection period hPeriod second = 0 := by
        rw [← map_sub]
        exact LinearMap.mem_ker.mp hKernel
      exact sub_eq_zero.mp hDifference)

@[simp] theorem matterLLVisibleQuotientActionCurve_mkQ
    (data : MatterMultipletActionData period hPeriod)
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) (parameter : Real)
    (variation : IndependentFieldVariation period hPeriod) :
    matterLLVisibleQuotientActionCurve period hPeriod data frame fields mu
        parameter ((matterLLActionInvisibleSubmodule period hPeriod).mkQ variation) =
      completeVariationMatterLLActionCurve period hPeriod data frame fields
        (independentCompleteVariation period hPeriod variation) mu parameter :=
  rfl

/-- The action-invisible kernel is contained in the radical already used for
the sectorial Hessian quotient. -/
theorem actionInvisible_le_hessianInvisible :
    matterLLActionInvisibleSubmodule period hPeriod ≤
      matterLLInvisibleSubmodule period hPeriod := by
  intro variation hVariation
  obtain ⟨hMatter, _, _, hField⟩ :=
    (mem_matterLLActionInvisibleSubmodule_iff period hPeriod variation).mp
      hVariation
  rw [mem_matterLLInvisibleSubmodule_iff]
  constructor
  · change matterVariationComponentFamily period hPeriod variation.matter = 0
    rw [hMatter]
    funext component
    ext point
    unfold matterVariationComponentFamily
    by_cases h : component.1 = 0
    · simp only [h, if_true]
      exact map_zero (EuclideanSpace.proj component.2)
    · simp only [h, if_false]
      exact map_zero (EuclideanSpace.proj component.2)
  · exact hField

/-- The genuine sectorial Hessian descends to the very same quotient whose
kernel leaves the action curve unchanged. -/
def matterLLActionVisibleQuotientHessian
    (data : MatterMultipletActionData period hPeriod)
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    (IndependentFieldVariation period hPeriod ⧸
        matterLLActionInvisibleSubmodule period hPeriod) →ₗ[Real]
      (IndependentFieldVariation period hPeriod ⧸
        matterLLActionInvisibleSubmodule period hPeriod) →ₗ[Real] Real :=
  (independentMatterLLHessianBilinear period hPeriod data frame fields mu).liftQ₂
    (matterLLActionInvisibleSubmodule period hPeriod)
    (matterLLActionInvisibleSubmodule period hPeriod)
    (by
      intro invisible hInvisible
      ext direction
      exact matterLLHessian_zero_left period hPeriod data frame fields mu
        invisible direction (actionInvisible_le_hessianInvisible period hPeriod hInvisible))
    (by
      intro invisible hInvisible
      ext direction
      exact matterLLHessian_zero_right period hPeriod data frame fields mu
        invisible direction (actionInvisible_le_hessianInvisible period hPeriod hInvisible))

@[simp] theorem matterLLActionVisibleQuotientHessian_mkQ
    (data : MatterMultipletActionData period hPeriod)
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu]
    (first second : IndependentFieldVariation period hPeriod) :
    matterLLActionVisibleQuotientHessian period hPeriod data frame fields mu
        ((matterLLActionInvisibleSubmodule period hPeriod).mkQ first)
        ((matterLLActionInvisibleSubmodule period hPeriod).mkQ second) =
      completeVariationMatterLLHessian period hPeriod data frame fields
        (independentCompleteVariation period hPeriod first)
        (independentCompleteVariation period hPeriod second) mu :=
  rfl

theorem matterLLActionVisibleQuotientHessian_symmetric
    (data : MatterMultipletActionData period hPeriod)
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu]
    (first second : IndependentFieldVariation period hPeriod ⧸
      matterLLActionInvisibleSubmodule period hPeriod) :
    matterLLActionVisibleQuotientHessian period hPeriod data frame fields mu
        first second =
      matterLLActionVisibleQuotientHessian period hPeriod data frame fields mu
        second first := by
  obtain ⟨first, rfl⟩ :=
    (matterLLActionInvisibleSubmodule period hPeriod).mkQ_surjective first
  obtain ⟨second, rfl⟩ :=
    (matterLLActionInvisibleSubmodule period hPeriod).mkQ_surjective second
  exact independentMatterLLHessianBilinear_symmetric period hPeriod data frame
    fields mu first second

end
end P0EFTJanusIndependentMatterLLActionVisibleQuotient4D
end JanusFormal
