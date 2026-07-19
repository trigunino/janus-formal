import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusInducedFieldVariation4D

/-!
# Linear space of genuine independent Program-P directions

The simultaneous variation record already consists entirely of smooth vector
spaces; only its assembled linear structure was missing.  This gate installs
that structure componentwise, including the logarithmic directions of both
positive diagonal metrics.  It does not linearize the nonlinear exponential
metric curve itself.
-/

namespace JanusFormal
namespace P0EFTJanusIndependentFieldVariationLinearSpace4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
open P0EFTJanusMappingTorusCandidateAFunctionalVariation4D
open P0EFTJanusMappingTorusInducedFieldVariation4D

variable (period : Real) (hPeriod : period ≠ 0)

@[ext]
theorem SmoothDiagonalMetricVariation.ext
    {first second : SmoothDiagonalMetricVariation period hPeriod}
    (hPlus : first.plusLogDirection = second.plusLogDirection)
    (hMinus : first.minusLogDirection = second.minusLogDirection) :
    first = second := by
  cases first
  cases second
  simp_all

instance : Zero (SmoothDiagonalMetricVariation period hPeriod) where
  zero := ⟨0, 0⟩

instance : Add (SmoothDiagonalMetricVariation period hPeriod) where
  add first second :=
    ⟨first.plusLogDirection + second.plusLogDirection,
      first.minusLogDirection + second.minusLogDirection⟩

instance : Neg (SmoothDiagonalMetricVariation period hPeriod) where
  neg variation :=
    ⟨-variation.plusLogDirection, -variation.minusLogDirection⟩

instance : AddCommGroup (SmoothDiagonalMetricVariation period hPeriod) where
  add_assoc := by
    intro first second third
    apply SmoothDiagonalMetricVariation.ext
    · exact add_assoc _ _ _
    · exact add_assoc _ _ _
  zero_add := by
    intro variation
    apply SmoothDiagonalMetricVariation.ext
    · exact zero_add _
    · exact zero_add _
  add_zero := by
    intro variation
    apply SmoothDiagonalMetricVariation.ext
    · exact add_zero _
    · exact add_zero _
  nsmul := nsmulRec
  add_comm := by
    intro first second
    apply SmoothDiagonalMetricVariation.ext
    · exact add_comm _ _
    · exact add_comm _ _
  neg_add_cancel := by
    intro variation
    apply SmoothDiagonalMetricVariation.ext
    · exact neg_add_cancel _
    · exact neg_add_cancel _
  sub_eq_add_neg := by
    intro first second
    apply SmoothDiagonalMetricVariation.ext
    · exact sub_eq_add_neg _ _
    · exact sub_eq_add_neg _ _
  zsmul := zsmulRec

instance : SMul Real (SmoothDiagonalMetricVariation period hPeriod) where
  smul scalar variation :=
    ⟨scalar • variation.plusLogDirection,
      scalar • variation.minusLogDirection⟩

instance : Module Real (SmoothDiagonalMetricVariation period hPeriod) where
  one_smul := by
    intro variation
    apply SmoothDiagonalMetricVariation.ext
    · exact one_smul Real _
    · exact one_smul Real _
  mul_smul := by
    intro first second variation
    apply SmoothDiagonalMetricVariation.ext
    · exact mul_smul _ _ _
    · exact mul_smul _ _ _
  smul_add := by
    intro scalar first second
    apply SmoothDiagonalMetricVariation.ext
    · exact smul_add _ _ _
    · exact smul_add _ _ _
  smul_zero := by
    intro scalar
    apply SmoothDiagonalMetricVariation.ext
    · exact smul_zero _
    · exact smul_zero _
  add_smul := by
    intro first second variation
    apply SmoothDiagonalMetricVariation.ext
    · exact add_smul _ _ _
    · exact add_smul _ _ _
  zero_smul := by
    intro variation
    apply SmoothDiagonalMetricVariation.ext
    · exact zero_smul Real _
    · exact zero_smul Real _

@[ext]
theorem IndependentFieldVariation.ext
    {first second : IndependentFieldVariation period hPeriod}
    (hMetrics : first.metrics = second.metrics)
    (hMatter : first.matter = second.matter)
    (hGauge : first.gauge = second.gauge)
    (hGhosts : first.ghosts = second.ghosts)
    (hAuxiliaries : first.auxiliaries = second.auxiliaries)
    (hLLAuxMetric : first.llAuxMetric = second.llAuxMetric)
    (hLLMeasure : first.llMeasure = second.llMeasure)
    (hLLField : first.llField = second.llField) : first = second := by
  cases first
  cases second
  simp_all

instance : Zero (IndependentFieldVariation period hPeriod) where
  zero := ⟨0, 0, 0, 0, 0, 0, 0, 0⟩

instance : Add (IndependentFieldVariation period hPeriod) where
  add first second :=
    ⟨first.metrics + second.metrics, first.matter + second.matter,
      first.gauge + second.gauge, first.ghosts + second.ghosts,
      first.auxiliaries + second.auxiliaries,
      first.llAuxMetric + second.llAuxMetric,
      first.llMeasure + second.llMeasure, first.llField + second.llField⟩

instance : Neg (IndependentFieldVariation period hPeriod) where
  neg variation :=
    ⟨-variation.metrics, -variation.matter, -variation.gauge,
      -variation.ghosts, -variation.auxiliaries, -variation.llAuxMetric,
      -variation.llMeasure, -variation.llField⟩

instance : AddCommGroup (IndependentFieldVariation period hPeriod) where
  add_assoc := by
    intro first second third
    apply IndependentFieldVariation.ext <;> exact add_assoc _ _ _
  zero_add := by
    intro variation
    apply IndependentFieldVariation.ext <;> exact zero_add _
  add_zero := by
    intro variation
    apply IndependentFieldVariation.ext <;> exact add_zero _
  nsmul := nsmulRec
  add_comm := by
    intro first second
    apply IndependentFieldVariation.ext <;> exact add_comm _ _
  neg_add_cancel := by
    intro variation
    apply IndependentFieldVariation.ext <;> exact neg_add_cancel _
  sub_eq_add_neg := by
    intro first second
    apply IndependentFieldVariation.ext <;> exact sub_eq_add_neg _ _
  zsmul := zsmulRec

instance : SMul Real (IndependentFieldVariation period hPeriod) where
  smul scalar variation :=
    ⟨scalar • variation.metrics, scalar • variation.matter,
      scalar • variation.gauge, scalar • variation.ghosts,
      scalar • variation.auxiliaries, scalar • variation.llAuxMetric,
      scalar • variation.llMeasure, scalar • variation.llField⟩

instance : Module Real (IndependentFieldVariation period hPeriod) where
  one_smul := by
    intro variation
    apply IndependentFieldVariation.ext <;> exact one_smul Real _
  mul_smul := by
    intro first second variation
    apply IndependentFieldVariation.ext <;> exact mul_smul _ _ _
  smul_add := by
    intro scalar first second
    apply IndependentFieldVariation.ext <;> exact smul_add _ _ _
  smul_zero := by
    intro scalar
    apply IndependentFieldVariation.ext <;> exact smul_zero _
  add_smul := by
    intro first second variation
    apply IndependentFieldVariation.ext <;> exact add_smul _ _ _
  zero_smul := by
    intro variation
    apply IndependentFieldVariation.ext <;> exact zero_smul Real _

/-- Forgetful projection to the actual pair of global gauge coefficient
directions is linear. -/
def independentGaugeVariationLinearMap :
    IndependentFieldVariation period hPeriod →ₗ[Real]
      (P0EFTJanusMappingTorusSmoothFieldDescent4D.SmoothQuotientField
          period hPeriod
          P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D.GaugeFiber ×
        P0EFTJanusMappingTorusSmoothFieldDescent4D.SmoothQuotientField
          period hPeriod
          P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D.GaugeFiber) where
  toFun := IndependentFieldVariation.gauge
  map_add' := by intro first second; rfl
  map_smul' := by intro scalar variation; rfl

/-- The LL direction used by the differential worldvolume action is likewise
an exact linear projection of the same global tangent record. -/
def independentLLFieldVariationLinearMap :
    IndependentFieldVariation period hPeriod →ₗ[Real]
      P0EFTJanusMappingTorusSmoothThroatTrace4D.SmoothThroatField
        period hPeriod
        P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D.LLFieldFiber where
  toFun := IndependentFieldVariation.llField
  map_add' := by intro first second; rfl
  map_smul' := by intro scalar variation; rfl

end
end P0EFTJanusIndependentFieldVariationLinearSpace4D
end JanusFormal
