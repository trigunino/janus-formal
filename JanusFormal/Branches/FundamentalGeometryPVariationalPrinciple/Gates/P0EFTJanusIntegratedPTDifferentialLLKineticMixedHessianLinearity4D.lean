import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusIntegratedPTDifferentialLLKineticMixedHessian4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusDifferentialLLKineticMixedHessianIntegrability4D

namespace JanusFormal
namespace P0EFTJanusIntegratedPTDifferentialLLKineticMixedHessianLinearity4D

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff Topology
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLHessian4D
open P0EFTJanusIntegratedPTDifferentialLLKineticMixedHessian4D
open P0EFTJanusDifferentialLLKineticMixedHessianIntegrability4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)
local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance : BorelSpace (EffectiveThroat period hPeriod) where measurable_eq := rfl

theorem ptMixedHessianDensity_continuous
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (aux : SmoothThroatField period hPeriod LLMetricFiber)
    (field : SmoothThroatField period hPeriod LLFieldFiber)
    (dAux₁ dAux₂ : SmoothThroatField period hPeriod LLMetricFiber)
    (dField₁ dField₂ : SmoothThroatField period hPeriod LLFieldFiber) :
    Continuous (ptSymmetricDifferentialLLKineticMixedHessianDensity period hPeriod
      frame aux field dAux₁ dAux₂ dField₁ dField₂) := by
  unfold ptSymmetricDifferentialLLKineticMixedHessianDensity
  exact continuous_const.mul
    ((differentialLLKineticMixedHessianDensity_continuous period hPeriod frame aux field
      dAux₁ dAux₂ dField₁ dField₂).add
    (differentialLLKineticMixedHessianDensity_continuous period hPeriod frame
      (throatPTPullback period hPeriod LLMetricFiber aux)
      (throatPTPullback period hPeriod LLFieldFiber field)
      (differentialLLAuxMetricDirectionPT period hPeriod dAux₁)
      (differentialLLAuxMetricDirectionPT period hPeriod dAux₂)
      (differentialLLFluxDirectionPT period hPeriod dField₁)
      (differentialLLFluxDirectionPT period hPeriod dField₂)))

theorem ptMixedHessianDensity_integrable
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (aux : SmoothThroatField period hPeriod LLMetricFiber)
    (field : SmoothThroatField period hPeriod LLFieldFiber)
    (dAux₁ dAux₂ : SmoothThroatField period hPeriod LLMetricFiber)
    (dField₁ dField₂ : SmoothThroatField period hPeriod LLFieldFiber)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    Integrable (ptSymmetricDifferentialLLKineticMixedHessianDensity period hPeriod
      frame aux field dAux₁ dAux₂ dField₁ dField₂) mu :=
  (ptMixedHessianDensity_continuous period hPeriod frame aux field dAux₁ dAux₂
    dField₁ dField₂).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem ptMixedHessianDensity_add_first
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (aux : SmoothThroatField period hPeriod LLMetricFiber)
    (field : SmoothThroatField period hPeriod LLFieldFiber)
    (a a' b : SmoothThroatField period hPeriod LLMetricFiber)
    (u u' v : SmoothThroatField period hPeriod LLFieldFiber)
    (p : EffectiveThroat period hPeriod) :
    ptSymmetricDifferentialLLKineticMixedHessianDensity period hPeriod frame aux field
        (a + a') b (u + u') v p =
      ptSymmetricDifferentialLLKineticMixedHessianDensity period hPeriod frame aux field
          a b u v p +
        ptSymmetricDifferentialLLKineticMixedHessianDensity period hPeriod frame aux field
          a' b u' v p := by
  unfold ptSymmetricDifferentialLLKineticMixedHessianDensity
  rw [differentialLLKineticMixedHessianDensity_add_first]
  have ha : differentialLLAuxMetricDirectionPT period hPeriod (a + a') =
      differentialLLAuxMetricDirectionPT period hPeriod a +
        differentialLLAuxMetricDirectionPT period hPeriod a' := by ext; rfl
  have hu : differentialLLFluxDirectionPT period hPeriod (u + u') =
      differentialLLFluxDirectionPT period hPeriod u +
        differentialLLFluxDirectionPT period hPeriod u' := by ext; rfl
  rw [ha, hu, differentialLLKineticMixedHessianDensity_add_first]
  ring

theorem globalPTMixedHessian_add_first
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (aux : SmoothThroatField period hPeriod LLMetricFiber)
    (field : SmoothThroatField period hPeriod LLFieldFiber)
    (a a' b : SmoothThroatField period hPeriod LLMetricFiber)
    (u u' v : SmoothThroatField period hPeriod LLFieldFiber)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    globalPTDifferentialLLKineticMixedHessian period hPeriod frame aux field
        (a + a') b (u + u') v mu =
      globalPTDifferentialLLKineticMixedHessian period hPeriod frame aux field a b u v mu +
        globalPTDifferentialLLKineticMixedHessian period hPeriod frame aux field a' b u' v mu := by
  unfold globalPTDifferentialLLKineticMixedHessian
  rw [← integral_add
    (ptMixedHessianDensity_integrable period hPeriod frame aux field a b u v mu)
    (ptMixedHessianDensity_integrable period hPeriod frame aux field a' b u' v mu)]
  apply integral_congr_ae
  filter_upwards [] with p
  exact ptMixedHessianDensity_add_first period hPeriod frame aux field a a' b u u' v p

theorem ptMixedHessianDensity_neg_first
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (aux : SmoothThroatField period hPeriod LLMetricFiber)
    (field : SmoothThroatField period hPeriod LLFieldFiber)
    (a b : SmoothThroatField period hPeriod LLMetricFiber)
    (u v : SmoothThroatField period hPeriod LLFieldFiber)
    (p : EffectiveThroat period hPeriod) :
    ptSymmetricDifferentialLLKineticMixedHessianDensity period hPeriod frame aux field
        (-a) b (-u) v p =
      -ptSymmetricDifferentialLLKineticMixedHessianDensity period hPeriod frame aux field
        a b u v p := by
  unfold ptSymmetricDifferentialLLKineticMixedHessianDensity
  rw [show -a = (-1 : Real) • a by simp, show -u = (-1 : Real) • u by simp]
  rw [differentialLLKineticMixedHessianDensity_smul_first]
  have ha : differentialLLAuxMetricDirectionPT period hPeriod ((-1 : Real) • a) =
      (-1 : Real) • differentialLLAuxMetricDirectionPT period hPeriod a := by ext; rfl
  have hu : differentialLLFluxDirectionPT period hPeriod ((-1 : Real) • u) =
      (-1 : Real) • differentialLLFluxDirectionPT period hPeriod u := by ext; rfl
  rw [ha, hu, differentialLLKineticMixedHessianDensity_smul_first]
  ring

theorem globalPTMixedHessian_neg_first
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (aux : SmoothThroatField period hPeriod LLMetricFiber)
    (field : SmoothThroatField period hPeriod LLFieldFiber)
    (a b : SmoothThroatField period hPeriod LLMetricFiber)
    (u v : SmoothThroatField period hPeriod LLFieldFiber)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    globalPTDifferentialLLKineticMixedHessian period hPeriod frame aux field
        (-a) b (-u) v mu =
      -globalPTDifferentialLLKineticMixedHessian period hPeriod frame aux field a b u v mu := by
  unfold globalPTDifferentialLLKineticMixedHessian
  rw [← integral_neg]
  apply integral_congr_ae
  filter_upwards [] with p
  exact ptMixedHessianDensity_neg_first period hPeriod frame aux field a b u v p

end
end P0EFTJanusIntegratedPTDifferentialLLKineticMixedHessianLinearity4D
end JanusFormal
