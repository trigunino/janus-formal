import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12ScalarFrameGhostInjection4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusShiftedSobolevMappingTorusFiniteTemporalFourierBridge4D

/-! The real smooth scalar and diffeomorphism ghost spaces have infinite
dimension for a positive period, using the existing injective temporal
Fourier realization and the finite spanning tangent family. -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12SmoothGhostInfiniteDimension4D
set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusShiftedSobolevMappingTorusFiniteTemporalFourierBridge4D
open P0EFTJanusProgramPT12ScalarFrameGhostInjection4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

def smoothComplexComponent (component : Complex →L[Real] Real) :
    SmoothQuotientField period hPeriod Complex →ₗ[Real]
      SmoothQuotientField period hPeriod Real where
  toFun field := {
    toFun := fun point => component (field point)
    contMDiff_toFun := component.contDiff.contMDiff.comp field.contMDiff_toFun }
  map_add' first second := by
    apply SmoothQuotientField.ext period hPeriod Real
    intro point
    exact component.map_add (first point) (second point)
  map_smul' scalar field := by
    apply SmoothQuotientField.ext period hPeriod Real
    intro point
    exact component.map_smul scalar (field point)

def smoothComplexRealParts :
    SmoothQuotientField period hPeriod Complex →ₗ[Real]
      (SmoothQuotientField period hPeriod Real × SmoothQuotientField period hPeriod Real) :=
  (smoothComplexComponent period hPeriod Complex.reCLM).prod
    (smoothComplexComponent period hPeriod Complex.imCLM)

theorem smoothComplexRealParts_injective :
    Function.Injective (smoothComplexRealParts period hPeriod) := by
  intro first second hEqual
  apply SmoothQuotientField.ext period hPeriod Complex
  intro point
  apply Complex.ext
  · exact congrArg (fun fields => fields.1 point) hEqual
  · exact congrArg (fun fields => fields.2 point) hEqual

variable [hPeriodPos : Fact (0 < period)]

theorem smoothScalar_not_finiteDimensional :
    ¬ FiniteDimensional Real (SmoothQuotientField period hPeriod Real) := by
  intro hFinite
  letI := hFinite
  letI : FiniteDimensional Real (SmoothQuotientField period hPeriod Complex) :=
    FiniteDimensional.of_injective (smoothComplexRealParts period hPeriod)
      (smoothComplexRealParts_injective period hPeriod)
  have hFourier : Module.Finite Real (Int →₀ Complex) :=
    FiniteDimensional.of_injective (finiteTemporalFourierFieldLinearMap period)
      (finiteTemporalFourierFieldLinearMap_injective period)
  rcases Module.finite_finsupp_iff.mp hFourier with hEmpty | hSub | hFiniteIndex
  · letI := hEmpty
    exact isEmptyElim (0 : Int)
  · letI := hSub
    exact zero_ne_one (Subsingleton.elim (0 : Complex) 1)
  · exact Infinite.not_finite hFiniteIndex.2

theorem smoothDiffeomorphismGhost_not_finiteDimensional :
    ¬ FiniteDimensional Real (GlobalDiffeomorphismGhostField period hPeriod) := by
  intro hFinite
  letI := hFinite
  exact smoothScalar_not_finiteDimensional period hPeriod
    (finiteDimensional_scalar_of_ghost period hPeriod)

end
end P0EFTJanusProgramPT12SmoothGhostInfiniteDimension4D
end JanusFormal
