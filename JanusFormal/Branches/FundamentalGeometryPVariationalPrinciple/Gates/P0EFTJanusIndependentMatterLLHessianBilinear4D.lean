import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusIndependentFieldVariationLinearSpace4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCompleteVariationMatterLLActionHessian4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusPTSymmetricLLWeakEulerJacobiOperator4D

/-!
# The matter--LL Hessian as a bilinear form on the common tangent

The existing second-variation theorem already uses the same independent
variation record as the complete Program-P action curve.  This gate bundles
that Hessian as an actual real bilinear map on that record.  It remains the
matter plus differential-LL sector; no Einstein--Hilbert or Maxwell term is
added here.
-/

namespace JanusFormal
namespace P0EFTJanusIndependentMatterLLHessianBilinear4D

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
open P0EFTJanusCommonMatterActionVariation4D
open P0EFTJanusMappingTorusScalarDiffeomorphismNoetherOperator4D
open P0EFTJanusGlobalMatterMultipletActualEulerHessian4D
open P0EFTJanusCompleteVariationMatterLLActionHessian4D
open P0EFTJanusCommonCompleteSectorD9Variation4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLHessian4D
open P0EFTJanusMappingTorusPTSymmetricLLWeakEulerJacobiOperator4D
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

/-- Extraction of the eight real matter components is linear on the genuine
common independent tangent record. -/
def independentMatterComponentLinearMap :
    IndependentFieldVariation period hPeriod →ₗ[Real]
      MatterComponentFamily period hPeriod where
  toFun variation :=
    matterVariationComponentFamily period hPeriod variation.matter
  map_add' first second := by
    funext component
    ext point
    unfold matterVariationComponentFamily
    by_cases h : component.1 = 0
    · simp only [h, if_true, Pi.add_apply]
      exact map_add (EuclideanSpace.proj component.2) _ _
    · simp only [h, if_false, Pi.add_apply]
      exact map_add (EuclideanSpace.proj component.2) _ _
  map_smul' scalar variation := by
    funext component
    ext point
    unfold matterVariationComponentFamily
    by_cases h : component.1 = 0
    · simp only [h, if_true, Pi.smul_apply]
      exact map_smul (EuclideanSpace.proj component.2) scalar _
    · simp only [h, if_false, Pi.smul_apply]
      exact map_smul (EuclideanSpace.proj component.2) scalar _

/-- The already proved eight-component Jacobi pairing, bundled in both
arguments rather than stored as a proposition-valued certificate. -/
def matterMultipletHessianBilinear
    (data : MatterMultipletActionData period hPeriod) :
    MatterComponentFamily period hPeriod →ₗ[Real]
      MatterComponentFamily period hPeriod →ₗ[Real] Real where
  toFun first :=
    { toFun := fun second =>
        globalMatterMultipletHessian period hPeriod data first second
      map_add' := by
        intro second third
        unfold globalMatterMultipletHessian
        simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]
      map_smul' := by
        intro scalar second
        unfold globalMatterMultipletHessian
        simp only [Pi.smul_apply, map_smul, RingHom.id_apply, smul_eq_mul,
          Finset.mul_sum] }
  map_add' first second := by
    apply LinearMap.ext
    intro third
    change globalMatterMultipletHessian period hPeriod data (first + second) third =
      globalMatterMultipletHessian period hPeriod data first third +
        globalMatterMultipletHessian period hPeriod data second third
    unfold globalMatterMultipletHessian
    simp only [Pi.add_apply, map_add, LinearMap.add_apply,
      Finset.sum_add_distrib]
  map_smul' scalar first := by
    apply LinearMap.ext
    intro second
    change globalMatterMultipletHessian period hPeriod data (scalar • first) second =
      scalar • globalMatterMultipletHessian period hPeriod data first second
    unfold globalMatterMultipletHessian
    simp only [Pi.smul_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
      Finset.mul_sum]

/-- Pull back a genuine bilinear form along one linear field projection. -/
def pullbackBilinear {V W : Type*} [AddCommGroup V] [Module Real V]
    [AddCommGroup W] [Module Real W]
    (projection : V →ₗ[Real] W) (form : W →ₗ[Real] W →ₗ[Real] Real) :
    V →ₗ[Real] V →ₗ[Real] Real where
  toFun first := (form (projection first)).comp projection
  map_add' first second := by
    ext third
    simp only [map_add, LinearMap.add_apply, LinearMap.comp_apply]
  map_smul' scalar first := by
    ext second
    simp only [map_smul, LinearMap.smul_apply, LinearMap.comp_apply,
      RingHom.id_apply]

/-- Matter Hessian on the exact common independent tangent. -/
def independentMatterHessianBilinear
    (data : MatterMultipletActionData period hPeriod) :
    IndependentFieldVariation period hPeriod →ₗ[Real]
      IndependentFieldVariation period hPeriod →ₗ[Real] Real :=
  pullbackBilinear
    (independentMatterComponentLinearMap period hPeriod)
    (matterMultipletHessianBilinear period hPeriod data)

/-- Differential-LL Hessian on the same common independent tangent. -/
def independentLLHessianBilinear
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    IndependentFieldVariation period hPeriod →ₗ[Real]
      IndependentFieldVariation period hPeriod →ₗ[Real] Real :=
  pullbackBilinear
    (independentLLFieldVariationLinearMap period hPeriod)
    (weakLLJacobiOperator period hPeriod frame fields mu)

/-- The actual matter plus LL Hessian is one bilinear form on the same tangent
record consumed by the complete action curve. -/
def independentMatterLLHessianBilinear
    (data : MatterMultipletActionData period hPeriod)
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    IndependentFieldVariation period hPeriod →ₗ[Real]
      IndependentFieldVariation period hPeriod →ₗ[Real] Real :=
  independentMatterHessianBilinear period hPeriod data +
    independentLLHessianBilinear period hPeriod frame fields mu

@[simp] theorem independentMatterLLHessianBilinear_apply
    (data : MatterMultipletActionData period hPeriod)
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu]
    (first second : IndependentFieldVariation period hPeriod) :
    independentMatterLLHessianBilinear period hPeriod data frame fields mu
        first second =
      completeVariationMatterLLHessian period hPeriod data frame fields
        (independentCompleteVariation period hPeriod first)
        (independentCompleteVariation period hPeriod second) mu :=
  rfl

theorem independentMatterLLHessianBilinear_symmetric
    (data : MatterMultipletActionData period hPeriod)
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu]
    (first second : IndependentFieldVariation period hPeriod) :
    independentMatterLLHessianBilinear period hPeriod data frame fields mu
        first second =
      independentMatterLLHessianBilinear period hPeriod data frame fields mu
        second first := by
  simp only [independentMatterLLHessianBilinear_apply,
    completeVariationMatterLLHessian_on_independent]
  rw [globalMatterMultipletHessian_symmetric]
  rw [globalPTSymmetricDifferentialLLFluxHessian_comm]

/-- On the already constructed six-sector combined directions, this bundled
form is exactly the mixed second derivative of the unchanged action curve. -/
theorem independentMatterLLHessianBilinear_is_secondVariation_on_combined
    (data : MatterMultipletActionData period hPeriod)
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (first second : CommonSectorDirections period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    HasDerivAt
      ((fun parameter => globalMatterMultipletEuler period hPeriod data
          (independentMatterComponentFamily period hPeriod
            (independentFieldCurve period hPeriod fields
              (combinedIndependentVariation period hPeriod first) parameter))
          (matterVariationComponentFamily period hPeriod second.matter)) +
        (fun parameter =>
          globalPTSymmetricDifferentialLLFluxFirstVariation period hPeriod frame
            (independentFieldCurve period hPeriod fields
              (combinedIndependentVariation period hPeriod first) parameter)
            second.ll mu))
      (independentMatterLLHessianBilinear period hPeriod data frame fields mu
        (combinedIndependentVariation period hPeriod first)
        (combinedIndependentVariation period hPeriod second)) 0 := by
  simpa only [independentMatterLLHessianBilinear_apply,
    completeVariationMatterLLHessian_on_independent,
    combinedIndependentVariation] using
    completeVariationMatterLLFirstVariation_combined_hasDerivAt period hPeriod
      data frame fields first second mu

end
end P0EFTJanusIndependentMatterLLHessianBilinear4D
end JanusFormal
