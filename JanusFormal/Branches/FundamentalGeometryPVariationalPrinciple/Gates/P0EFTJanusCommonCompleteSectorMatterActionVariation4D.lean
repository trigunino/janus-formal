import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCommonCompleteSectorD9Variation4D

/-!
# Actual global matter action on the simultaneous six-sector variation

The action here is the existing global eight-component matter action on the
actual `IndependentFields` configuration.  The result only states its exact
dependence on the matter component of the simultaneous variation; it does not
claim that the other Program-P action sectors vanish.
-/

namespace JanusFormal
namespace P0EFTJanusCommonCompleteSectorMatterActionVariation4D

set_option autoImplicit false

noncomputable section

open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusInducedFieldVariation4D
open P0EFTJanusMappingTorusLinearizedDiffeomorphismBRST4D
open P0EFTJanusMappingTorusScalarDiffeomorphismNoetherOperator4D
open P0EFTJanusGlobalMatterMultipletActualEulerHessian4D
open P0EFTJanusCommonMatterActionVariation4D
open P0EFTJanusCommonCompleteSectorD9Variation4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Extracting the actual eight matter components from the simultaneous
six-sector curve gives exactly the established matter affine curve. -/
theorem independentMatterComponentFamily_combinedIndependentVariation
    (fields : IndependentFields period hPeriod)
    (direction : CommonSectorDirections period hPeriod)
    (parameter : Real) :
    independentMatterComponentFamily period hPeriod
        (independentFieldCurve period hPeriod fields
          (combinedIndependentVariation period hPeriod direction) parameter) =
      matterMultipletAffineCurve period hPeriod
        (independentMatterComponentFamily period hPeriod fields)
        (matterVariationComponentFamily period hPeriod direction.matter)
        parameter := by
  rw [← independentMatterComponentFamily_independentFieldCurve_matterOnly
    period hPeriod fields direction.matter parameter]
  funext component
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  rcases component with ⟨sector, component⟩
  fin_cases sector <;>
    simp [independentMatterComponentFamily, independentMatterScalar,
      selectMatterField, independentFieldCurve, combinedIndependentVariation,
      matterOnlyIndependentVariation]

/-- Along the simultaneous curve, the unchanged global matter action is
definitionally the same action evaluated along its matter-only curve. -/
theorem globalIndependentMatterAction_combinedCurve_eq_matterOnlyCurve
    (data : MatterMultipletActionData period hPeriod)
    (fields : IndependentFields period hPeriod)
    (direction : CommonSectorDirections period hPeriod)
    (parameter : Real) :
    globalIndependentMatterAction period hPeriod data
        (independentFieldCurve period hPeriod fields
          (combinedIndependentVariation period hPeriod direction) parameter) =
      globalIndependentMatterAction period hPeriod data
        (independentFieldCurve period hPeriod fields
          (matterOnlyIndependentVariation period hPeriod direction.matter)
          parameter) := by
  unfold globalIndependentMatterAction
  rw [independentMatterComponentFamily_combinedIndependentVariation]
  rw [independentMatterComponentFamily_independentFieldCurve_matterOnly]

/-- The real first derivative of the existing global matter action transports
to the same simultaneous common configuration and variation. -/
theorem globalIndependentMatterAction_combinedCurve_hasDerivAt
    (data : MatterMultipletActionData period hPeriod)
    (fields : IndependentFields period hPeriod)
    (direction : CommonSectorDirections period hPeriod) :
    HasDerivAt
      (fun parameter : Real => globalIndependentMatterAction period hPeriod data
        (independentFieldCurve period hPeriod fields
          (combinedIndependentVariation period hPeriod direction) parameter))
      (globalMatterMultipletEuler period hPeriod data
        (independentMatterComponentFamily period hPeriod fields)
        (matterVariationComponentFamily period hPeriod direction.matter)) 0 := by
  rw [show (fun parameter : Real =>
      globalIndependentMatterAction period hPeriod data
        (independentFieldCurve period hPeriod fields
          (combinedIndependentVariation period hPeriod direction) parameter)) =
      (fun parameter : Real =>
        globalIndependentMatterAction period hPeriod data
          (independentFieldCurve period hPeriod fields
            (matterOnlyIndependentVariation period hPeriod direction.matter)
            parameter)) from by
    funext parameter
    exact globalIndependentMatterAction_combinedCurve_eq_matterOnlyCurve
      period hPeriod data fields direction parameter]
  exact globalIndependentMatterAction_matterOnlyCurve_hasDerivAt period hPeriod
    data fields direction.matter

/-- For this same global matter action, equal matter directions give identical
curves regardless of metric, gauge, ghost, auxiliary, and LL directions. -/
theorem globalIndependentMatterAction_combinedCurve_independent_other_sectors
    (data : MatterMultipletActionData period hPeriod)
    (fields : IndependentFields period hPeriod)
    (first second : CommonSectorDirections period hPeriod)
    (hMatter : first.matter = second.matter)
    (parameter : Real) :
    globalIndependentMatterAction period hPeriod data
        (independentFieldCurve period hPeriod fields
          (combinedIndependentVariation period hPeriod first) parameter) =
      globalIndependentMatterAction period hPeriod data
        (independentFieldCurve period hPeriod fields
          (combinedIndependentVariation period hPeriod second) parameter) := by
  rw [globalIndependentMatterAction_combinedCurve_eq_matterOnlyCurve,
    globalIndependentMatterAction_combinedCurve_eq_matterOnlyCurve, hMatter]

end

end P0EFTJanusCommonCompleteSectorMatterActionVariation4D
end JanusFormal
