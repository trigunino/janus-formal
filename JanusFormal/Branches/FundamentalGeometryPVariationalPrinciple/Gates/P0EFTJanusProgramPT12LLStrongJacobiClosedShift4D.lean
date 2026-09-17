import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12LLStrongJacobiClosedLowerBound4D

/-! Positive scalar shifts of the closed LL Jacobi operator. -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12LLStrongJacobiClosedShift4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff ENNReal LinearPMap
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusPTSymmetricLLWeakEulerJacobiOperator4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusProgramPT12LLStrongJacobiClosure4D
open P0EFTJanusProgramPT12LLStrongJacobiClosedLowerBound4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance :
    IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance : CompactSpace (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod

local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _

local instance : BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

local instance :
    IsFiniteMeasure (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod

private abbrev LLFieldL2 :=
  Lp LLFieldFiber (2 : ENNReal)
    (intrinsicCanonicalThroatVolumeMeasure period hPeriod)

/-- The scalar shift acts on exactly the closed Jacobi domain. -/
def llJacobiShiftedPMap (fields : IndependentFields period hPeriod) (shift : Real) :
    LLFieldL2 period hPeriod →ₗ.[Real] LLFieldL2 period hPeriod :=
  let C := llJacobiClosedPMap period hPeriod fields
  ⟨C.domain, C.toFun + shift • C.domain.subtype⟩

theorem llJacobiShiftedPMap_domain (fields : IndependentFields period hPeriod)
    (shift : Real) :
    (llJacobiShiftedPMap period hPeriod fields shift).domain =
      (llJacobiClosedPMap period hPeriod fields).domain := rfl

theorem llJacobiShiftedPMap_apply (fields : IndependentFields period hPeriod)
    (shift : Real) (x : (llJacobiClosedPMap period hPeriod fields).domain) :
    llJacobiShiftedPMap period hPeriod fields shift x =
      llJacobiClosedPMap period hPeriod fields x +
        shift • (x : LLFieldL2 period hPeriod) := by
  simp [llJacobiShiftedPMap]

/-- Any shift beyond the semiboundedness constant is coercive on the same domain. -/
theorem llJacobiShiftedPMap_coercive (fields : IndependentFields period hPeriod) :
    ∃ constant : Real, 0 ≤ constant ∧
      ∀ (shift : Real), constant < shift →
        ∀ x : (llJacobiShiftedPMap period hPeriod fields shift).domain,
          (shift - constant) * ‖(x : LLFieldL2 period hPeriod)‖ ^ 2 ≤
            inner Real (llJacobiShiftedPMap period hPeriod fields shift x)
              (x : LLFieldL2 period hPeriod) := by
  obtain ⟨constant, hNonnegative, hLower⟩ :=
    llJacobiClosedPMap_l2_lower_bound period hPeriod fields
  refine ⟨constant, hNonnegative, ?_⟩
  intro shift hShift x
  have hBase := hLower x
  rw [llJacobiShiftedPMap_apply]
  rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
  nlinarith

end
end P0EFTJanusProgramPT12LLStrongJacobiClosedShift4D
end JanusFormal
