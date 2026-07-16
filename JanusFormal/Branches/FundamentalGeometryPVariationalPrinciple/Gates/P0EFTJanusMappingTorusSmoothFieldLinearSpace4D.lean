import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusSmoothThroatTrace4D

/-!
# Linear spaces of smooth D8 and throat fields

The smooth coefficient-field structures inherit their pointwise real vector
space operations. Restriction to the throat and PT pullback are linear maps.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusSmoothFieldLinearSpace4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothPTFieldAction4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D

variable (period : Real) (hPeriod : Not (period = 0))

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev throatData := fixedEquatorData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)
private abbrev EffectiveThroat := MappingTorus (throatData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

universe u

variable (Fiber : Type u)
  [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]

instance : Zero (SmoothQuotientField period hPeriod Fiber) where
  zero := ⟨fun _ => 0, contMDiff_const⟩

instance : Add (SmoothQuotientField period hPeriod Fiber) where
  add first second :=
    ⟨fun point => first point + second point,
      first.contMDiff_toFun.add second.contMDiff_toFun⟩

instance : Neg (SmoothQuotientField period hPeriod Fiber) where
  neg field := ⟨fun point => -field point, field.contMDiff_toFun.neg⟩

instance : Sub (SmoothQuotientField period hPeriod Fiber) where
  sub first second :=
    ⟨fun point => first point - second point,
      first.contMDiff_toFun.sub second.contMDiff_toFun⟩

instance : AddCommGroup (SmoothQuotientField period hPeriod Fiber) where
  add_assoc := by intro first second third; ext point; exact add_assoc _ _ _
  zero_add := by intro field; ext point; exact zero_add _
  add_zero := by intro field; ext point; exact add_zero _
  nsmul := nsmulRec
  add_comm := by intro first second; ext point; exact add_comm _ _
  neg_add_cancel := by intro field; ext point; exact neg_add_cancel _
  sub_eq_add_neg := by intro first second; ext point; exact sub_eq_add_neg _ _
  zsmul := zsmulRec

instance : SMul Real (SmoothQuotientField period hPeriod Fiber) where
  smul scalar field :=
    ⟨fun point => scalar • field point,
      contMDiff_const.smul (I := 𝓘(Real)) field.contMDiff_toFun⟩

@[simp] theorem smoothQuotientField_smul_apply
    (scalar : Real) (field : SmoothQuotientField period hPeriod Fiber)
    (point : EffectiveQuotient period hPeriod) :
    (scalar • field) point = scalar • field point := rfl

instance : Module Real (SmoothQuotientField period hPeriod Fiber) where
  one_smul := by intro field; ext point; exact one_smul _ _
  mul_smul := by intro first second field; ext point; exact mul_smul _ _ _
  smul_add := by intro scalar first second; ext point; exact smul_add _ _ _
  smul_zero := by intro scalar; ext point; exact smul_zero _
  add_smul := by intro first second field; ext point; exact add_smul _ _ _
  zero_smul := by intro field; ext point; exact zero_smul _ _

instance : Zero (SmoothThroatField period hPeriod Fiber) where
  zero := ⟨fun _ => 0, contMDiff_const⟩

instance : Add (SmoothThroatField period hPeriod Fiber) where
  add first second :=
    ⟨fun point => first point + second point,
      first.contMDiff_toFun.add second.contMDiff_toFun⟩

instance : Neg (SmoothThroatField period hPeriod Fiber) where
  neg field := ⟨fun point => -field point, field.contMDiff_toFun.neg⟩

instance : Sub (SmoothThroatField period hPeriod Fiber) where
  sub first second :=
    ⟨fun point => first point - second point,
      first.contMDiff_toFun.sub second.contMDiff_toFun⟩

instance : AddCommGroup (SmoothThroatField period hPeriod Fiber) where
  add_assoc := by intro first second third; ext point; exact add_assoc _ _ _
  zero_add := by intro field; ext point; exact zero_add _
  add_zero := by intro field; ext point; exact add_zero _
  nsmul := nsmulRec
  add_comm := by intro first second; ext point; exact add_comm _ _
  neg_add_cancel := by intro field; ext point; exact neg_add_cancel _
  sub_eq_add_neg := by intro first second; ext point; exact sub_eq_add_neg _ _
  zsmul := zsmulRec

instance : SMul Real (SmoothThroatField period hPeriod Fiber) where
  smul scalar field :=
    ⟨fun point => scalar • field point,
      contMDiff_const.smul (I := 𝓘(Real)) field.contMDiff_toFun⟩

instance : Module Real (SmoothThroatField period hPeriod Fiber) where
  one_smul := by intro field; ext point; exact one_smul _ _
  mul_smul := by intro first second field; ext point; exact mul_smul _ _ _
  smul_add := by intro scalar first second; ext point; exact smul_add _ _ _
  smul_zero := by intro scalar; ext point; exact smul_zero _
  add_smul := by intro first second field; ext point; exact add_smul _ _ _
  zero_smul := by intro field; ext point; exact zero_smul _ _

/-- Smooth restriction to the actual throat is linear. -/
def throatTraceLinearMap :
    SmoothQuotientField period hPeriod Fiber →ₗ[Real]
      SmoothThroatField period hPeriod Fiber where
  toFun := throatTrace period hPeriod Fiber
  map_add' first second := rfl
  map_smul' scalar field := rfl

/-- PT pullback on spacetime smooth fields is linear. -/
def ptPullbackLinearMap :
    SmoothQuotientField period hPeriod Fiber →ₗ[Real]
      SmoothQuotientField period hPeriod Fiber where
  toFun := ptPullback period hPeriod Fiber
  map_add' first second := rfl
  map_smul' scalar field := rfl

/-- PT pullback on smooth throat fields is linear. -/
def throatPTPullbackLinearMap :
    SmoothThroatField period hPeriod Fiber →ₗ[Real]
      SmoothThroatField period hPeriod Fiber where
  toFun := throatPTPullback period hPeriod Fiber
  map_add' first second := rfl
  map_smul' scalar field := rfl

theorem throatTraceLinearMap_pt_intertwines :
    (throatTraceLinearMap period hPeriod Fiber).comp
        (ptPullbackLinearMap period hPeriod Fiber) =
      (throatPTPullbackLinearMap period hPeriod Fiber).comp
        (throatTraceLinearMap period hPeriod Fiber) := by
  ext field point
  exact congrArg (fun traced => traced point)
    (throatTrace_pt_equivariant period hPeriod Fiber field)

end

end P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
end JanusFormal
