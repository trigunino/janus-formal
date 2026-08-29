import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntrinsicMetricBVThroatBracket4D

/-!
# Linear module of smooth symmetric throat tensors

The throat BV layer already had pointwise zero, addition, and scalar
multiplication, but no bundled linear-space instances.  This gate packages
the same operations as an additive commutative group and real module.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPThroatMetricTensorModule4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusReflectionFixedThroat
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothThroatEmbedding
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVThroatBoundary4D
open P0EFTJanusMappingTorusIntrinsicMetricBVThroatBracket4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

private abbrev ThroatTensor :=
  SmoothSymmetricThroatCovariantTwoTensor period hPeriod

private theorem throatTensor_ext_pointwise
    {first second : ThroatTensor period hPeriod}
    (h : ∀ point x y,
      first.tensor point x y = second.tensor point x y) :
    first = second := by
  apply SmoothSymmetricThroatCovariantTwoTensor.ext
  apply ContMDiffSection.ext
  intro point
  apply ContinuousLinearMap.ext
  intro x
  apply ContinuousLinearMap.ext
  intro y
  exact h point x y

instance : Zero (ThroatTensor period hPeriod) where
  zero :=
    { tensor := 0
      symmetric := by intro point first second; rfl }

instance : Add (ThroatTensor period hPeriod) where
  add := smoothSymmetricThroatTensorAdd period hPeriod

instance : Neg (ThroatTensor period hPeriod) where
  neg tensor :=
    { tensor := -tensor.tensor
      symmetric := by
        intro point first second
        change -tensor.tensor point first second =
          -tensor.tensor point second first
        rw [tensor.symmetric] }

instance : Sub (ThroatTensor period hPeriod) where
  sub first second := first + -second

instance : AddCommGroup (ThroatTensor period hPeriod) where
  add_assoc first second third := by
    apply throatTensor_ext_pointwise
    intro point x y
    change (first.tensor point x y + second.tensor point x y) +
      third.tensor point x y =
        first.tensor point x y +
          (second.tensor point x y + third.tensor point x y)
    ring
  zero_add tensor := by
    apply throatTensor_ext_pointwise
    intro point x y
    change 0 + tensor.tensor point x y = tensor.tensor point x y
    ring
  add_zero tensor := by
    apply throatTensor_ext_pointwise
    intro point x y
    change tensor.tensor point x y + 0 = tensor.tensor point x y
    ring
  nsmul := nsmulRec
  add_comm first second := by
    apply throatTensor_ext_pointwise
    intro point x y
    change first.tensor point x y + second.tensor point x y =
      second.tensor point x y + first.tensor point x y
    ring
  neg_add_cancel tensor := by
    apply throatTensor_ext_pointwise
    intro point x y
    change -tensor.tensor point x y + tensor.tensor point x y = 0
    ring
  sub_eq_add_neg first second := rfl
  zsmul := zsmulRec

instance : SMul Real (ThroatTensor period hPeriod) where
  smul := smoothSymmetricThroatTensorSMul period hPeriod

instance : Module Real (ThroatTensor period hPeriod) where
  one_smul tensor := by
    apply throatTensor_ext_pointwise
    intro point x y
    change (1 : Real) * tensor.tensor point x y = tensor.tensor point x y
    ring
  mul_smul first second tensor := by
    apply throatTensor_ext_pointwise
    intro point x y
    change (first * second) * tensor.tensor point x y =
      first * (second * tensor.tensor point x y)
    ring
  smul_add scalar first second := by
    apply throatTensor_ext_pointwise
    intro point x y
    change scalar * (first.tensor point x y + second.tensor point x y) =
      scalar * first.tensor point x y +
        scalar * second.tensor point x y
    ring
  smul_zero scalar := by
    apply throatTensor_ext_pointwise
    intro point x y
    change scalar * 0 = (0 : Real)
    ring
  add_smul first second tensor := by
    apply throatTensor_ext_pointwise
    intro point x y
    change (first + second) * tensor.tensor point x y =
      first * tensor.tensor point x y +
        second * tensor.tensor point x y
    ring
  zero_smul tensor := by
    apply throatTensor_ext_pointwise
    intro point x y
    change (0 : Real) * tensor.tensor point x y = 0
    ring

@[simp]
theorem smoothThroatGeneralMetricTensorPair_add_eq
    (first second :
      SmoothThroatGeneralMetricTensorPair period hPeriod) :
    first + second =
      smoothThroatGeneralMetricTensorPairAdd
        period hPeriod first second :=
  rfl

@[simp]
theorem smoothThroatGeneralMetricTensorPair_smul_eq
    (scalar : Real)
    (tensor : SmoothThroatGeneralMetricTensorPair period hPeriod) :
    scalar • tensor =
      smoothThroatGeneralMetricTensorPairSMul
        period hPeriod scalar tensor :=
  rfl

end
end P0EFTJanusProgramPThroatMetricTensorModule4D
end JanusFormal
