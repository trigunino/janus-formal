import Mathlib.LinearAlgebra.Prod
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9MatterSpinorDoubledIntrinsicDiracOperator4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPThroatMatterSpinorSectionLinearSpace4D

/-!
# Linear smooth core of the intrinsic doubled D9 Dirac operator

The doubled smooth section space is the product of the two opposite normal
root sectors.  This gate transports its real module structure, proves that
the intrinsic geometric Dirac operator is linear, and packages its square,
mass shift, and exact smooth graph.

No Hilbert completion or closed unbounded realization is asserted here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD9MatterSpinorDoubledIntrinsicDiracLinearCore4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusProgramPThroatMatterSpinorSectionSpace4D
open P0EFTJanusProgramPThroatMatterSpinorSectionLinearSpace4D
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothSectionDescent4D
open P0EFTJanusProgramPD9MatterSpinorFlatCoverConnection4D
open P0EFTJanusProgramPD9MatterSpinorDoubledFlatCoverConnection4D
open P0EFTJanusProgramPD9MatterSpinorDoubledCliffordConnectionCompatibility4D
open P0EFTJanusProgramPD9MatterSpinorDoubledIntrinsicDiracOperator4D
open P0EFTJanusNormalPinLiftBoundaryConditions

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev ThroatData := fixedEquatorData period hPeriod
private abbrev ThroatCover := MappingTorusCover (ThroatData period hPeriod)

local instance throatCoverChartedSpace :
    ChartedSpace ThroatCoverModel (ThroatCover period hPeriod) :=
  fixedThroatCoverChartedSpace period hPeriod

local instance throatCoverIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (ThroatCover period hPeriod) :=
  fixedThroatCover_isManifold period hPeriod

/-- The doubled lift is exactly the product of its two opposite-root
components. -/
def smoothThroatDoubledMatterSpinorLiftEquiv
    (choice : NormalRootChoice) :
    SmoothThroatDoubledMatterSpinorLift period hPeriod choice ≃
      SmoothThroatMatterSpinorLift period hPeriod choice ×
        SmoothThroatMatterSpinorLift
          period hPeriod (oppositeRoot choice) where
  toFun lift := (lift.first, lift.second)
  invFun pair := ⟨pair.1, pair.2⟩
  left_inv lift := by cases lift; rfl
  right_inv pair := by cases pair; rfl

instance doubledMatterSpinorLiftAddCommGroup
    (choice : NormalRootChoice) :
    AddCommGroup
      (SmoothThroatDoubledMatterSpinorLift
        period hPeriod choice) :=
  Equiv.addCommGroup
    (smoothThroatDoubledMatterSpinorLiftEquiv
      period hPeriod choice)

instance doubledMatterSpinorLiftModule
    (choice : NormalRootChoice) :
    Module Real
      (SmoothThroatDoubledMatterSpinorLift
        period hPeriod choice) :=
  Equiv.module Real
    (smoothThroatDoubledMatterSpinorLiftEquiv
      period hPeriod choice)

@[simp]
theorem doubledMatterSpinorLift_add_apply
    (choice : NormalRootChoice)
    (first second : SmoothThroatDoubledMatterSpinorLift
      period hPeriod choice)
    (point : ThroatCover period hPeriod) :
    (first + second) point = first point + second point := by
  rfl

@[simp]
theorem doubledMatterSpinorLift_smul_apply
    (choice : NormalRootChoice) (scalar : Real)
    (lift : SmoothThroatDoubledMatterSpinorLift
      period hPeriod choice)
    (point : ThroatCover period hPeriod) :
    (scalar • lift) point = scalar • lift point := by
  rfl

theorem smoothThroatDoubledMatterSpinorLift_ext
    (choice : NormalRootChoice)
    {first second : SmoothThroatDoubledMatterSpinorLift
      period hPeriod choice}
    (hEqual : ∀ point, first point = second point) :
    first = second := by
  have hFirst : first.first = second.first := by
    apply SmoothThroatMatterSpinorLift.ext
    intro point
    exact congrArg Prod.fst (hEqual point)
  have hSecond : first.second = second.second := by
    apply SmoothThroatMatterSpinorLift.ext
    intro point
    exact congrArg Prod.snd (hEqual point)
  cases first
  cases second
  simp_all

/-- The intrinsic frame derivative is additive in the doubled section. -/
theorem d9IntrinsicDoubledMatterFlatFrameDerivative_add
    (choice : NormalRootChoice)
    (first second : SmoothThroatDoubledMatterSpinorLift
      period hPeriod choice)
    (direction : Fin 3) (point : ThroatCover period hPeriod) :
    d9IntrinsicDoubledMatterFlatFrameDerivative
        period hPeriod choice (first + second) direction point =
      d9IntrinsicDoubledMatterFlatFrameDerivative
          period hPeriod choice first direction point +
        d9IntrinsicDoubledMatterFlatFrameDerivative
          period hPeriod choice second direction point := by
  unfold d9IntrinsicDoubledMatterFlatFrameDerivative
  apply Prod.ext
  · change
      d9MatterSpinorFlatCoverDerivative period hPeriod choice
          (first.first + second.first) point
          (d9IntrinsicThroatCoverFrame
            period hPeriod direction point) =
        d9MatterSpinorFlatCoverDerivative period hPeriod choice
            first.first point
            (d9IntrinsicThroatCoverFrame
              period hPeriod direction point) +
          d9MatterSpinorFlatCoverDerivative period hPeriod choice
            second.first point
            (d9IntrinsicThroatCoverFrame
              period hPeriod direction point)
    unfold d9MatterSpinorFlatCoverDerivative
    change
      mvfderiv throatCoverModelWithCorners
          (first.first.toFun + second.first.toFun) point
          (d9IntrinsicThroatCoverFrame
            period hPeriod direction point) = _
    rw [mvfderiv_add
      (first.first.contMDiff_toFun.mdifferentiableAt (by simp))
      (second.first.contMDiff_toFun.mdifferentiableAt (by simp))]
    rfl
  · change
      d9MatterSpinorFlatCoverDerivative period hPeriod
          (oppositeRoot choice) (first.second + second.second) point
          (d9IntrinsicThroatCoverFrame
            period hPeriod direction point) =
        d9MatterSpinorFlatCoverDerivative period hPeriod
            (oppositeRoot choice) first.second point
            (d9IntrinsicThroatCoverFrame
              period hPeriod direction point) +
          d9MatterSpinorFlatCoverDerivative period hPeriod
            (oppositeRoot choice) second.second point
            (d9IntrinsicThroatCoverFrame
              period hPeriod direction point)
    unfold d9MatterSpinorFlatCoverDerivative
    change
      mvfderiv throatCoverModelWithCorners
          (first.second.toFun + second.second.toFun) point
          (d9IntrinsicThroatCoverFrame
            period hPeriod direction point) = _
    rw [mvfderiv_add
      (first.second.contMDiff_toFun.mdifferentiableAt (by simp))
      (second.second.contMDiff_toFun.mdifferentiableAt (by simp))]
    rfl

/-- The intrinsic frame derivative is homogeneous in the doubled section. -/
theorem d9IntrinsicDoubledMatterFlatFrameDerivative_smul
    (choice : NormalRootChoice) (scalar : Real)
    (lift : SmoothThroatDoubledMatterSpinorLift
      period hPeriod choice)
    (direction : Fin 3) (point : ThroatCover period hPeriod) :
    d9IntrinsicDoubledMatterFlatFrameDerivative
        period hPeriod choice (scalar • lift) direction point =
      scalar •
        d9IntrinsicDoubledMatterFlatFrameDerivative
          period hPeriod choice lift direction point := by
  unfold d9IntrinsicDoubledMatterFlatFrameDerivative
  apply Prod.ext
  · change
      d9MatterSpinorFlatCoverDerivative period hPeriod choice
          (scalar • lift.first) point
          (d9IntrinsicThroatCoverFrame
            period hPeriod direction point) =
        scalar •
          d9MatterSpinorFlatCoverDerivative period hPeriod choice
            lift.first point
            (d9IntrinsicThroatCoverFrame
              period hPeriod direction point)
    unfold d9MatterSpinorFlatCoverDerivative
    change
      mvfderiv throatCoverModelWithCorners
          (scalar • lift.first.toFun) point
          (d9IntrinsicThroatCoverFrame
            period hPeriod direction point) = _
    unfold mvfderiv
    rw [const_smul_mfderiv
      (lift.first.contMDiff_toFun.mdifferentiableAt (by simp)) scalar]
    rfl
  · change
      d9MatterSpinorFlatCoverDerivative period hPeriod
          (oppositeRoot choice) (scalar • lift.second) point
          (d9IntrinsicThroatCoverFrame
            period hPeriod direction point) =
        scalar •
          d9MatterSpinorFlatCoverDerivative period hPeriod
            (oppositeRoot choice) lift.second point
            (d9IntrinsicThroatCoverFrame
              period hPeriod direction point)
    unfold d9MatterSpinorFlatCoverDerivative
    change
      mvfderiv throatCoverModelWithCorners
          (scalar • lift.second.toFun) point
          (d9IntrinsicThroatCoverFrame
            period hPeriod direction point) = _
    unfold mvfderiv
    rw [const_smul_mfderiv
      (lift.second.contMDiff_toFun.mdifferentiableAt (by simp)) scalar]
    rfl

/-- The intrinsic cover Dirac contraction is additive. -/
theorem d9IntrinsicDoubledMatterSpinorCoverDirac_add
    (choice : NormalRootChoice)
    (first second : SmoothThroatDoubledMatterSpinorLift
      period hPeriod choice)
    (point : ThroatCover period hPeriod) :
    d9IntrinsicDoubledMatterSpinorCoverDirac
        period hPeriod choice (first + second) point =
      d9IntrinsicDoubledMatterSpinorCoverDirac
          period hPeriod choice first point +
        d9IntrinsicDoubledMatterSpinorCoverDirac
          period hPeriod choice second point := by
  unfold d9IntrinsicDoubledMatterSpinorCoverDirac
  calc
    _ = ∑ direction : Fin 3,
        (d9DoubledMatterFiberCliffordGammaCLM direction
          (d9IntrinsicDoubledMatterFlatFrameDerivative
            period hPeriod choice first direction point) +
        d9DoubledMatterFiberCliffordGammaCLM direction
          (d9IntrinsicDoubledMatterFlatFrameDerivative
            period hPeriod choice second direction point)) := by
      apply Finset.sum_congr rfl
      intro direction _
      rw [d9IntrinsicDoubledMatterFlatFrameDerivative_add, map_add]
    _ = _ := Finset.sum_add_distrib

/-- The intrinsic cover Dirac contraction is homogeneous. -/
theorem d9IntrinsicDoubledMatterSpinorCoverDirac_smul
    (choice : NormalRootChoice) (scalar : Real)
    (lift : SmoothThroatDoubledMatterSpinorLift
      period hPeriod choice)
    (point : ThroatCover period hPeriod) :
    d9IntrinsicDoubledMatterSpinorCoverDirac
        period hPeriod choice (scalar • lift) point =
      scalar •
        d9IntrinsicDoubledMatterSpinorCoverDirac
          period hPeriod choice lift point := by
  unfold d9IntrinsicDoubledMatterSpinorCoverDirac
  calc
    _ = ∑ direction : Fin 3,
        scalar •
          d9DoubledMatterFiberCliffordGammaCLM direction
            (d9IntrinsicDoubledMatterFlatFrameDerivative
              period hPeriod choice lift direction point) := by
      apply Finset.sum_congr rfl
      intro direction _
      rw [d9IntrinsicDoubledMatterFlatFrameDerivative_smul, map_smul]
    _ = _ := by rw [Finset.smul_sum]

theorem d9IntrinsicDoubledMatterSpinorDiracOperator_add
    (choice : NormalRootChoice)
    (first second : SmoothThroatDoubledMatterSpinorLift
      period hPeriod choice) :
    d9IntrinsicDoubledMatterSpinorDiracOperator
        period hPeriod choice (first + second) =
      d9IntrinsicDoubledMatterSpinorDiracOperator
          period hPeriod choice first +
        d9IntrinsicDoubledMatterSpinorDiracOperator
          period hPeriod choice second := by
  apply smoothThroatDoubledMatterSpinorLift_ext
  intro point
  exact d9IntrinsicDoubledMatterSpinorCoverDirac_add
    period hPeriod choice first second point

theorem d9IntrinsicDoubledMatterSpinorDiracOperator_smul
    (choice : NormalRootChoice) (scalar : Real)
    (lift : SmoothThroatDoubledMatterSpinorLift
      period hPeriod choice) :
    d9IntrinsicDoubledMatterSpinorDiracOperator
        period hPeriod choice (scalar • lift) =
      scalar •
        d9IntrinsicDoubledMatterSpinorDiracOperator
          period hPeriod choice lift := by
  apply smoothThroatDoubledMatterSpinorLift_ext
  intro point
  exact d9IntrinsicDoubledMatterSpinorCoverDirac_smul
    period hPeriod choice scalar lift point

/-- Intrinsic Dirac operator as a genuine real linear map on its smooth
core. -/
def d9IntrinsicDoubledMatterSpinorDiracLinearMap
    (choice : NormalRootChoice) :
    SmoothThroatDoubledMatterSpinorLift period hPeriod choice →ₗ[Real]
      SmoothThroatDoubledMatterSpinorLift period hPeriod choice where
  toFun :=
    d9IntrinsicDoubledMatterSpinorDiracOperator
      period hPeriod choice
  map_add' :=
    d9IntrinsicDoubledMatterSpinorDiracOperator_add
      period hPeriod choice
  map_smul' :=
    d9IntrinsicDoubledMatterSpinorDiracOperator_smul
      period hPeriod choice

@[simp]
theorem d9IntrinsicDoubledMatterSpinorDiracLinearMap_apply
    (choice : NormalRootChoice)
    (lift : SmoothThroatDoubledMatterSpinorLift
      period hPeriod choice) :
    d9IntrinsicDoubledMatterSpinorDiracLinearMap
        period hPeriod choice lift =
      d9IntrinsicDoubledMatterSpinorDiracOperator
        period hPeriod choice lift :=
  rfl

/-- Smooth-core square of the intrinsic Dirac operator. -/
def d9IntrinsicDoubledMatterSpinorDiracSquaredLinearMap
    (choice : NormalRootChoice) :
    SmoothThroatDoubledMatterSpinorLift period hPeriod choice →ₗ[Real]
      SmoothThroatDoubledMatterSpinorLift period hPeriod choice :=
  (d9IntrinsicDoubledMatterSpinorDiracLinearMap
    period hPeriod choice).comp
    (d9IntrinsicDoubledMatterSpinorDiracLinearMap
      period hPeriod choice)

@[simp]
theorem d9IntrinsicDoubledMatterSpinorDiracSquaredLinearMap_apply
    (choice : NormalRootChoice)
    (lift : SmoothThroatDoubledMatterSpinorLift
      period hPeriod choice) :
    d9IntrinsicDoubledMatterSpinorDiracSquaredLinearMap
        period hPeriod choice lift =
      d9IntrinsicDoubledMatterSpinorDiracOperator
        period hPeriod choice
        (d9IntrinsicDoubledMatterSpinorDiracOperator
          period hPeriod choice lift) :=
  rfl

/-- Positive-sign smooth-core Laplace-type convention `-D² + m²`. -/
def d9IntrinsicDoubledMatterSpinorMassiveLaplaceLinearMap
    (choice : NormalRootChoice) (massSquared : Real) :
    SmoothThroatDoubledMatterSpinorLift period hPeriod choice →ₗ[Real]
      SmoothThroatDoubledMatterSpinorLift period hPeriod choice :=
  -(d9IntrinsicDoubledMatterSpinorDiracSquaredLinearMap
      period hPeriod choice) +
    massSquared • LinearMap.id

@[simp]
theorem d9IntrinsicDoubledMatterSpinorMassiveLaplaceLinearMap_apply
    (choice : NormalRootChoice) (massSquared : Real)
    (lift : SmoothThroatDoubledMatterSpinorLift
      period hPeriod choice) :
    d9IntrinsicDoubledMatterSpinorMassiveLaplaceLinearMap
        period hPeriod choice massSquared lift =
      -d9IntrinsicDoubledMatterSpinorDiracOperator
          period hPeriod choice
          (d9IntrinsicDoubledMatterSpinorDiracOperator
            period hPeriod choice lift) +
        massSquared • lift := by
  rfl

/-- Exact graph of the intrinsic Dirac operator on the smooth core. -/
def d9IntrinsicDoubledMatterSpinorDiracSmoothGraph
    (choice : NormalRootChoice) :
    Submodule Real
      (SmoothThroatDoubledMatterSpinorLift period hPeriod choice ×
        SmoothThroatDoubledMatterSpinorLift period hPeriod choice) :=
  (d9IntrinsicDoubledMatterSpinorDiracLinearMap
    period hPeriod choice).graph

@[simp]
theorem mem_d9IntrinsicDoubledMatterSpinorDiracSmoothGraph_iff
    (choice : NormalRootChoice)
    (pair :
      SmoothThroatDoubledMatterSpinorLift period hPeriod choice ×
        SmoothThroatDoubledMatterSpinorLift period hPeriod choice) :
    pair ∈ d9IntrinsicDoubledMatterSpinorDiracSmoothGraph
        period hPeriod choice ↔
      pair.2 =
        d9IntrinsicDoubledMatterSpinorDiracOperator
          period hPeriod choice pair.1 :=
  Iff.rfl

structure
    ProgramPD9MatterSpinorDoubledIntrinsicDiracLinearCoreCertificate4D where
  choice : NormalRootChoice
  dirac :
    SmoothThroatDoubledMatterSpinorLift period hPeriod choice →ₗ[Real]
      SmoothThroatDoubledMatterSpinorLift period hPeriod choice
  diracCanonical :
    dirac = d9IntrinsicDoubledMatterSpinorDiracLinearMap
      period hPeriod choice
  square :
    SmoothThroatDoubledMatterSpinorLift period hPeriod choice →ₗ[Real]
      SmoothThroatDoubledMatterSpinorLift period hPeriod choice
  squareCanonical :
    square = d9IntrinsicDoubledMatterSpinorDiracSquaredLinearMap
      period hPeriod choice
  graph : Submodule Real
    (SmoothThroatDoubledMatterSpinorLift period hPeriod choice ×
      SmoothThroatDoubledMatterSpinorLift period hPeriod choice)
  graphCanonical :
    graph = d9IntrinsicDoubledMatterSpinorDiracSmoothGraph
      period hPeriod choice

def programPD9MatterSpinorDoubledIntrinsicDiracLinearCoreCertificate4D :
    ProgramPD9MatterSpinorDoubledIntrinsicDiracLinearCoreCertificate4D
      period hPeriod where
  choice := .positiveQuarter
  dirac := d9IntrinsicDoubledMatterSpinorDiracLinearMap
    period hPeriod .positiveQuarter
  diracCanonical := rfl
  square := d9IntrinsicDoubledMatterSpinorDiracSquaredLinearMap
    period hPeriod .positiveQuarter
  squareCanonical := rfl
  graph := d9IntrinsicDoubledMatterSpinorDiracSmoothGraph
    period hPeriod .positiveQuarter
  graphCanonical := rfl

theorem
    programPD9MatterSpinorDoubledIntrinsicDiracLinearCoreCertificate4D_nonempty :
    Nonempty
      (ProgramPD9MatterSpinorDoubledIntrinsicDiracLinearCoreCertificate4D
        period hPeriod) :=
  ⟨programPD9MatterSpinorDoubledIntrinsicDiracLinearCoreCertificate4D
    period hPeriod⟩

end
end P0EFTJanusProgramPD9MatterSpinorDoubledIntrinsicDiracLinearCore4D
end JanusFormal
