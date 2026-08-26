import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCBundle4D

/-!
# Operator groupoid laws for primitive SpinC transitions

The existing SpinC `VectorBundleCore` proves its transition laws pointwise.
This gate exposes the equivalent continuous-linear-map identities needed by
the second-jet transport.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatSpinCZeroOrderTransitionGroupoid4D

set_option autoImplicit false
noncomputable section

open Set
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCBundle4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev ThroatBase :=
  MappingTorus (fixedEquatorData period hPeriod)

@[simp]
theorem d9PrimitiveSpinCCoordChange_self
    (choice : NormalRootChoice)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (base : ThroatBase period hPeriod)
    (hBase : base ∈ d9PrimitiveSpinCBaseSet period hPeriod index) :
    d9PrimitiveSpinCCoordChange period hPeriod choice index index base =
      ContinuousLinearMap.id Real D9DoubledMatterFiber := by
  apply ContinuousLinearMap.ext
  intro matter
  exact (d9PrimitiveSpinCVectorBundleCore period hPeriod choice)
    |>.coordChange_self index base hBase matter

theorem d9PrimitiveSpinCCoordChange_comp
    (choice : NormalRootChoice)
    (first middle last : D9PrimitiveSpinCIndex period hPeriod)
    (base : ThroatBase period hPeriod)
    (hBase : base ∈
      d9PrimitiveSpinCBaseSet period hPeriod first ∩
        d9PrimitiveSpinCBaseSet period hPeriod middle ∩
          d9PrimitiveSpinCBaseSet period hPeriod last) :
    (d9PrimitiveSpinCCoordChange period hPeriod choice middle last base).comp
        (d9PrimitiveSpinCCoordChange period hPeriod choice first middle base) =
      d9PrimitiveSpinCCoordChange period hPeriod choice first last base := by
  apply ContinuousLinearMap.ext
  intro matter
  exact (d9PrimitiveSpinCVectorBundleCore period hPeriod choice)
    |>.coordChange_comp first middle last base hBase matter

@[simp]
theorem d9PrimitiveSpinCCoordChange_inverse_comp
    (choice : NormalRootChoice)
    (first second : D9PrimitiveSpinCIndex period hPeriod)
    (base : ThroatBase period hPeriod)
    (hBase : base ∈
      d9PrimitiveSpinCBaseSet period hPeriod first ∩
        d9PrimitiveSpinCBaseSet period hPeriod second) :
    (d9PrimitiveSpinCCoordChange period hPeriod choice second first base).comp
        (d9PrimitiveSpinCCoordChange period hPeriod choice first second base) =
      ContinuousLinearMap.id Real D9DoubledMatterFiber := by
  rw [d9PrimitiveSpinCCoordChange_comp period hPeriod choice first second first
    base ⟨hBase, hBase.1⟩]
  exact d9PrimitiveSpinCCoordChange_self period hPeriod choice first base hBase.1

@[simp]
theorem d9PrimitiveSpinCCoordChange_comp_inverse
    (choice : NormalRootChoice)
    (first second : D9PrimitiveSpinCIndex period hPeriod)
    (base : ThroatBase period hPeriod)
    (hBase : base ∈
      d9PrimitiveSpinCBaseSet period hPeriod first ∩
        d9PrimitiveSpinCBaseSet period hPeriod second) :
    (d9PrimitiveSpinCCoordChange period hPeriod choice first second base).comp
        (d9PrimitiveSpinCCoordChange period hPeriod choice second first base) =
      ContinuousLinearMap.id Real D9DoubledMatterFiber := by
  rw [d9PrimitiveSpinCCoordChange_comp period hPeriod choice second first second
    base ⟨⟨hBase.2, hBase.1⟩, hBase.2⟩]
  exact d9PrimitiveSpinCCoordChange_self period hPeriod choice second base hBase.2

end
end P0EFTJanusProgramPActualThroatSpinCZeroOrderTransitionGroupoid4D
end JanusFormal
