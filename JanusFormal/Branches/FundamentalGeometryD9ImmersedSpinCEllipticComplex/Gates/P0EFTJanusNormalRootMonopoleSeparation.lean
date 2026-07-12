import Mathlib

namespace JanusFormal
namespace P0EFTJanusNormalRootMonopoleSeparation

set_option autoImplicit false

/-- Chern-number bookkeeping for the complex square root of the normal sign line. -/
structure NormalRootLineChernData where
  firstChernNumber : ℤ
  flatnessForcesChernZero : firstChernNumber = 0

/-- Chern-number bookkeeping for the intrinsic primitive monopole line. -/
structure PrimitiveMonopoleLineChernData where
  firstChernNumber : ℤ
  primitive : firstChernNumber.natAbs = 1

/-- A flat normal-root line cannot be the primitive monopole line. -/
theorem normal_root_line_not_primitive_monopole
    (normalRoot : NormalRootLineChernData)
    (monopole : PrimitiveMonopoleLineChernData) :
    normalRoot.firstChernNumber ≠ monopole.firstChernNumber := by
  intro hEqual
  have hMonopoleZero : monopole.firstChernNumber = 0 := by
    calc
      monopole.firstChernNumber = normalRoot.firstChernNumber :=
        hEqual.symm
      _ = 0 := normalRoot.flatnessForcesChernZero
  rw [hMonopoleZero] at monopole.primitive
  norm_num at monopole.primitive

/-- The normal-root line has no primitive sphere flux. -/
theorem flat_normal_root_cannot_carry_unit_sphere_flux
    (normalRoot : NormalRootLineChernData) :
    normalRoot.firstChernNumber.natAbs ≠ 1 := by
  rw [normalRoot.flatnessForcesChernZero]
  norm_num

/-- The primitive monopole line is necessarily nonflat in Chern-number bookkeeping. -/
theorem primitive_monopole_cannot_have_zero_chern_number
    (monopole : PrimitiveMonopoleLineChernData) :
    monopole.firstChernNumber ≠ 0 := by
  intro hZero
  rw [hZero] at monopole.primitive
  norm_num at monopole.primitive

/-- Minimal geometric input required by the twisted Dirac sector. -/
structure ImmersedSpinCInput where
  immersionAndNormalLineConstructed : Prop
  normalRootFlatLineConstructed : Prop
  primitiveMonopoleLineConstructed : Prop
  normalAndMonopoleLinesDistinguished : Prop
  tensorProductTwistConstructed : Prop

/-- The two line-bundle roles are logically independent. -/
def immersedSpinCInputClosed
    (s : ImmersedSpinCInput) : Prop :=
  s.immersionAndNormalLineConstructed /\
  s.normalRootFlatLineConstructed /\
  s.primitiveMonopoleLineConstructed /\
  s.normalAndMonopoleLinesDistinguished /\
  s.tensorProductTwistConstructed

/--
The immersion produces the nontrivial real normal line and its flat quarter
square root along the circle.  It does not produce the primitive `U(1)` Chern
class on the sphere.  The minimal common foundation is therefore an immersed
SpinC hypersurface: an immersion plus an independent primitive determinant
line, together with the normal-root flat twist.
-/
structure ImmersedSpinCPhysicalStatus where
  hypersurfaceImmersionConstructed : Prop
  oneSidedNormalLineConstructed : Prop
  normalRootLineConstructed : Prop
  spinCDeterminantLineConstructed : Prop
  primitiveChernClassProved : Prop
  lineBundleIndependenceProved : Prop
  twistedSpinorBundleConstructed : Prop
  compatibleConnectionsConstructed : Prop
  globalDiracOperatorConstructed : Prop


def immersedSpinCPhysicalClosure
    (s : ImmersedSpinCPhysicalStatus) : Prop :=
  s.hypersurfaceImmersionConstructed /\
  s.oneSidedNormalLineConstructed /\
  s.normalRootLineConstructed /\
  s.spinCDeterminantLineConstructed /\
  s.primitiveChernClassProved /\
  s.lineBundleIndependenceProved /\
  s.twistedSpinorBundleConstructed /\
  s.compatibleConnectionsConstructed /\
  s.globalDiracOperatorConstructed

end P0EFTJanusNormalRootMonopoleSeparation
end JanusFormal
