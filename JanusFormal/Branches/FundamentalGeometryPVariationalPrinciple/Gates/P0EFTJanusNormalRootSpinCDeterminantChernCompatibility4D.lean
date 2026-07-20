import JanusFormal.Branches.FundamentalGeometryD9ImmersedSpinCEllipticComplex.Gates.P0EFTJanusNormalRootMonopoleSeparation
import JanusFormal.Branches.FundamentalGeometryD10DerivedModuliPotential.Gates.P0EFTJanusSpinCDeterminantParityAudit

/-!
# Normal-root, primitive twist and SpinC determinant Chern arithmetic

This gate combines existing Chern-number results.  It does not identify or
construct the corresponding global `Pin⁻`/`PinC` bundles.
-/

namespace JanusFormal
namespace P0EFTJanusNormalRootSpinCDeterminantChernCompatibility4D

open P0EFTJanusNormalRootMonopoleSeparation
open P0EFTJanusSpinCDeterminantParityAudit

set_option autoImplicit false

/-- The flat normal root, primitive SpinC twist and its determinant occupy
the distinct Chern magnitudes `0`, `1` and `2`. -/
theorem normalRoot_primitiveSpinCTwist_determinant_separation
    (normalRoot : NormalRootLineChernData)
    (monopole : PrimitiveMonopoleLineChernData)
    (spinC : SpinTwistChernData)
    (hTwist : spinC.twistChernNumber = monopole.firstChernNumber) :
    normalRoot.firstChernNumber = 0 ∧
      spinC.twistChernNumber.natAbs = 1 ∧
      spinC.determinantChernNumber.natAbs = 2 ∧
      normalRoot.firstChernNumber ≠ spinC.twistChernNumber ∧
      spinC.twistChernNumber ≠ spinC.determinantChernNumber := by
  have hTwistPrimitive : spinC.twistChernNumber.natAbs = 1 := by
    rw [hTwist]
    exact monopole.primitive
  have hDeterminantMagnitude : spinC.determinantChernNumber.natAbs = 2 :=
    primitive_twist_forces_determinant_magnitude_two spinC hTwistPrimitive
  refine ⟨normalRoot.flatnessForcesChernZero, hTwistPrimitive,
    hDeterminantMagnitude, ?_, ?_⟩
  · rw [hTwist]
    exact normal_root_line_not_primitive_monopole normalRoot monopole
  · intro hEqual
    have hMagnitudeEqual := congrArg Int.natAbs hEqual
    omega

/-- In the same convention the SpinC determinant Chern number is even. -/
theorem primitiveSpinCTwist_determinant_even
    (spinC : SpinTwistChernData) :
    Even spinC.determinantChernNumber :=
  determinant_chern_number_even spinC

end P0EFTJanusNormalRootSpinCDeterminantChernCompatibility4D
end JanusFormal
