import Mathlib

namespace JanusFormal
namespace P0EFTJanusHopfBundleOrientationNoGo

set_option autoImplicit false

/-- Orientation parity: `false` preserves and `true` reverses orientation. -/
abbrev OrientationParity := Bool

/-- Product orientation reverses exactly when one factor reverses. -/
def totalOrientationParity
    (fiber base : OrientationParity) : OrientationParity :=
  xor fiber base

/--
For a symmetry of the unit Hopf bundle, compatibility with the primitive first
Chern class forces the orientation action on the circle fiber to agree with the
orientation action on the two-sphere base.
-/
structure HopfBundleSymmetry where
  reversesFiber : OrientationParity
  reversesBase : OrientationParity
  primitiveChernCompatibility : reversesFiber = reversesBase

/-- Every primitive-Chern-compatible Hopf-bundle symmetry preserves total-space orientation. -/
theorem compatible_hopf_symmetry_preserves_total_orientation
    (s : HopfBundleSymmetry) :
    totalOrientationParity s.reversesFiber s.reversesBase = false := by
  rw [s.primitiveChernCompatibility]
  cases s.reversesBase <;> rfl

/--
Hence an orientation-reversing monodromy of `S3` cannot simultaneously be an
automorphism of the ordinary principal `U(1)` Hopf bundle with primitive Chern
class.
-/
theorem no_orientation_reversing_primitive_hopf_bundle_automorphism
    (s : HopfBundleSymmetry) :
    totalOrientationParity s.reversesFiber s.reversesBase ≠ true := by
  rw [compatible_hopf_symmetry_preserves_total_orientation s]
  decide

/--
The geometric escape routes must therefore change the gauge object: use a
monopole line bundle intrinsic to the `S2` throat, an `O(2)=U(1)⋊Z2` twisted
bundle, or a non-fiber-preserving family of Hopf structures.
-/
structure HopfNoGoExitStatus where
  throatMonopoleBundleConstructed : Prop
  twistedO2BundleConstructed : Prop
  varyingHopfFamilyConstructed : Prop
  atLeastOneExitDerived : Prop


def hopfNoGoExited (s : HopfNoGoExitStatus) : Prop :=
  (s.throatMonopoleBundleConstructed \/
    s.twistedO2BundleConstructed \/
    s.varyingHopfFamilyConstructed) /\
  s.atLeastOneExitDerived

end P0EFTJanusHopfBundleOrientationNoGo
end JanusFormal
