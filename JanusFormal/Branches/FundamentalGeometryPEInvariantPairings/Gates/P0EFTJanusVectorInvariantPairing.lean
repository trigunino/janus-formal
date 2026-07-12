import Mathlib

namespace JanusFormal
namespace P0EFTJanusVectorInvariantPairing

set_option autoImplicit false

/-- Real vector fiber in the local three-dimensional orthonormal model. -/
@[ext] structure Vector3 where
  x : ℝ
  y : ℝ
  z : ℝ

/-- General bilinear form on the vector fiber. -/
@[ext] structure BilinearMatrix3 where
  xx : ℝ
  xy : ℝ
  xz : ℝ
  yx : ℝ
  yy : ℝ
  yz : ℝ
  zx : ℝ
  zy : ℝ
  zz : ℝ

/-- Evaluation of the bilinear form. -/
def pairingValue
    (pairing : BilinearMatrix3)
    (first second : Vector3) : ℝ :=
  pairing.xx * first.x * second.x +
    pairing.xy * first.x * second.y +
    pairing.xz * first.x * second.z +
    pairing.yx * first.y * second.x +
    pairing.yy * first.y * second.y +
    pairing.yz * first.y * second.z +
    pairing.zx * first.z * second.x +
    pairing.zy * first.z * second.y +
    pairing.zz * first.z * second.z

/-- Euclidean dot product. -/
def dotProduct (first second : Vector3) : ℝ :=
  first.x * second.x + first.y * second.y + first.z * second.z

/-- Signed coordinate generators contained in `O(3)`. -/
def flipX (vector : Vector3) : Vector3 :=
  { x := -vector.x, y := vector.y, z := vector.z }


def flipY (vector : Vector3) : Vector3 :=
  { x := vector.x, y := -vector.y, z := vector.z }


def swapXY (vector : Vector3) : Vector3 :=
  { x := vector.y, y := vector.x, z := vector.z }


def swapYZ (vector : Vector3) : Vector3 :=
  { x := vector.x, y := vector.z, z := vector.y }

/-- Basis vectors. -/
def basisX : Vector3 := { x := 1, y := 0, z := 0 }

def basisY : Vector3 := { x := 0, y := 1, z := 0 }

def basisZ : Vector3 := { x := 0, y := 0, z := 1 }

/-- Invariance under a small generating set of signed permutations. -/
structure SignedPermutationInvariant
    (pairing : BilinearMatrix3) where
  flipXInvariant :
    ∀ first second,
      pairingValue pairing (flipX first) (flipX second) =
        pairingValue pairing first second
  flipYInvariant :
    ∀ first second,
      pairingValue pairing (flipY first) (flipY second) =
        pairingValue pairing first second
  swapXYInvariant :
    ∀ first second,
      pairingValue pairing (swapXY first) (swapXY second) =
        pairingValue pairing first second
  swapYZInvariant :
    ∀ first second,
      pairingValue pairing (swapYZ first) (swapYZ second) =
        pairingValue pairing first second

/-- Reflection invariance kills the `xy` coefficient. -/
theorem invariant_xy_zero
    (pairing : BilinearMatrix3)
    (hInvariant : SignedPermutationInvariant pairing) :
    pairing.xy = 0 := by
  have h := hInvariant.flipXInvariant basisX basisY
  norm_num [pairingValue, flipX, basisX, basisY] at h
  linarith

/-- Reflection invariance kills the `xz` coefficient. -/
theorem invariant_xz_zero
    (pairing : BilinearMatrix3)
    (hInvariant : SignedPermutationInvariant pairing) :
    pairing.xz = 0 := by
  have h := hInvariant.flipXInvariant basisX basisZ
  norm_num [pairingValue, flipX, basisX, basisZ] at h
  linarith

/-- Reflection invariance kills the `yx` coefficient. -/
theorem invariant_yx_zero
    (pairing : BilinearMatrix3)
    (hInvariant : SignedPermutationInvariant pairing) :
    pairing.yx = 0 := by
  have h := hInvariant.flipXInvariant basisY basisX
  norm_num [pairingValue, flipX, basisX, basisY] at h
  linarith

/-- Reflection invariance kills the `zx` coefficient. -/
theorem invariant_zx_zero
    (pairing : BilinearMatrix3)
    (hInvariant : SignedPermutationInvariant pairing) :
    pairing.zx = 0 := by
  have h := hInvariant.flipXInvariant basisZ basisX
  norm_num [pairingValue, flipX, basisX, basisZ] at h
  linarith

/-- The remaining `yz` coefficient vanishes. -/
theorem invariant_yz_zero
    (pairing : BilinearMatrix3)
    (hInvariant : SignedPermutationInvariant pairing) :
    pairing.yz = 0 := by
  have h := hInvariant.flipYInvariant basisY basisZ
  norm_num [pairingValue, flipY, basisY, basisZ] at h
  linarith

/-- The remaining `zy` coefficient vanishes. -/
theorem invariant_zy_zero
    (pairing : BilinearMatrix3)
    (hInvariant : SignedPermutationInvariant pairing) :
    pairing.zy = 0 := by
  have h := hInvariant.flipYInvariant basisZ basisY
  norm_num [pairingValue, flipY, basisY, basisZ] at h
  linarith

/-- Coordinate permutation invariance equates the first two diagonal entries. -/
theorem invariant_xx_eq_yy
    (pairing : BilinearMatrix3)
    (hInvariant : SignedPermutationInvariant pairing) :
    pairing.xx = pairing.yy := by
  have h := hInvariant.swapXYInvariant basisX basisX
  norm_num [pairingValue, swapXY, basisX, basisY] at h
  linarith

/-- Coordinate permutation invariance equates the last two diagonal entries. -/
theorem invariant_yy_eq_zz
    (pairing : BilinearMatrix3)
    (hInvariant : SignedPermutationInvariant pairing) :
    pairing.yy = pairing.zz := by
  have h := hInvariant.swapYZInvariant basisY basisY
  norm_num [pairingValue, swapYZ, basisY, basisZ] at h
  linarith

/-- Every invariant vector bilinear form is a scalar multiple of the dot product. -/
theorem invariant_pairing_is_scalar_dot
    (pairing : BilinearMatrix3)
    (hInvariant : SignedPermutationInvariant pairing)
    (first second : Vector3) :
    pairingValue pairing first second =
      pairing.xx * dotProduct first second := by
  rw [invariant_xy_zero pairing hInvariant,
    invariant_xz_zero pairing hInvariant,
    invariant_yx_zero pairing hInvariant,
    invariant_yz_zero pairing hInvariant,
    invariant_zx_zero pairing hInvariant,
    invariant_zy_zero pairing hInvariant,
    ← invariant_xx_eq_yy pairing hInvariant,
    ← invariant_yy_eq_zz pairing hInvariant,
    ← invariant_xx_eq_yy pairing hInvariant]
  unfold pairingValue dotProduct
  ring

/-- Canonical scalar multiple of the Euclidean metric. -/
def scalarDotPairing (coefficient : ℝ) : BilinearMatrix3 :=
  { xx := coefficient
    xy := 0
    xz := 0
    yx := 0
    yy := coefficient
    yz := 0
    zx := 0
    zy := 0
    zz := coefficient }

/-- The canonical scalar-dot form is invariant under the selected generators. -/
theorem scalar_dot_pairing_invariant
    (coefficient : ℝ) :
    SignedPermutationInvariant (scalarDotPairing coefficient) := by
  constructor <;>
    intro first second <;>
    simp [pairingValue, scalarDotPairing,
      flipX, flipY, swapXY, swapYZ] <;>
    ring

/-- Unique classification, up to one real coefficient. -/
theorem vector_invariant_pairing_classification
    (pairing : BilinearMatrix3)
    (hInvariant : SignedPermutationInvariant pairing) :
    pairing = scalarDotPairing pairing.xx := by
  apply BilinearMatrix3.ext
  · rfl
  · exact invariant_xy_zero pairing hInvariant
  · exact invariant_xz_zero pairing hInvariant
  · exact invariant_yx_zero pairing hInvariant
  · exact (invariant_xx_eq_yy pairing hInvariant).symm
  · exact invariant_yz_zero pairing hInvariant
  · exact invariant_zx_zero pairing hInvariant
  · exact invariant_zy_zero pairing hInvariant
  · calc
      pairing.zz = pairing.yy :=
        (invariant_yy_eq_zz pairing hInvariant).symm
      _ = pairing.xx :=
        (invariant_xx_eq_yy pairing hInvariant).symm

/--
P.E vector result: the local vector representation admits one invariant
bilinear form, up to scale.  This fixes the shape of the Maxwell and vector-
ghost pairings, but not their relative normalization or lower-order terms.
-/
structure VectorPairingPhysicalStatus where
  actualO3OrSO3ActionConstructed : Prop
  tangentMetricDerived : Prop
  vectorRepresentationIdentified : Prop
  invariantPairingClassificationApplied : Prop
  realityAndGhostConventionsFixed : Prop
  relativeNormalizationDerived : Prop


def vectorPairingPhysicalClosure
    (s : VectorPairingPhysicalStatus) : Prop :=
  s.actualO3OrSO3ActionConstructed /\
  s.tangentMetricDerived /\
  s.vectorRepresentationIdentified /\
  s.invariantPairingClassificationApplied /\
  s.realityAndGhostConventionsFixed /\
  s.relativeNormalizationDerived

end P0EFTJanusVectorInvariantPairing
end JanusFormal
