import Mathlib

namespace JanusFormal
namespace P0EFTJanusPEInvariantPairings

set_option autoImplicit false

/-- Standard three-dimensional tangent representation. -/
@[ext] structure Vector3 where
  x : ℝ
  y : ℝ
  z : ℝ


def basisX : Vector3 := { x := 1, y := 0, z := 0 }
def basisY : Vector3 := { x := 0, y := 1, z := 0 }
def basisZ : Vector3 := { x := 0, y := 0, z := 1 }

/-- Signed-permutation generators in the tangent representation. -/
def flipX (vector : Vector3) : Vector3 :=
  { x := -vector.x, y := vector.y, z := vector.z }


def flipY (vector : Vector3) : Vector3 :=
  { x := vector.x, y := -vector.y, z := vector.z }


def flipZ (vector : Vector3) : Vector3 :=
  { x := vector.x, y := vector.y, z := -vector.z }


def swapXY (vector : Vector3) : Vector3 :=
  { x := vector.y, y := vector.x, z := vector.z }


def swapYZ (vector : Vector3) : Vector3 :=
  { x := vector.x, y := vector.z, z := vector.y }

/-- General real bilinear form on the tangent representation. -/
@[ext] structure VectorBilinear3 where
  xx : ℝ
  xy : ℝ
  xz : ℝ
  yx : ℝ
  yy : ℝ
  yz : ℝ
  zx : ℝ
  zy : ℝ
  zz : ℝ

/-- Evaluation of a tangent bilinear form. -/
def vectorBilinearValue
    (form : VectorBilinear3)
    (first second : Vector3) : ℝ :=
  form.xx * first.x * second.x +
  form.xy * first.x * second.y +
  form.xz * first.x * second.z +
  form.yx * first.y * second.x +
  form.yy * first.y * second.y +
  form.yz * first.y * second.z +
  form.zx * first.z * second.x +
  form.zy * first.z * second.y +
  form.zz * first.z * second.z

/-- Invariance under a generating signed-permutation subgroup of `O(3)`. -/
structure SignedPermutationInvariant
    (form : VectorBilinear3) : Prop where
  flipXInvariant :
    ∀ first second,
      vectorBilinearValue form (flipX first) (flipX second) =
        vectorBilinearValue form first second
  flipYInvariant :
    ∀ first second,
      vectorBilinearValue form (flipY first) (flipY second) =
        vectorBilinearValue form first second
  flipZInvariant :
    ∀ first second,
      vectorBilinearValue form (flipZ first) (flipZ second) =
        vectorBilinearValue form first second
  swapXYInvariant :
    ∀ first second,
      vectorBilinearValue form (swapXY first) (swapXY second) =
        vectorBilinearValue form first second
  swapYZInvariant :
    ∀ first second,
      vectorBilinearValue form (swapYZ first) (swapYZ second) =
        vectorBilinearValue form first second

/-- Euclidean pairing with one normalization. -/
def euclideanVectorForm (coefficient : ℝ) : VectorBilinear3 :=
  { xx := coefficient, xy := 0, xz := 0
    yx := 0, yy := coefficient, yz := 0
    zx := 0, zy := 0, zz := coefficient }

/-- Every Euclidean multiple is signed-permutation invariant. -/
theorem euclidean_vector_form_invariant
    (coefficient : ℝ) :
    SignedPermutationInvariant (euclideanVectorForm coefficient) := by
  refine
    { flipXInvariant := ?_
      flipYInvariant := ?_
      flipZInvariant := ?_
      swapXYInvariant := ?_
      swapYZInvariant := ?_ }
  all_goals
    intro first second
    rcases first with ⟨firstX, firstY, firstZ⟩
    rcases second with ⟨secondX, secondY, secondZ⟩
    simp [vectorBilinearValue, euclideanVectorForm,
      flipX, flipY, flipZ, swapXY, swapYZ]
    ring

/-- Signed permutations force every tangent bilinear form to be Euclidean up to scale. -/
theorem vector_bilinear_unique_up_to_scale
    (form : VectorBilinear3)
    (hInvariant : SignedPermutationInvariant form) :
    form = euclideanVectorForm form.xx := by
  have hXY := hInvariant.flipXInvariant basisX basisY
  have hXZ := hInvariant.flipXInvariant basisX basisZ
  have hYX := hInvariant.flipXInvariant basisY basisX
  have hZX := hInvariant.flipXInvariant basisZ basisX
  have hYZ := hInvariant.flipYInvariant basisY basisZ
  have hZY := hInvariant.flipYInvariant basisZ basisY
  have hYY := hInvariant.swapXYInvariant basisX basisX
  have hZZ := hInvariant.swapYZInvariant basisY basisY
  norm_num [vectorBilinearValue, flipX, flipY,
    swapXY, swapYZ, basisX, basisY, basisZ] at
      hXY hXZ hYX hZX hYZ hZY hYY hZZ
  have hXYZero : form.xy = 0 := by linarith
  have hXZZero : form.xz = 0 := by linarith
  have hYXZero : form.yx = 0 := by linarith
  have hZXZero : form.zx = 0 := by linarith
  have hYZZero : form.yz = 0 := by linarith
  have hZYZero : form.zy = 0 := by linarith
  have hYYEqual : form.yy = form.xx := by linarith
  have hZZEqual : form.zz = form.xx := by linarith
  apply VectorBilinear3.ext
  · rfl
  · exact hXYZero
  · exact hXZZero
  · exact hYXZero
  · exact hYYEqual
  · exact hYZZero
  · exact hZXZero
  · exact hZYZero
  · exact hZZEqual

/-- Scalar-vector bilinear coupling. -/
@[ext] structure ScalarVectorCoupling where
  x : ℝ
  y : ℝ
  z : ℝ


def scalarVectorValue
    (coupling : ScalarVectorCoupling)
    (scalar : ℝ)
    (vector : Vector3) : ℝ :=
  scalar *
    (coupling.x * vector.x +
      coupling.y * vector.y +
      coupling.z * vector.z)

/-- Reflection invariance of a scalar-vector coupling. -/
structure ScalarVectorReflectionInvariant
    (coupling : ScalarVectorCoupling) : Prop where
  flipXInvariant :
    ∀ scalar vector,
      scalarVectorValue coupling scalar (flipX vector) =
        scalarVectorValue coupling scalar vector
  flipYInvariant :
    ∀ scalar vector,
      scalarVectorValue coupling scalar (flipY vector) =
        scalarVectorValue coupling scalar vector
  flipZInvariant :
    ∀ scalar vector,
      scalarVectorValue coupling scalar (flipZ vector) =
        scalarVectorValue coupling scalar vector

/-- No nonzero scalar-vector invariant exists. -/
theorem scalar_vector_invariant_is_zero
    (coupling : ScalarVectorCoupling)
    (hInvariant : ScalarVectorReflectionInvariant coupling) :
    coupling = { x := 0, y := 0, z := 0 } := by
  have hX := hInvariant.flipXInvariant 1 basisX
  have hY := hInvariant.flipYInvariant 1 basisY
  have hZ := hInvariant.flipZInvariant 1 basisZ
  norm_num [scalarVectorValue, flipX, flipY, flipZ,
    basisX, basisY, basisZ] at hX hY hZ
  apply ScalarVectorCoupling.ext <;> linarith

/-- Five coordinates of a symmetric traceless tensor. -/
@[ext] structure TracelessTensor5 where
  a : ℝ
  b : ℝ
  xy : ℝ
  xz : ℝ
  yz : ℝ

/-- Signed-permutation action on traceless tensors. -/
def tensorFlipX (tensor : TracelessTensor5) : TracelessTensor5 :=
  { a := tensor.a, b := tensor.b
    xy := -tensor.xy, xz := -tensor.xz, yz := tensor.yz }


def tensorFlipY (tensor : TracelessTensor5) : TracelessTensor5 :=
  { a := tensor.a, b := tensor.b
    xy := -tensor.xy, xz := tensor.xz, yz := -tensor.yz }


def tensorSwapXY (tensor : TracelessTensor5) : TracelessTensor5 :=
  { a := tensor.b, b := tensor.a
    xy := tensor.xy, xz := tensor.yz, yz := tensor.xz }


def tensorSwapYZ (tensor : TracelessTensor5) : TracelessTensor5 :=
  { a := tensor.a, b := -tensor.a - tensor.b
    xy := tensor.xz, xz := tensor.xy, yz := tensor.yz }


def tensorBasisA : TracelessTensor5 :=
  { a := 1, b := 0, xy := 0, xz := 0, yz := 0 }


def tensorBasisB : TracelessTensor5 :=
  { a := 0, b := 1, xy := 0, xz := 0, yz := 0 }


def tensorBasisXY : TracelessTensor5 :=
  { a := 0, b := 0, xy := 1, xz := 0, yz := 0 }


def tensorBasisXZ : TracelessTensor5 :=
  { a := 0, b := 0, xy := 0, xz := 1, yz := 0 }


def tensorBasisYZ : TracelessTensor5 :=
  { a := 0, b := 0, xy := 0, xz := 0, yz := 1 }

/-- Linear scalar coupling to a traceless tensor. -/
@[ext] structure ScalarTensorCoupling where
  a : ℝ
  b : ℝ
  xy : ℝ
  xz : ℝ
  yz : ℝ


def scalarTensorValue
    (coupling : ScalarTensorCoupling)
    (tensor : TracelessTensor5) : ℝ :=
  coupling.a * tensor.a +
    coupling.b * tensor.b +
    coupling.xy * tensor.xy +
    coupling.xz * tensor.xz +
    coupling.yz * tensor.yz

/-- Signed-permutation invariance of a scalar-tensor linear coupling. -/
structure ScalarTensorInvariant
    (coupling : ScalarTensorCoupling) : Prop where
  flipXInvariant :
    ∀ tensor,
      scalarTensorValue coupling (tensorFlipX tensor) =
        scalarTensorValue coupling tensor
  flipYInvariant :
    ∀ tensor,
      scalarTensorValue coupling (tensorFlipY tensor) =
        scalarTensorValue coupling tensor
  swapXYInvariant :
    ∀ tensor,
      scalarTensorValue coupling (tensorSwapXY tensor) =
        scalarTensorValue coupling tensor
  swapYZInvariant :
    ∀ tensor,
      scalarTensorValue coupling (tensorSwapYZ tensor) =
        scalarTensorValue coupling tensor

/-- No scalar can couple linearly to the traceless tensor representation. -/
theorem scalar_traceless_invariant_is_zero
    (coupling : ScalarTensorCoupling)
    (hInvariant : ScalarTensorInvariant coupling) :
    coupling = { a := 0, b := 0, xy := 0, xz := 0, yz := 0 } := by
  have hXY := hInvariant.flipXInvariant tensorBasisXY
  have hXZ := hInvariant.flipXInvariant tensorBasisXZ
  have hYZ := hInvariant.flipYInvariant tensorBasisYZ
  have hAB := hInvariant.swapXYInvariant tensorBasisA
  have hB := hInvariant.swapYZInvariant tensorBasisB
  norm_num [scalarTensorValue, tensorFlipX, tensorFlipY,
    tensorSwapXY, tensorSwapYZ, tensorBasisA, tensorBasisB,
    tensorBasisXY, tensorBasisXZ, tensorBasisYZ] at
      hXY hXZ hYZ hAB hB
  have hXYZero : coupling.xy = 0 := by linarith
  have hXZZero : coupling.xz = 0 := by linarith
  have hYZZero : coupling.yz = 0 := by linarith
  have hBZero : coupling.b = 0 := by linarith
  have hAZero : coupling.a = 0 := by linarith
  apply ScalarTensorCoupling.ext
  · exact hAZero
  · exact hBZero
  · exact hXYZero
  · exact hXZZero
  · exact hYZZero

/-- Generic inversion selection rule for an odd-even scalar bilinear. -/
theorem inversion_forbids_odd_even_pairing
    {EvenSector : Type*}
    (pairing : Vector3 → EvenSector → ℝ)
    (negLinear :
      ∀ vector tensor,
        pairing { x := -vector.x, y := -vector.y, z := -vector.z }
            tensor = -pairing vector tensor)
    (invariant :
      ∀ vector tensor,
        pairing { x := -vector.x, y := -vector.y, z := -vector.z }
            tensor = pairing vector tensor)
    (vector : Vector3)
    (tensor : EvenSector) :
    pairing vector tensor = 0 := by
  have hNeg := negLinear vector tensor
  have hInvariant := invariant vector tensor
  linarith

/--
P.E low-rank verdict: tangent-vector pairings are unique up to the Euclidean
normalization, while scalar-vector, scalar-traceless and inversion-odd/even
cross pairings vanish.  These are explicit finite-coordinate versions of the
multiplicity-zero/one statements usually obtained from `O(3)` representation
theory.
-/
structure InvariantPairingPhysicalStatus where
  tangentStructureGroupDerived : Prop
  signedPermutationSubgroupIncluded : Prop
  vectorPairingUniquenessProved : Prop
  scalarVectorVanishingProved : Prop
  scalarTracelessVanishingProved : Prop
  vectorTracelessVanishingProved : Prop
  spinorPairingsClassified : Prop
  fullContinuousGroupClassificationProved : Prop
  remainingSectorNormalizationsFixed : Prop


def invariantPairingPhysicalClosure
    (s : InvariantPairingPhysicalStatus) : Prop :=
  s.tangentStructureGroupDerived /\
  s.signedPermutationSubgroupIncluded /\
  s.vectorPairingUniquenessProved /\
  s.scalarVectorVanishingProved /\
  s.scalarTracelessVanishingProved /\
  s.vectorTracelessVanishingProved /\
  s.spinorPairingsClassified /\
  s.fullContinuousGroupClassificationProved /\
  s.remainingSectorNormalizationsFixed

end P0EFTJanusPEInvariantPairings
end JanusFormal
