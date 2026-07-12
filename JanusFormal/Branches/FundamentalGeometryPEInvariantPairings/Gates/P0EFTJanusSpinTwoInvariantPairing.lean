import Mathlib

namespace JanusFormal
namespace P0EFTJanusSpinTwoInvariantPairing

set_option autoImplicit false

/-- Five coordinates of a traceless symmetric tensor in dimension three. -/
@[ext] structure SpinTwoVector where
  a : ℝ
  b : ℝ
  c : ℝ
  d : ℝ
  e : ℝ

/-- General symmetric bilinear form on the five-dimensional spin-two fiber. -/
@[ext] structure SymmetricPairing5 where
  q00 : ℝ
  q01 : ℝ
  q02 : ℝ
  q03 : ℝ
  q04 : ℝ
  q11 : ℝ
  q12 : ℝ
  q13 : ℝ
  q14 : ℝ
  q22 : ℝ
  q23 : ℝ
  q24 : ℝ
  q33 : ℝ
  q34 : ℝ
  q44 : ℝ

/-- Evaluation of the symmetric bilinear form. -/
def pairingValue
    (pairing : SymmetricPairing5)
    (first second : SpinTwoVector) : ℝ :=
  pairing.q00 * first.a * second.a +
  pairing.q01 * (first.a * second.b + first.b * second.a) +
  pairing.q02 * (first.a * second.c + first.c * second.a) +
  pairing.q03 * (first.a * second.d + first.d * second.a) +
  pairing.q04 * (first.a * second.e + first.e * second.a) +
  pairing.q11 * first.b * second.b +
  pairing.q12 * (first.b * second.c + first.c * second.b) +
  pairing.q13 * (first.b * second.d + first.d * second.b) +
  pairing.q14 * (first.b * second.e + first.e * second.b) +
  pairing.q22 * first.c * second.c +
  pairing.q23 * (first.c * second.d + first.d * second.c) +
  pairing.q24 * (first.c * second.e + first.e * second.c) +
  pairing.q33 * first.d * second.d +
  pairing.q34 * (first.d * second.e + first.e * second.d) +
  pairing.q44 * first.e * second.e

/-- Infinitesimal rotation about the `x` axis in the traceless-tensor representation. -/
def generatorX (vector : SpinTwoVector) : SpinTwoVector :=
  { a := vector.e
    b := -vector.e
    c := -vector.d
    d := vector.c
    e := -vector.a + 3 * vector.b }

/-- Infinitesimal rotation about the `z` axis. -/
def generatorZ (vector : SpinTwoVector) : SpinTwoVector :=
  { a := -2 * vector.c
    b := 0
    c := 2 * vector.a
    d := -vector.e
    e := vector.d }

/-- Coordinate basis. -/
def basis0 : SpinTwoVector := { a := 1, b := 0, c := 0, d := 0, e := 0 }

def basis1 : SpinTwoVector := { a := 0, b := 1, c := 0, d := 0, e := 0 }

def basis2 : SpinTwoVector := { a := 0, b := 0, c := 1, d := 0, e := 0 }

def basis3 : SpinTwoVector := { a := 0, b := 0, c := 0, d := 1, e := 0 }

def basis4 : SpinTwoVector := { a := 0, b := 0, c := 0, d := 0, e := 1 }

/-- Infinitesimal invariance under two Lie-algebra generators of `SO(3)`. -/
structure LieGeneratorInvariant
    (pairing : SymmetricPairing5) where
  xInvariant :
    ∀ first second,
      pairingValue pairing (generatorX first) second +
        pairingValue pairing first (generatorX second) = 0
  zInvariant :
    ∀ first second,
      pairingValue pairing (generatorZ first) second +
        pairingValue pairing first (generatorZ second) = 0

/-- Fourteen independent linear constraints extracted from generator invariance. -/
structure SpinTwoInvariantConstraints
    (pairing : SymmetricPairing5) where
  x00 : -2 * pairing.q04 = 0
  x01 : 3 * pairing.q04 - pairing.q14 = 0
  x02 : pairing.q03 - pairing.q24 = 0
  x03 : -pairing.q02 - pairing.q34 = 0
  x04 : pairing.q00 - pairing.q01 - pairing.q44 = 0
  x12 : pairing.q13 + 3 * pairing.q24 = 0
  x13 : -pairing.q12 + 3 * pairing.q34 = 0
  x14 : pairing.q01 - pairing.q11 + 3 * pairing.q44 = 0
  x22 : 2 * pairing.q23 = 0
  x23 : -pairing.q22 + pairing.q33 = 0
  x24 : pairing.q02 - pairing.q12 + pairing.q34 = 0
  x34 : pairing.q03 - pairing.q13 - pairing.q24 = 0
  z02 : -2 * pairing.q00 + 2 * pairing.q22 = 0
  z12 : -2 * pairing.q01 = 0

/-- Lie-generator invariance implies the exact rational constraint certificate. -/
theorem lie_invariance_implies_constraints
    (pairing : SymmetricPairing5)
    (hInvariant : LieGeneratorInvariant pairing) :
    SpinTwoInvariantConstraints pairing := by
  constructor
  · have h := hInvariant.xInvariant basis0 basis0
    norm_num [pairingValue, generatorX, basis0] at h
    linarith
  · have h := hInvariant.xInvariant basis0 basis1
    norm_num [pairingValue, generatorX, basis0, basis1] at h
    linarith
  · have h := hInvariant.xInvariant basis0 basis2
    norm_num [pairingValue, generatorX, basis0, basis2] at h
    linarith
  · have h := hInvariant.xInvariant basis0 basis3
    norm_num [pairingValue, generatorX, basis0, basis3] at h
    linarith
  · have h := hInvariant.xInvariant basis0 basis4
    norm_num [pairingValue, generatorX, basis0, basis4] at h
    linarith
  · have h := hInvariant.xInvariant basis1 basis2
    norm_num [pairingValue, generatorX, basis1, basis2] at h
    linarith
  · have h := hInvariant.xInvariant basis1 basis3
    norm_num [pairingValue, generatorX, basis1, basis3] at h
    linarith
  · have h := hInvariant.xInvariant basis1 basis4
    norm_num [pairingValue, generatorX, basis1, basis4] at h
    linarith
  · have h := hInvariant.xInvariant basis2 basis2
    norm_num [pairingValue, generatorX, basis2] at h
    linarith
  · have h := hInvariant.xInvariant basis2 basis3
    norm_num [pairingValue, generatorX, basis2, basis3] at h
    linarith
  · have h := hInvariant.xInvariant basis2 basis4
    norm_num [pairingValue, generatorX, basis2, basis4] at h
    linarith
  · have h := hInvariant.xInvariant basis3 basis4
    norm_num [pairingValue, generatorX, basis3, basis4] at h
    linarith
  · have h := hInvariant.zInvariant basis0 basis2
    norm_num [pairingValue, generatorZ, basis0, basis2] at h
    linarith
  · have h := hInvariant.zInvariant basis1 basis2
    norm_num [pairingValue, generatorZ, basis1, basis2] at h
    linarith

/-- Canonical invariant Frobenius pairing in the chosen non-orthonormal basis. -/
def canonicalSpinTwoPairing
    (coefficient : ℝ) : SymmetricPairing5 :=
  { q00 := coefficient
    q01 := 0
    q02 := 0
    q03 := 0
    q04 := 0
    q11 := 3 * coefficient
    q12 := 0
    q13 := 0
    q14 := 0
    q22 := coefficient
    q23 := 0
    q24 := 0
    q33 := coefficient
    q34 := 0
    q44 := coefficient }

/-- The constraint certificate has a one-dimensional solution space. -/
theorem constraints_force_canonical_pairing
    (pairing : SymmetricPairing5)
    (constraints : SpinTwoInvariantConstraints pairing) :
    pairing = canonicalSpinTwoPairing pairing.q44 := by
  have hQ04 : pairing.q04 = 0 := by linarith [constraints.x00]
  have hQ14 : pairing.q14 = 0 := by
    linarith [constraints.x01, hQ04]
  have hQ01 : pairing.q01 = 0 := by linarith [constraints.z12]
  have hQ00 : pairing.q00 = pairing.q44 := by
    linarith [constraints.x04, hQ01]
  have hQ11 : pairing.q11 = 3 * pairing.q44 := by
    linarith [constraints.x14, hQ01]
  have hQ22 : pairing.q22 = pairing.q44 := by
    linarith [constraints.z02, hQ00]
  have hQ33 : pairing.q33 = pairing.q44 := by
    linarith [constraints.x23, hQ22]
  have hQ23 : pairing.q23 = 0 := by linarith [constraints.x22]
  have hQ24 : pairing.q24 = 0 := by
    linarith [constraints.x02, constraints.x12, constraints.x34]
  have hQ03 : pairing.q03 = 0 := by
    linarith [constraints.x02, hQ24]
  have hQ13 : pairing.q13 = 0 := by
    linarith [constraints.x12, hQ24]
  have hQ34 : pairing.q34 = 0 := by
    linarith [constraints.x03, constraints.x13, constraints.x24]
  have hQ02 : pairing.q02 = 0 := by
    linarith [constraints.x03, hQ34]
  have hQ12 : pairing.q12 = 0 := by
    linarith [constraints.x13, hQ34]
  apply SymmetricPairing5.ext
  · exact hQ00
  · exact hQ01
  · exact hQ02
  · exact hQ03
  · exact hQ04
  · exact hQ11
  · exact hQ12
  · exact hQ13
  · exact hQ14
  · exact hQ22
  · exact hQ23
  · exact hQ24
  · exact hQ33
  · exact hQ34
  · rfl

/-- Full spin-two classification: one invariant symmetric pairing, up to scale. -/
theorem spin_two_invariant_pairing_classification
    (pairing : SymmetricPairing5)
    (hInvariant : LieGeneratorInvariant pairing) :
    pairing = canonicalSpinTwoPairing pairing.q44 :=
  constraints_force_canonical_pairing pairing
    (lie_invariance_implies_constraints pairing hInvariant)

/-- The canonical pairing is Lie-generator invariant. -/
theorem canonical_spin_two_pairing_invariant
    (coefficient : ℝ) :
    LieGeneratorInvariant (canonicalSpinTwoPairing coefficient) := by
  constructor <;>
    intro first second <;>
    simp [pairingValue, generatorX, generatorZ,
      canonicalSpinTwoPairing] <;>
    ring

/--
P.E spin-two result: the irreducible traceless symmetric tensor sector carries
one `SO(3)`-invariant symmetric bilinear form up to scale.  The factor `3` is a
basis Gram factor, not a second coupling.  This is an exact Lean certificate
using two infinitesimal rotation generators.
-/
structure SpinTwoPairingPhysicalStatus where
  tracelessTensorBundleConstructed : Prop
  so3ActionIdentified : Prop
  localBasisComparedWithGeometricFrobeniusPairing : Prop
  lieGeneratorCertificateApplied : Prop
  globalInvariantPairingConstructed : Prop
  relativeNormalizationDerived : Prop


def spinTwoPairingPhysicalClosure
    (s : SpinTwoPairingPhysicalStatus) : Prop :=
  s.tracelessTensorBundleConstructed /\
  s.so3ActionIdentified /\
  s.localBasisComparedWithGeometricFrobeniusPairing /\
  s.lieGeneratorCertificateApplied /\
  s.globalInvariantPairingConstructed /\
  s.relativeNormalizationDerived

end P0EFTJanusSpinTwoInvariantPairing
end JanusFormal
