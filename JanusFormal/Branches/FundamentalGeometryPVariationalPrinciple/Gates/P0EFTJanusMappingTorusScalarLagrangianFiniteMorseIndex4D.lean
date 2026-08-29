import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarLagrangianBirmanSchwinger4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarLagrangianFiniteSpectralPacket4D

/-!
# Finite Morse index of scalar Lagrangian spectral packets

For a finite orthonormal eigenpacket, the Hessian is diagonal.  This file defines
its Morse index, nullity and positive count by the signs of the packet
eigenvalues.  It proves nonnegativity/strict positivity criteria and records how
a two-sector exchange coupling shifts the diagonal and relative eigenvalues by
`+kappa` and `-kappa`.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarLagrangianFiniteMorseIndex4D

set_option autoImplicit false
noncomputable section

open Set Topology Module
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarOperatorGraphCompletion4D
open P0EFTJanusMappingTorusScalarClosedGraphRealization4D
open P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D
open P0EFTJanusMappingTorusScalarLagrangianVariationalEigenprinciple4D
open P0EFTJanusMappingTorusScalarLagrangianFiniteSpectralPacket4D

universe u v w z

variable {Domain : Type u} {Ambient : Type v} {Trace : Type w} {Mode : Type z}
  [AddCommGroup Domain] [Module Real Domain]
  [NormedAddCommGroup Ambient] [InnerProductSpace Real Ambient]
  [CompleteSpace Ambient]
  [NormedAddCommGroup Trace] [InnerProductSpace Real Trace]
  [CompleteSpace Trace]
  [Fintype Mode] [DecidableEq Mode]

variable
  {data : CanonicalScalarHilbertGreenSystem
    (Domain := Domain) (Ambient := Ambient) (Trace := Trace)}
  {hClosable : CanonicalScalarGraphClosable data}
  {traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data}
  {condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace}

namespace CanonicalScalarFiniteSpectralPacket

/-- Negative packet modes. -/
def negativeModes
    (packet : CanonicalScalarFiniteSpectralPacket
      data hClosable traceBound condition Mode) : Finset Mode :=
  Finset.univ.filter fun mode => packet.eigenvalue mode < 0

/-- Zero packet modes. -/
def zeroModes
    (packet : CanonicalScalarFiniteSpectralPacket
      data hClosable traceBound condition Mode) : Finset Mode :=
  Finset.univ.filter fun mode => packet.eigenvalue mode = 0

/-- Positive packet modes. -/
def positiveModes
    (packet : CanonicalScalarFiniteSpectralPacket
      data hClosable traceBound condition Mode) : Finset Mode :=
  Finset.univ.filter fun mode => 0 < packet.eigenvalue mode

/-- Finite Morse index. -/
def morseIndex
    (packet : CanonicalScalarFiniteSpectralPacket
      data hClosable traceBound condition Mode) : Nat :=
  (negativeModes packet).card

/-- Finite nullity. -/
def nullity
    (packet : CanonicalScalarFiniteSpectralPacket
      data hClosable traceBound condition Mode) : Nat :=
  (zeroModes packet).card

/-- Number of positive packet modes. -/
def positiveIndex
    (packet : CanonicalScalarFiniteSpectralPacket
      data hClosable traceBound condition Mode) : Nat :=
  (positiveModes packet).card

@[simp] theorem mem_negativeModes
    (packet : CanonicalScalarFiniteSpectralPacket
      data hClosable traceBound condition Mode)
    (mode : Mode) :
    mode ∈ negativeModes packet ↔ packet.eigenvalue mode < 0 := by
  simp [negativeModes]

@[simp] theorem mem_zeroModes
    (packet : CanonicalScalarFiniteSpectralPacket
      data hClosable traceBound condition Mode)
    (mode : Mode) :
    mode ∈ zeroModes packet ↔ packet.eigenvalue mode = 0 := by
  simp [zeroModes]

@[simp] theorem mem_positiveModes
    (packet : CanonicalScalarFiniteSpectralPacket
      data hClosable traceBound condition Mode)
    (mode : Mode) :
    mode ∈ positiveModes packet ↔ 0 < packet.eigenvalue mode := by
  simp [positiveModes]

/-- The three sign sectors partition the finite mode set. -/
theorem negative_zero_positive_card
    (packet : CanonicalScalarFiniteSpectralPacket
      data hClosable traceBound condition Mode) :
    morseIndex packet + nullity packet + positiveIndex packet = Fintype.card Mode := by
  classical
  unfold morseIndex nullity positiveIndex negativeModes zeroModes positiveModes
  have hPartition : Finset.univ =
      ((Finset.univ.filter fun mode => packet.eigenvalue mode < 0) ∪
       (Finset.univ.filter fun mode => packet.eigenvalue mode = 0)) ∪
      (Finset.univ.filter fun mode => 0 < packet.eigenvalue mode) := by
    ext mode
    simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_filter, true_and,
      true_iff]
    rcases lt_trichotomy (packet.eigenvalue mode) 0 with h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
  have hPairwise₁ : Disjoint
      (Finset.univ.filter fun mode => packet.eigenvalue mode < 0)
      (Finset.univ.filter fun mode => packet.eigenvalue mode = 0) := by
    rw [Finset.disjoint_left]
    intro mode hNegative hZero
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hNegative hZero
    linarith
  have hPairwise₂ : Disjoint
      (Finset.univ.filter fun mode => packet.eigenvalue mode < 0)
      (Finset.univ.filter fun mode => 0 < packet.eigenvalue mode) := by
    rw [Finset.disjoint_left]
    intro mode hNegative hPositive
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hNegative hPositive
    linarith
  have hPairwise₃ : Disjoint
      (Finset.univ.filter fun mode => packet.eigenvalue mode = 0)
      (Finset.univ.filter fun mode => 0 < packet.eigenvalue mode) := by
    rw [Finset.disjoint_left]
    intro mode hZero hPositive
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hZero hPositive
    linarith
  have hPairwiseUnion : Disjoint
      ((Finset.univ.filter fun mode => packet.eigenvalue mode < 0) ∪
       (Finset.univ.filter fun mode => packet.eigenvalue mode = 0))
      (Finset.univ.filter fun mode => 0 < packet.eigenvalue mode) := by
    rw [Finset.disjoint_union_left]
    exact ⟨hPairwise₂, hPairwise₃⟩
  calc
    (Finset.univ.filter fun mode => packet.eigenvalue mode < 0).card +
          (Finset.univ.filter fun mode => packet.eigenvalue mode = 0).card +
        (Finset.univ.filter fun mode => 0 < packet.eigenvalue mode).card =
      (((Finset.univ.filter fun mode => packet.eigenvalue mode < 0) ∪
          (Finset.univ.filter fun mode => packet.eigenvalue mode = 0)) ∪
        (Finset.univ.filter fun mode => 0 < packet.eigenvalue mode)).card := by
          rw [Finset.card_union_of_disjoint hPairwiseUnion,
            Finset.card_union_of_disjoint hPairwise₁]
    _ = Finset.univ.card := congrArg Finset.card hPartition.symm
    _ = Fintype.card Mode := Finset.card_univ

/-- Morse index zero exactly when all packet eigenvalues are nonnegative. -/
theorem morseIndex_eq_zero_iff
    (packet : CanonicalScalarFiniteSpectralPacket
      data hClosable traceBound condition Mode) :
    morseIndex packet = 0 ↔ ∀ mode, 0 ≤ packet.eigenvalue mode := by
  classical
  simp [morseIndex, negativeModes]

/-- Nullity zero exactly when all packet eigenvalues are nonzero. -/
theorem nullity_eq_zero_iff
    (packet : CanonicalScalarFiniteSpectralPacket
      data hClosable traceBound condition Mode) :
    nullity packet = 0 ↔ ∀ mode, packet.eigenvalue mode ≠ 0 := by
  classical
  simp [nullity, zeroModes]

/-- Nonnegative packet spectrum gives a nonnegative Hessian on the entire
packet. -/
theorem quadratic_nonnegative_of_morseIndex_zero
    (packet : CanonicalScalarFiniteSpectralPacket
      data hClosable traceBound condition Mode)
    (hMorse : morseIndex packet = 0)
    (coefficient : Mode → Real) :
    0 ≤ canonicalScalarClosedLagrangianQuadraticFunctional
      data hClosable traceBound condition (packet.field coefficient) := by
  rw [packet.quadratic_eq_weighted_sum]
  apply Finset.sum_nonneg
  intro mode _
  exact mul_nonneg ((morseIndex_eq_zero_iff packet).1 hMorse mode)
    (sq_nonneg _)

/-- Strictly positive packet spectrum gives positive Hessian for every nonzero
coefficient vector. -/
theorem quadratic_positive_of_all_positive
    (packet : CanonicalScalarFiniteSpectralPacket
      data hClosable traceBound condition Mode)
    (hPositive : ∀ mode, 0 < packet.eigenvalue mode)
    (coefficient : Mode → Real)
    (hCoefficient : ∃ mode, coefficient mode ≠ 0) :
    0 < canonicalScalarClosedLagrangianQuadraticFunctional
      data hClosable traceBound condition (packet.field coefficient) := by
  rw [packet.quadratic_eq_weighted_sum]
  rcases hCoefficient with ⟨mode, hMode⟩
  have hTerm : 0 < packet.eigenvalue mode * coefficient mode ^ 2 :=
    mul_pos (hPositive mode) (sq_pos_of_ne_zero hMode)
  have hNonnegative : ∀ currentMode ∈ Finset.univ,
      0 ≤ packet.eigenvalue currentMode * coefficient currentMode ^ 2 := by
    intro currentMode _
    exact mul_nonneg (hPositive currentMode).le (sq_nonneg _)
  exact lt_of_lt_of_le hTerm
    (Finset.single_le_sum hNonnegative (Finset.mem_univ mode))

/-- A negative eigenmode gives a negative Hessian direction. -/
theorem negative_direction_of_mem_negativeModes
    (packet : CanonicalScalarFiniteSpectralPacket
      data hClosable traceBound condition Mode)
    (mode : Mode) (hMode : mode ∈ negativeModes packet) :
    canonicalScalarClosedLagrangianQuadraticFunctional
        data hClosable traceBound condition
        (packet.field (fun currentMode => if currentMode = mode then 1 else 0)) < 0 := by
  rw [packet.quadratic_eq_weighted_sum]
  classical
  simp [(mem_negativeModes packet mode).mp hMode]

/-- Two-sector shifted even eigenvalue. -/
def evenShiftedEigenvalue
    (packet : CanonicalScalarFiniteSpectralPacket
      data hClosable traceBound condition Mode)
    (coupling : Real) (mode : Mode) : Real :=
  packet.eigenvalue mode + coupling

/-- Two-sector shifted odd eigenvalue. -/
def oddShiftedEigenvalue
    (packet : CanonicalScalarFiniteSpectralPacket
      data hClosable traceBound condition Mode)
    (coupling : Real) (mode : Mode) : Real :=
  packet.eigenvalue mode - coupling

/-- Two-sector finite Morse count from shifted even and odd modes. -/
def twoSectorMorseIndex
    (packet : CanonicalScalarFiniteSpectralPacket
      data hClosable traceBound condition Mode)
    (coupling : Real) : Nat :=
  (Finset.univ.filter fun mode => evenShiftedEigenvalue packet coupling mode < 0).card +
  (Finset.univ.filter fun mode => oddShiftedEigenvalue packet coupling mode < 0).card

/-- Vanishing two-sector Morse index is equivalent to nonnegativity of both
shifted sectors. -/
theorem twoSectorMorseIndex_eq_zero_iff
    (packet : CanonicalScalarFiniteSpectralPacket
      data hClosable traceBound condition Mode)
    (coupling : Real) :
    twoSectorMorseIndex packet coupling = 0 ↔
      (∀ mode, 0 ≤ packet.eigenvalue mode + coupling) ∧
      (∀ mode, 0 ≤ packet.eigenvalue mode - coupling) := by
  classical
  simp [twoSectorMorseIndex, evenShiftedEigenvalue, oddShiftedEigenvalue,
    Nat.add_eq_zero_iff]

/-- Finite Morse-index certificate. -/
theorem canonicalScalarFiniteMorseIndex_certificate
    (packet : CanonicalScalarFiniteSpectralPacket
      data hClosable traceBound condition Mode) :
    morseIndex packet + nullity packet + positiveIndex packet = Fintype.card Mode ∧
      (morseIndex packet = 0 ↔ ∀ mode, 0 ≤ packet.eigenvalue mode) ∧
      (nullity packet = 0 ↔ ∀ mode, packet.eigenvalue mode ≠ 0) :=
  ⟨negative_zero_positive_card packet,
    morseIndex_eq_zero_iff packet,
    nullity_eq_zero_iff packet⟩

end CanonicalScalarFiniteSpectralPacket

end
end P0EFTJanusMappingTorusScalarLagrangianFiniteMorseIndex4D
end JanusFormal
