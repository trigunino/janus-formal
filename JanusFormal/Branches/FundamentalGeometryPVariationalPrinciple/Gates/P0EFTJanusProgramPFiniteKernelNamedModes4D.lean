import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteKernelModel4D

/-!
# Named finite models of the actual operator kernel

`FiniteKernelModel` already identifies a finite coordinate space with the
actual kernel.  For the physical closure one also wants the coordinate axes to
be attached to explicitly named zero-mode vectors, rather than retaining only
an anonymous linear equivalence.

This file adds exactly that datum.  A named family stores concrete vectors in
the ambient Hilbert space, proves that they are annihilated by the displayed
operator, and identifies every coordinate unit with the corresponding named
vector.  The existing finite-kernel and actual-complement machinery is then
reused without choosing an auxiliary defect space.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiniteKernelNamedModes4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPSelfAdjointKernelComplementReduction4D
open P0EFTJanusProgramPFiniteKernelModel4D

variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]

/-- The standard coordinate vector associated with one finite label. -/
def finiteCoordinateUnit
    {Index : Type*} [DecidableEq Index]
    (index : Index) : Index → Real :=
  fun other => if other = index then 1 else 0

@[simp]
theorem finiteCoordinateUnit_same
    {Index : Type*} [DecidableEq Index]
    (index : Index) :
    finiteCoordinateUnit index index = 1 := by
  simp [finiteCoordinateUnit]

@[simp]
theorem finiteCoordinateUnit_of_ne
    {Index : Type*} [DecidableEq Index]
    {first second : Index} (hne : first ≠ second) :
    finiteCoordinateUnit first second = 0 := by
  simp [finiteCoordinateUnit, Ne.symm hne]

/-- A finite physical classification of the actual kernel.  The labels may be
sectors, residual gauge generators, moduli, or any later physically meaningful
finite type. -/
structure FiniteKernelNamedModeFamily
    (operator : E →L[Real] E)
    (ZeroMode : Type) [Fintype ZeroMode] [DecidableEq ZeroMode] where
  vector : ZeroMode → E
  vector_mem_kernel : ∀ index, operator (vector index) = 0
  coordinates : (ZeroMode → Real) ≃ₗ[Real] operator.ker
  coordinates_unit : ∀ index,
    (coordinates (finiteCoordinateUnit index)).1 = vector index

namespace FiniteKernelNamedModeFamily

variable {operator : E →L[Real] E}
variable {ZeroMode : Type} [Fintype ZeroMode] [DecidableEq ZeroMode]

/-- Forget the physical names while retaining the exact finite kernel model. -/
def toFiniteKernelModel
    (family : FiniteKernelNamedModeFamily operator ZeroMode) :
    FiniteKernelModel operator where
  ZeroMode := ZeroMode
  zeroModeFintype := inferInstance
  zeroModeDecidableEq := inferInstance
  coordinates := family.coordinates

/-- Synthesis of one arbitrary finite coordinate vector. -/
def synthesize
    (family : FiniteKernelNamedModeFamily operator ZeroMode)
    (coefficient : ZeroMode → Real) : E :=
  (family.coordinates coefficient).1

/-- Analysis of one genuine vector in the actual kernel. -/
def analyze
    (family : FiniteKernelNamedModeFamily operator ZeroMode)
    (zeroMode : operator.ker) : ZeroMode → Real :=
  family.coordinates.symm zeroMode

/-- Coordinate synthesis lands in the actual kernel. -/
theorem synthesize_mem_kernel
    (family : FiniteKernelNamedModeFamily operator ZeroMode)
    (coefficient : ZeroMode → Real) :
    operator (family.synthesize coefficient) = 0 :=
  (family.coordinates coefficient).2

/-- Every named vector is the synthesis of its own coordinate axis. -/
@[simp]
theorem synthesize_coordinateUnit
    (family : FiniteKernelNamedModeFamily operator ZeroMode)
    (index : ZeroMode) :
    family.synthesize (finiteCoordinateUnit index) = family.vector index :=
  family.coordinates_unit index

/-- Every named vector is genuinely annihilated by the operator. -/
theorem named_vector_mem_kernel
    (family : FiniteKernelNamedModeFamily operator ZeroMode)
    (index : ZeroMode) :
    operator (family.vector index) = 0 :=
  family.vector_mem_kernel index

/-- Exact reconstruction of every genuine zero mode from its finite
coordinates. -/
@[simp]
theorem synthesize_analyze
    (family : FiniteKernelNamedModeFamily operator ZeroMode)
    (zeroMode : operator.ker) :
    family.synthesize (family.analyze zeroMode) = zeroMode.1 := by
  unfold synthesize analyze
  rw [family.coordinates.apply_symm_apply]

/-- Exact recovery of every finite coordinate vector. -/
@[simp]
theorem analyze_synthesize
    (family : FiniteKernelNamedModeFamily operator ZeroMode)
    (coefficient : ZeroMode → Real) :
    family.analyze (family.coordinates coefficient) = coefficient := by
  unfold analyze
  exact family.coordinates.symm_apply_apply coefficient

/-- The number of physical labels is exactly the dimension of the actual
kernel. -/
theorem kernel_finrank_eq_card
    (family : FiniteKernelNamedModeFamily operator ZeroMode) :
    Module.finrank Real operator.ker = Fintype.card ZeroMode :=
  family.toFiniteKernelModel.kernel_finrank_eq_card

end FiniteKernelNamedModeFamily

section Gap

variable
  {Hilbert : Type*}
  [NormedAddCommGroup Hilbert] [InnerProductSpace Real Hilbert]
  [CompleteSpace Hilbert]

/-- Actual-kernel gap data whose finite obstruction is represented by named
physical zero modes. -/
structure SelfAdjointKernelComplementGapWithNamedModes
    (operator : Hilbert →L[Real] Hilbert)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (ZeroMode : Type) [Fintype ZeroMode] [DecidableEq ZeroMode] where
  family : FiniteKernelNamedModeFamily operator ZeroMode
  gap : Real
  gap_pos : 0 < gap
  lowerBound : ∀ vector : SelfAdjointKernelComplement operator,
    gap * ‖vector‖ ≤
      ‖selfAdjointKernelComplementOperator operator hSelfAdjoint vector‖

/-- Forget the labels and recover the already installed actual-kernel gap
packet. -/
def SelfAdjointKernelComplementGapWithNamedModes.toGapWithModel
    {operator : Hilbert →L[Real] Hilbert}
    {hSelfAdjoint : IsSelfAdjoint operator}
    {ZeroMode : Type} [Fintype ZeroMode] [DecidableEq ZeroMode]
    (data : SelfAdjointKernelComplementGapWithNamedModes operator hSelfAdjoint
      ZeroMode) :
    SelfAdjointKernelComplementGapWithModel operator hSelfAdjoint where
  model := data.family.toFiniteKernelModel
  gap := data.gap
  gap_pos := data.gap_pos
  lowerBound := data.lowerBound

/-- Named zero modes feed the existing actual-kernel Green and Fredholm
machinery without any new analytic hypothesis. -/
theorem finite_kernel_named_modes_actual_gap_gate
    (operator : Hilbert →L[Real] Hilbert)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (ZeroMode : Type) [Fintype ZeroMode] [DecidableEq ZeroMode]
    (data : SelfAdjointKernelComplementGapWithNamedModes operator hSelfAdjoint
      ZeroMode) :
    Nonempty (SelfAdjointKernelComplementGapWithModel operator hSelfAdjoint) ∧
      Module.finrank Real operator.ker = Fintype.card ZeroMode ∧
      (∀ index, operator (data.family.vector index) = 0) := by
  exact ⟨⟨data.toGapWithModel⟩,
    data.family.kernel_finrank_eq_card,
    data.family.vector_mem_kernel⟩

end Gap

end
end P0EFTJanusProgramPFiniteKernelNamedModes4D
end JanusFormal
