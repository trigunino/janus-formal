import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPCandidateAFiveSectorOrthogonalPrincipal4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteSectorQuadraticGarding4D

/-!
# Five-sector principal Gårding from one canonical off-diagonal form

The ten cross-sector forms are useful for fine estimates, but they are not the
minimal structural input.  Once the five natural projectors are generated from
an orthogonal coordinate decomposition, define

`B_diag = sum_s B(P_s ·, P_s ·)`

and

`B_off = B - B_diag`.

The identity `B = B_diag + B_off` is definitional.  Thus one strict estimate
`‖B_off‖ < c_floor` replaces ten separate cross-form norms and the associated
finite bookkeeping.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPCandidateAFiveSectorOrthogonalOffDiagonalGarding4D

set_option autoImplicit false
set_option maxHeartbeats 3800000
set_option synthInstance.maxHeartbeats 1900000

noncomputable section

open scoped BigOperators InnerProductSpace
open P0EFTJanusProgramPFiniteSectorQuadraticGarding4D
open P0EFTJanusProgramPFiniteOrthogonalCoordinateResolution4D
open P0EFTJanusProgramPCandidateAFiveSectorPairwiseGarding4D
open P0EFTJanusProgramPCandidateAZeroModeSector4D
open P0EFTJanusProgramPGlobalCandidateANamedZeroModeSectors4D

variable {E : Type*}
  [NormedAddCommGroup E]
  [InnerProductSpace Real E]

variable (Component : CandidateAZeroModeSector → Type*)
  [∀ sector, NormedAddCommGroup (Component sector)]
  [∀ sector, InnerProductSpace Real (Component sector)]

/-- Orthogonal coordinates, five diagonal estimates, and one canonical
+off-diagonal norm estimate. -/
structure CandidateAFiveSectorOrthogonalOffDiagonalGardingData where
  principalForm : E →L[Real] E →L[Real] Real
  principal_symmetric : ∀ first second,
    principalForm first second = principalForm second first
  coordinates : FiniteOrthogonalCoordinateDecompositionData
    (Sector := CandidateAZeroModeSector) (E := E) Component
  diagonalConstants : CandidateAFiveSectorDiagonalConstants
  diagonal_lower : ∀ sector vector,
    diagonalConstants.sectorConstant sector *
        ‖coordinates.projection Component sector vector‖ ^ 2 ≤
      principalForm
        (coordinates.projection Component sector vector)
        (coordinates.projection Component sector vector)
  offDiagonal_small :
    ‖principalForm -
      ∑ sector : CandidateAZeroModeSector,
        principalForm.bilinearComp
          (coordinates.projection Component sector)
          (coordinates.projection Component sector)‖ <
      diagonalConstants.sectorFloor

namespace CandidateAFiveSectorOrthogonalOffDiagonalGardingData

/-- Sum of the five true diagonal restrictions. -/
def diagonalForm
    (data : CandidateAFiveSectorOrthogonalOffDiagonalGardingData
      (E := E) Component) :
    E →L[Real] E →L[Real] Real :=
  ∑ sector : CandidateAZeroModeSector,
    data.principalForm.bilinearComp
      (data.coordinates.projection Component sector)
      (data.coordinates.projection Component sector)

/-- Canonical complete off-diagonal principal form. -/
def offDiagonalForm
    (data : CandidateAFiveSectorOrthogonalOffDiagonalGardingData
      (E := E) Component) :
    E →L[Real] E →L[Real] Real :=
  data.principalForm - data.diagonalForm Component

/-- The operator norm gives the canonical quadratic estimate for the complete
+off-diagonal form. -/
theorem offDiagonal_quadratic_bound
    (data : CandidateAFiveSectorOrthogonalOffDiagonalGardingData
      (E := E) Component)
    (vector : E) :
    |data.offDiagonalForm Component vector vector| ≤
      ‖data.offDiagonalForm Component‖ * ‖vector‖ ^ 2 := by
  calc
    |data.offDiagonalForm Component vector vector| =
        ‖data.offDiagonalForm Component vector vector‖ :=
      (Real.norm_eq_abs _).symm
    _ ≤ ‖data.offDiagonalForm Component vector‖ * ‖vector‖ :=
      (data.offDiagonalForm Component vector).le_opNorm vector
    _ ≤ (‖data.offDiagonalForm Component‖ * ‖vector‖) * ‖vector‖ :=
      mul_le_mul_of_nonneg_right
        ((data.offDiagonalForm Component).le_opNorm vector)
        (norm_nonneg vector)
    _ = ‖data.offDiagonalForm Component‖ * ‖vector‖ ^ 2 := by
      ring

/-- Generic finite-sector packet generated from the canonical diagonal/off-
+diagonal split. -/
def toFiniteSectorGarding
    (data : CandidateAFiveSectorOrthogonalOffDiagonalGardingData
      (E := E) Component) :
    FiniteSectorQuadraticGardingData
      (Sector := CandidateAZeroModeSector) (E := E) where
  sectorWeight := fun sector vector =>
    ‖data.coordinates.projection Component sector vector‖ ^ 2
  sectorWeight_nonneg := fun _ _ => sq_nonneg _
  sectorWeight_sum := data.coordinates.norm_sq_decomposition Component
  sectorConstant := data.diagonalConstants.sectorConstant
  sectorConstant_pos := data.diagonalConstants.sectorConstant_pos
  sectorFloor := data.diagonalConstants.sectorFloor
  sectorFloor_pos := data.diagonalConstants.sectorFloor_pos
  sectorFloor_le := data.diagonalConstants.sectorFloor_le
  diagonalEnergy := fun vector => data.diagonalForm Component vector vector
  diagonal_lower := by
    intro vector
    unfold diagonalForm
    simp only [ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.bilinearComp_apply]
    apply Finset.sum_le_sum
    intro sector _
    exact data.diagonal_lower sector vector
  couplingEnergy := fun vector => data.offDiagonalForm Component vector vector
  couplingConstant := ‖data.offDiagonalForm Component‖
  couplingConstant_nonneg := norm_nonneg (data.offDiagonalForm Component)
  coupling_bound := data.offDiagonal_quadratic_bound Component
  coupling_small := by
    simpa [offDiagonalForm, diagonalForm] using data.offDiagonal_small
  principalEnergy := fun vector => data.principalForm vector vector
  principal_eq := by
    intro vector
    unfold offDiagonalForm
    simp only [ContinuousLinearMap.sub_apply]
    ring

/-- Explicit one-form principal margin. -/
def margin
    (data : CandidateAFiveSectorOrthogonalOffDiagonalGardingData
      (E := E) Component) : Real :=
  data.diagonalConstants.sectorFloor - ‖data.offDiagonalForm Component‖

/-- Principal Gårding from one orthogonal decomposition and one off-diagonal
+norm comparison. -/
theorem candidateA_five_sector_orthogonal_offDiagonal_garding_gate
    (data : CandidateAFiveSectorOrthogonalOffDiagonalGardingData
      (E := E) Component) :
    0 < data.margin Component ∧
      ∀ vector : E,
        data.margin Component * ‖vector‖ ^ 2 ≤
          data.principalForm vector vector := by
  have h :=
    data.toFiniteSectorGarding Component |>.finite_sector_quadratic_garding_gate
  constructor
  · exact h.1
  · exact h.2

end CandidateAFiveSectorOrthogonalOffDiagonalGardingData

end
end P0EFTJanusProgramPCandidateAFiveSectorOrthogonalOffDiagonalGarding4D
end JanusFormal
