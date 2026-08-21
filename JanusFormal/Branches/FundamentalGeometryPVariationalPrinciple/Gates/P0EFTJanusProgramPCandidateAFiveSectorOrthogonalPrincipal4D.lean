import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteOrthogonalCoordinateResolution4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPCandidateAFiveSectorAutomaticPrincipalDecomposition4D

/-!
# Candidate-A principal Gårding from one orthogonal sector decomposition

This packet removes both the five projectors and the principal block-expansion
identity from the analytic input.  One continuous orthogonal coordinate
decomposition determines the natural projectors.  Bilinearity and the
resolution of the identity determine all five diagonal and ten cross terms.

The remaining principal content is therefore only:

* the genuine continuous symmetric principal Hessian;
* the five diagonal coercive estimates;
* strict domination of the ten automatically generated cross norms by the
  smallest diagonal constant.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPCandidateAFiveSectorOrthogonalPrincipal4D

set_option autoImplicit false
set_option maxHeartbeats 3600000
set_option synthInstance.maxHeartbeats 1800000

noncomputable section

open scoped BigOperators InnerProductSpace
open P0EFTJanusProgramPFiniteOrthogonalCoordinateResolution4D
open P0EFTJanusProgramPCandidateAFiveSectorAutomaticPrincipalDecomposition4D
open P0EFTJanusProgramPCandidateAFiveSectorPrincipalBlockDecomposition4D
open P0EFTJanusProgramPCandidateAFiveSectorSymmetricGarding4D
open P0EFTJanusProgramPCandidateAFiveSectorPairwiseGarding4D
open P0EFTJanusProgramPGlobalCandidateANamedZeroModeSectors4D
open P0EFTJanusProgramPCandidateAZeroModeSector4D

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace Real E]

variable (Component : CandidateAZeroModeSector → Type*)
  [∀ sector, NormedAddCommGroup (Component sector)]
  [∀ sector, InnerProductSpace Real (Component sector)]

/-- Principal Candidate-A data in genuine orthogonal sector coordinates. -/
structure CandidateAFiveSectorOrthogonalPrincipalData where
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
  cross_sum_small :
    (∑ pair : CandidateACrossSectorPair,
      ‖candidateASectorSymmetricCrossForm principalForm
        (coordinates.projection Component) pair‖) <
      diagonalConstants.sectorFloor

namespace CandidateAFiveSectorOrthogonalPrincipalData

/-- Forget the coordinate spaces after generating the canonical projectors. -/
def toAutomaticPrincipal
    (data : CandidateAFiveSectorOrthogonalPrincipalData
      (E := E) Component) :
    CandidateAFiveSectorAutomaticPrincipalData (E := E) where
  principalForm := data.principalForm
  principal_symmetric := data.principal_symmetric
  resolution := data.coordinates.toSelfAdjointProjectionResolution Component
  diagonalConstants := data.diagonalConstants
  diagonal_lower := data.diagonal_lower
  cross_sum_small := data.cross_sum_small

/-- Explicit principal margin. -/
def margin
    (data : CandidateAFiveSectorOrthogonalPrincipalData
      (E := E) Component) : Real :=
  data.toAutomaticPrincipal Component |>.margin

/-- Principal Gårding from one orthogonal coordinate decomposition. -/
theorem candidateA_five_sector_orthogonal_principal_garding_gate
    (data : CandidateAFiveSectorOrthogonalPrincipalData
      (E := E) Component) :
    0 < data.margin Component ∧
      ∀ vector : E,
        data.margin Component * ‖vector‖ ^ 2 ≤
          data.principalForm vector vector :=
  data.toAutomaticPrincipal Component
    |>.candidateA_five_sector_automatic_principal_garding_gate

/-- The natural sector projectors are generated outputs, not fields. -/
theorem generated_projection_laws
    (data : CandidateAFiveSectorOrthogonalPrincipalData
      (E := E) Component) :
    (∀ vector,
      (∑ sector : CandidateAZeroModeSector,
        data.coordinates.projection Component sector vector) = vector) ∧
    (∀ sector vector,
      data.coordinates.projection Component sector
          (data.coordinates.projection Component sector vector) =
        data.coordinates.projection Component sector vector) ∧
    (∀ sector first second,
      inner Real (data.coordinates.projection Component sector first) second =
        inner Real first
          (data.coordinates.projection Component sector second)) :=
  ⟨data.coordinates.sum_projection Component,
    data.coordinates.projection_idempotent Component,
    data.coordinates.projection_symmetric Component⟩

end CandidateAFiveSectorOrthogonalPrincipalData

end
end P0EFTJanusProgramPCandidateAFiveSectorOrthogonalPrincipal4D
end JanusFormal
