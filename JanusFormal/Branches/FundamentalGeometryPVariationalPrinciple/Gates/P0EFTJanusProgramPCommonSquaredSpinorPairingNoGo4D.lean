import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPCommonGhostPairingBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusD9MatterSquaredSpinorCoordinateCompletion4D

/-! # Squared-spinor coordinate pairing no-go

The existing real rank-four coordinate equivalence completes the local D9
record, but it carries no SpinC action or Hermitian structure.  This gate
exhibits two distinct pairings transported through that same equivalence.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPCommonSquaredSpinorPairingNoGo4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusProgramPCommonGeometricDomain4D
open P0EFTJanusProgramPCommonGhostPairingBridge4D
open P0EFTJanusD9MatterSquaredSpinorCoordinateCompletion4D

variable (period : Real) (hPeriod : period ≠ 0)

abbrev MatterCoordinatePairing := MatterFiber → MatterFiber → Real

def euclideanMatterCoordinatePairing : MatterCoordinatePairing :=
  fun first second =>
    first 0 * second 0 + first 1 * second 1 +
      first 2 * second 2 + first 3 * second 3

def anisotropicMatterCoordinatePairing : MatterCoordinatePairing :=
  fun first second =>
    2 * first 0 * second 0 + first 1 * second 1 +
      first 2 * second 2 + first 3 * second 3

private def firstMatterCoordinate : MatterFiber :=
  EuclideanSpace.single 0 (1 : Real)

theorem matterCoordinatePairings_distinct :
    euclideanMatterCoordinatePairing ≠
      anisotropicMatterCoordinatePairing := by
  intro hEqual
  have hValue := congrFun (congrFun hEqual firstMatterCoordinate)
    firstMatterCoordinate
  norm_num [euclideanMatterCoordinatePairing,
    anisotropicMatterCoordinatePairing, firstMatterCoordinate] at hValue

abbrev SquaredSpinorCoordinatePairing :=
  D9SquaredSpinorCoordinateFiber → D9SquaredSpinorCoordinateFiber → Real

/-- Transport of any matter-coordinate pairing through the already existing
rank-four coordinate equivalence. -/
def transportMatterCoordinatePairing
    (pairing : MatterCoordinatePairing) : SquaredSpinorCoordinatePairing :=
  fun first second => pairing
    (matterFiberEquivSquaredSpinorCoordinates.symm first)
    (matterFiberEquivSquaredSpinorCoordinates.symm second)

theorem transportedMatterCoordinatePairings_distinct :
    transportMatterCoordinatePairing euclideanMatterCoordinatePairing ≠
      transportMatterCoordinatePairing anisotropicMatterCoordinatePairing := by
  intro hEqual
  apply matterCoordinatePairings_distinct
  funext first second
  have hValue := congrFun
    (congrFun hEqual (matterFiberEquivSquaredSpinorCoordinates first))
    (matterFiberEquivSquaredSpinorCoordinates second)
  change euclideanMatterCoordinatePairing
      (matterFiberEquivSquaredSpinorCoordinates.symm
        (matterFiberEquivSquaredSpinorCoordinates first))
      (matterFiberEquivSquaredSpinorCoordinates.symm
        (matterFiberEquivSquaredSpinorCoordinates second)) =
    anisotropicMatterCoordinatePairing
      (matterFiberEquivSquaredSpinorCoordinates.symm
        (matterFiberEquivSquaredSpinorCoordinates first))
      (matterFiberEquivSquaredSpinorCoordinates.symm
        (matterFiberEquivSquaredSpinorCoordinates second)) at hValue
  simpa only [Equiv.symm_apply_apply] using hValue

/-- Therefore coordinate completion alone cannot choose even the shape of a
spinor pairing; a geometric SpinC action/Hermitian structure is genuine new
input. -/
theorem squaredSpinorCoordinateEquivalence_does_not_select_pairing :
    ∃ first second : SquaredSpinorCoordinatePairing,
      first ≠ second :=
  ⟨transportMatterCoordinatePairing euclideanMatterCoordinatePairing,
    transportMatterCoordinatePairing anisotropicMatterCoordinatePairing,
    transportedMatterCoordinatePairings_distinct⟩

structure ProgramPCommonSquaredSpinorPairingFrontier4D
    (domain : ProgramPCommonGeometricDomain4D period hPeriod) where
  ghostCertificate :
    ProgramPCommonGhostPairingCertificate4D period hPeriod domain
  coordinatePairingNonunique :
    ∃ first second : SquaredSpinorCoordinatePairing,
      first ≠ second

def programPCommonSquaredSpinorPairingFrontier4D
    (domain : ProgramPCommonGeometricDomain4D period hPeriod) :
    ProgramPCommonSquaredSpinorPairingFrontier4D period hPeriod domain where
  ghostCertificate :=
    programPCommonGhostPairingCertificate4D period hPeriod domain
  coordinatePairingNonunique :=
    squaredSpinorCoordinateEquivalence_does_not_select_pairing

theorem canonicalProgramPCommonSquaredSpinorPairingFrontier4D_nonempty :
    Nonempty
      (ProgramPCommonSquaredSpinorPairingFrontier4D period hPeriod
        (canonicalProgramPCommonGeometricDomain4D period hPeriod)) :=
  ⟨programPCommonSquaredSpinorPairingFrontier4D period hPeriod _⟩

end
end P0EFTJanusProgramPCommonSquaredSpinorPairingNoGo4D
end JanusFormal
