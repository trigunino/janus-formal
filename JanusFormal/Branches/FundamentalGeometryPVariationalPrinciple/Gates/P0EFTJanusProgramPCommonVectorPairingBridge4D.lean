import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPCommonGeometricDomain4D
import JanusFormal.Branches.FundamentalGeometryPEInvariantPairings.Gates.P0EFTJanusVectorInvariantPairing

/-! # Common-domain vector-pairing certificate

This gate transports the finite `O(3)` vector-pairing classification to the
actual throat tangent coordinates of the global Program-P variation type.
It does not globalize the remaining spin-two, spinor or BRST pairings.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPCommonVectorPairingBridge4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusInducedFieldVariation4D
open P0EFTJanusMappingTorusIndependentPTBoundaryAction4D
open P0EFTJanusImmersionFiberAlgebra
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPCommonGeometricDomain4D
open P0EFTJanusVectorInvariantPairing

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

/-- The representation-theory vector is exactly the existing D9 throat
tangent coordinate, with no discarded component. -/
def tangentVectorPairingEquiv : TangentVector3 ≃ Vector3 where
  toFun vector := { x := vector.x, y := vector.y, z := vector.z }
  invFun vector := { x := vector.x, y := vector.y, z := vector.z }
  left_inv vector := by cases vector; rfl
  right_inv vector := by cases vector; rfl

/-- Pull an arbitrary classified bilinear matrix back to the genuine D9
tangent coordinate. -/
def tangentVectorPairing
    (pairing : BilinearMatrix3)
    (first second : TangentVector3) : Real :=
  pairingValue pairing
    (tangentVectorPairingEquiv first)
    (tangentVectorPairingEquiv second)

def tangentVectorDot (first second : TangentVector3) : Real :=
  first.x * second.x + first.y * second.y + first.z * second.z

/-- Signed-permutation invariance leaves precisely the metric dot product on
the actual tangent coordinate. -/
theorem tangentVectorPairing_classified
    (pairing : BilinearMatrix3)
    (hInvariant : SignedPermutationInvariant pairing)
    (first second : TangentVector3) :
    tangentVectorPairing pairing first second =
      pairing.xx * tangentVectorDot first second := by
  rw [vector_invariant_pairing_classification pairing hInvariant]
  rcases first with ⟨firstX, firstY, firstZ⟩
  rcases second with ⟨secondX, secondY, secondZ⟩
  simp [tangentVectorPairing, tangentVectorPairingEquiv,
    tangentVectorDot, pairingValue, scalarDotPairing]
  ring

/-- The same pairing evaluated on the actual smooth complete variations at a
point of the true effective throat. -/
def completeVariationGhostPairingAt
    (pairing : BilinearMatrix3)
    (first second : ProgramPCompleteVariation4D period hPeriod)
    (sector : Sector) (point : EffectiveThroat period hPeriod) : Real :=
  tangentVectorPairing pairing
    (first.diffeomorphismGhostAt period hPeriod sector point)
    (second.diffeomorphismGhostAt period hPeriod sector point)

theorem completeVariationGhostPairingAt_classified
    (pairing : BilinearMatrix3)
    (hInvariant : SignedPermutationInvariant pairing)
    (first second : ProgramPCompleteVariation4D period hPeriod)
    (sector : Sector) (point : EffectiveThroat period hPeriod) :
    completeVariationGhostPairingAt period hPeriod pairing first second
        sector point =
      pairing.xx * tangentVectorDot
        (first.diffeomorphismGhostAt period hPeriod sector point)
        (second.diffeomorphismGhostAt period hPeriod sector point) :=
  tangentVectorPairing_classified pairing hInvariant _ _

/-- Typed certificate joining the established common-domain coherences and
the vector pairing classification on its genuine complete variations. -/
structure ProgramPCommonVectorPairingCertificate4D
    (domain : ProgramPCommonGeometricDomain4D period hPeriod) where
  induced_coherent :
    domain.induced = induce period hPeriod domain.configuration
  operator_coherent :
    domain.operatorData.fields = domain.configuration
  boundary_coherent :
    domain.boundary =
      independentBoundaryTrace period hPeriod domain.configuration
  ghost_pairing_classified :
    ∀ pairing, SignedPermutationInvariant pairing →
      ∀ first second sector point,
        completeVariationGhostPairingAt period hPeriod pairing first second
            sector point =
          pairing.xx * tangentVectorDot
            (first.diffeomorphismGhostAt period hPeriod sector point)
            (second.diffeomorphismGhostAt period hPeriod sector point)

def programPCommonVectorPairingCertificate4D
    (domain : ProgramPCommonGeometricDomain4D period hPeriod) :
    ProgramPCommonVectorPairingCertificate4D period hPeriod domain where
  induced_coherent := domain.induced_eq period hPeriod
  operator_coherent := domain.operator_fields_eq period hPeriod
  boundary_coherent := domain.boundary_eq_trace period hPeriod
  ghost_pairing_classified := by
    intro pairing hInvariant first second sector point
    exact completeVariationGhostPairingAt_classified period hPeriod pairing
      hInvariant first second sector point

/-- Closed witness on the canonical global common domain. -/
theorem canonicalProgramPCommonVectorPairingCertificate4D_nonempty :
    Nonempty
      (ProgramPCommonVectorPairingCertificate4D period hPeriod
        (canonicalProgramPCommonGeometricDomain4D period hPeriod)) :=
  ⟨programPCommonVectorPairingCertificate4D period hPeriod _⟩

end
end P0EFTJanusProgramPCommonVectorPairingBridge4D
end JanusFormal
