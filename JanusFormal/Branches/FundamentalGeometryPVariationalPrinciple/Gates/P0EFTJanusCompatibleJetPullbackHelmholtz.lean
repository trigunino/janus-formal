import Mathlib
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusHessianHelmholtzReconstruction

namespace JanusFormal
namespace P0EFTJanusCompatibleJetPullbackHelmholtz

set_option autoImplicit false

open P0EFTJanusHessianHelmholtzReconstruction

/-- Transpose of a two-sector linear map. -/
def transposeOperator
    (operator : LinearOperator2) : LinearOperator2 :=
  { xx := operator.xx
    xy := operator.yx
    yx := operator.xy
    yy := operator.yy }

/-- Composition `first ∘ second`. -/
def composeOperators
    (first second : LinearOperator2) : LinearOperator2 :=
  { xx := first.xx * second.xx + first.xy * second.yx
    xy := first.xx * second.xy + first.xy * second.yy
    yx := first.yx * second.xx + first.yy * second.yx
    yy := first.yx * second.xy + first.yy * second.yy }

/-- Pullback of a bilinear/Hessian operator along a linearized compatible-jet map. -/
def pullbackOperator
    (jetMap targetHessian : LinearOperator2) : LinearOperator2 :=
  composeOperators (transposeOperator jetMap)
    (composeOperators targetHessian jetMap)

/-- Transposition is involutive. -/
@[simp] theorem transpose_operator_involutive
    (operator : LinearOperator2) :
    transposeOperator (transposeOperator operator) = operator := by
  rfl

/-- Formal self-adjointness is equality with the transpose. -/
theorem formally_self_adjoint_iff_transpose
    (operator : LinearOperator2) :
    FormallySelfAdjoint operator ↔
      transposeOperator operator = operator := by
  constructor
  · intro hSelfAdjoint
    apply LinearOperator2.ext
    · rfl
    · exact hSelfAdjoint.symm
    · exact hSelfAdjoint
    · rfl
  · intro hTranspose
    have hXY := congrArg LinearOperator2.xy hTranspose
    simpa [transposeOperator, FormallySelfAdjoint] using hXY

/--
Core bridge theorem: pulling back a symmetric target Hessian along any
linearized jet/compatibility map gives a symmetric source Hessian.
-/
theorem pullback_operator_formally_self_adjoint
    (jetMap targetHessian : LinearOperator2)
    (hTarget : FormallySelfAdjoint targetHessian) :
    FormallySelfAdjoint
      (pullbackOperator jetMap targetHessian) := by
  unfold FormallySelfAdjoint pullbackOperator
    composeOperators transposeOperator
  unfold FormallySelfAdjoint at hTarget
  rw [hTarget]
  ring

/-- Every pullback of an actual Hessian passes the quadratic Helmholtz test. -/
theorem pullback_of_hessian_is_helmholtz
    (jetMap : LinearOperator2)
    (targetPotential : QuadraticPotential2) :
    FormallySelfAdjoint
      (pullbackOperator jetMap
        (hessianOperator targetPotential)) := by
  exact pullback_operator_formally_self_adjoint
    jetMap (hessianOperator targetPotential)
    (hessian_formally_self_adjoint targetPotential)

/-- Therefore a quadratic source action exists for the pulled-back Hessian. -/
theorem pullback_of_hessian_has_source_potential
    (jetMap : LinearOperator2)
    (targetPotential : QuadraticPotential2) :
    ∃ sourcePotential : QuadraticPotential2,
      hessianOperator sourcePotential =
        pullbackOperator jetMap
          (hessianOperator targetPotential) := by
  exact (helmholtz_realizability_iff
    (pullbackOperator jetMap
      (hessianOperator targetPotential))).2
    (pullback_of_hessian_is_helmholtz
      jetMap targetPotential)

/-- Identity compatible-jet map. -/
def identityJetMap : LinearOperator2 :=
  { xx := 1, xy := 0, yx := 0, yy := 1 }

/-- A nonreciprocal target response. -/
def nonreciprocalTargetResponse : LinearOperator2 :=
  { xx := 1, xy := 1, yx := 0, yy := 1 }

/-- Pullback along the identity leaves an operator unchanged. -/
@[simp] theorem identity_pullback
    (targetHessian : LinearOperator2) :
    pullbackOperator identityJetMap targetHessian = targetHessian := by
  apply LinearOperator2.ext <;>
    simp [pullbackOperator, composeOperators,
      transposeOperator, identityJetMap]

/--
Counterexample to the speculative implication: a perfectly valid jet map does
not turn a nonreciprocal response into a Helmholtz operator.
-/
theorem compatible_jet_map_alone_does_not_imply_helmholtz :
    Not (FormallySelfAdjoint
      (pullbackOperator identityJetMap
        nonreciprocalTargetResponse)) := by
  rw [identity_pullback]
  norm_num [FormallySelfAdjoint,
    nonreciprocalTargetResponse]

/-- The nonreciprocal example has no quadratic variational primitive. -/
theorem compatible_geometry_can_carry_nonvariational_response :
    Not (∃ potential : QuadraticPotential2,
      hessianOperator potential =
        pullbackOperator identityJetMap
          nonreciprocalTargetResponse) := by
  rw [identity_pullback]
  exact nonsymmetric_operator_is_not_variational
    nonreciprocalTargetResponse (by norm_num [nonreciprocalTargetResponse])

/-- Geometric compatibility and variational reciprocity are separate inputs. -/
structure CompatibilityHelmholtzBridgeStatus where
  compatibleJetSpaceConstructed : Prop
  gaussCodazziRicciBianchiConstraintsImposed : Prop
  linearizedJetMapConstructed : Prop
  targetBilinearResponseConstructed : Prop
  targetResponseSelfAdjointProved : Prop
  pullbackFormulaDerived : Prop
  sourceHelmholtzProved : Prop
  sourceActionReconstructed : Prop

/-- Closure of the positive bridge. -/
def compatibilityHelmholtzBridgeClosed
    (s : CompatibilityHelmholtzBridgeStatus) : Prop :=
  s.compatibleJetSpaceConstructed /\
  s.gaussCodazziRicciBianchiConstraintsImposed /\
  s.linearizedJetMapConstructed /\
  s.targetBilinearResponseConstructed /\
  s.targetResponseSelfAdjointProved /\
  s.pullbackFormulaDerived /\
  s.sourceHelmholtzProved /\
  s.sourceActionReconstructed

/-- Missing target reciprocity blocks the proposed geometric-to-variational bridge. -/
theorem missing_target_reciprocity_blocks_bridge
    (s : CompatibilityHelmholtzBridgeStatus)
    (hMissing : Not s.targetResponseSelfAdjointProved) :
    Not (compatibilityHelmholtzBridgeClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.1

/--
Corrected P.F verdict:

* Gauss--Codazzi--Ricci--Bianchi define the admissible/compatible jet locus and
  its linearization `J`;
* Helmholtz does not follow from that compatibility alone;
* Helmholtz follows when the response on compatible invariants is represented
  by a self-adjoint bilinear form `H`, because the source Hessian is `Jᵀ H J`.
-/
structure CorrectedPFVerdict where
  geometrySuppliesCompatibleJetMap : Prop
  geometryAloneDoesNotImplyHelmholtz : Prop
  selfAdjointTargetPairingIsAdditional : Prop
  pullbackHessianFormulaDerived : Prop
  pullbackAutomaticallyHelmholtz : Prop
  variationalPrimitiveExistsLocally : Prop


def correctedPFVerdictClosed
    (s : CorrectedPFVerdict) : Prop :=
  s.geometrySuppliesCompatibleJetMap /\
  s.geometryAloneDoesNotImplyHelmholtz /\
  s.selfAdjointTargetPairingIsAdditional /\
  s.pullbackHessianFormulaDerived /\
  s.pullbackAutomaticallyHelmholtz /\
  s.variationalPrimitiveExistsLocally

end P0EFTJanusCompatibleJetPullbackHelmholtz
end JanusFormal
