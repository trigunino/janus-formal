import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarCompletedBoundaryTripleCompactSpectrum4D

/-!
# Resolvent identity on a completed scalar boundary triple

For two bounded direct resolvents, the usual identity holds on the completed
Lagrangian realization:

`R_lambda - R_mu = (lambda-mu) R_lambda I R_mu`.

After ambient inclusion this becomes the standard ambient resolvent identity.
It implies commutation of all real resolvents and propagates compactness from one
resolvent parameter to every other bounded resolvent parameter.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarCompletedBoundaryTripleResolventIdentity4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D
open P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleResolvent4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleCompactSpectrum4D

universe u v w

variable {Domain : Type u} {Ambient : Type v} {Trace : Type w}
  [AddCommGroup Domain] [Module Real Domain]
  [NormedAddCommGroup Ambient] [InnerProductSpace Real Ambient]
  [CompleteSpace Ambient]
  [NormedAddCommGroup Trace] [InnerProductSpace Real Trace]
  [CompleteSpace Trace]

namespace CanonicalScalarCompletedBoundaryTripleData

/-- Domain-valued direct resolvent identity. -/
theorem lagrangianResolvent_sub_resolvent_apply
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (firstParameter secondParameter : Real)
    (firstResolvent : triple.LagrangianBoundedResolventAt
      condition firstParameter)
    (secondResolvent : triple.LagrangianBoundedResolventAt
      condition secondParameter)
    (source : Ambient) :
    firstResolvent.resolvent source - secondResolvent.resolvent source =
      (firstParameter - secondParameter) •
        firstResolvent.resolvent
          (triple.lagrangianInclusion condition
            (secondResolvent.resolvent source)) := by
  let secondField := secondResolvent.resolvent source
  have hSecond :
      triple.lagrangianShiftedOperator condition secondParameter
        secondField = source :=
    secondResolvent.left_inverse source
  have hFirstApplied := firstResolvent.right_inverse secondField
  have hShiftRelation :
      triple.lagrangianShiftedOperator condition firstParameter secondField =
        source + (secondParameter - firstParameter) •
          triple.lagrangianInclusion condition secondField := by
    rw [triple.lagrangianShiftedOperator_apply,
      triple.lagrangianShiftedOperator_apply] at hSecond ⊢
    rw [← hSecond]
    module
  rw [hShiftRelation, map_add, map_smul,
    firstResolvent.left_inverse] at hFirstApplied
  have hRearranged := congrArg
    (fun field => firstResolvent.resolvent source - field) hFirstApplied
  simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm,
    sub_smul] using hRearranged

/-- Domain-valued direct resolvent identity as equality of continuous maps. -/
theorem lagrangianResolvent_sub_resolvent
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (firstParameter secondParameter : Real)
    (firstResolvent : triple.LagrangianBoundedResolventAt
      condition firstParameter)
    (secondResolvent : triple.LagrangianBoundedResolventAt
      condition secondParameter) :
    firstResolvent.resolvent - secondResolvent.resolvent =
      (firstParameter - secondParameter) •
        (firstResolvent.resolvent.comp
          (secondResolvent.ambientResolvent
            triple condition secondParameter)) := by
  ext source
  exact triple.lagrangianResolvent_sub_resolvent_apply condition
    firstParameter secondParameter firstResolvent secondResolvent source

/-- Ambient direct resolvent identity. -/
theorem ambientResolvent_sub_resolvent
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (firstParameter secondParameter : Real)
    (firstResolvent : triple.LagrangianBoundedResolventAt
      condition firstParameter)
    (secondResolvent : triple.LagrangianBoundedResolventAt
      condition secondParameter) :
    firstResolvent.ambientResolvent triple condition firstParameter -
        secondResolvent.ambientResolvent triple condition secondParameter =
      (firstParameter - secondParameter) •
        ((firstResolvent.ambientResolvent triple condition firstParameter).comp
          (secondResolvent.ambientResolvent
            triple condition secondParameter)) := by
  ext source
  change triple.lagrangianInclusion condition
      (firstResolvent.resolvent source - secondResolvent.resolvent source) = _
  rw [triple.lagrangianResolvent_sub_resolvent_apply]
  simp

/-- Ambient direct resolvents commute. -/
theorem ambientResolvent_commute
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (firstParameter secondParameter : Real)
    (firstResolvent : triple.LagrangianBoundedResolventAt
      condition firstParameter)
    (secondResolvent : triple.LagrangianBoundedResolventAt
      condition secondParameter) :
    (firstResolvent.ambientResolvent triple condition firstParameter).comp
        (secondResolvent.ambientResolvent triple condition secondParameter) =
      (secondResolvent.ambientResolvent triple condition secondParameter).comp
        (firstResolvent.ambientResolvent triple condition firstParameter) := by
  by_cases hParameters : firstParameter = secondParameter
  · subst hParameters
    have hResolventEquality : firstResolvent.resolvent = secondResolvent.resolvent := by
      ext source
      apply (triple.lagrangianShiftedOperator
        condition secondParameter).toLinearMap.ker_eq_bot.mp
      rw [map_sub, firstResolvent.left_inverse, secondResolvent.left_inverse,
        sub_self]
    rw [hResolventEquality]
  · have hFirst := triple.ambientResolvent_sub_resolvent condition
      firstParameter secondParameter firstResolvent secondResolvent
    have hSecond := triple.ambientResolvent_sub_resolvent condition
      secondParameter firstParameter secondResolvent firstResolvent
    have hDifference : firstParameter - secondParameter ≠ 0 :=
      sub_ne_zero.mpr hParameters
    have hScaled :
        (firstParameter - secondParameter) •
            ((firstResolvent.ambientResolvent triple condition firstParameter).comp
              (secondResolvent.ambientResolvent triple condition secondParameter)) =
          (firstParameter - secondParameter) •
            ((secondResolvent.ambientResolvent triple condition secondParameter).comp
              (firstResolvent.ambientResolvent triple condition firstParameter)) := by
      rw [← hFirst]
      rw [← neg_sub secondParameter firstParameter,
        smul_neg, ← neg_smul]
      rw [← hSecond]
      module
    exact (smul_right_injective _ hDifference) hScaled

/-- Compactness of one ambient resolvent propagates to every other bounded
ambient resolvent. -/
theorem compact_ambientResolvent_of_compact
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (compactParameter targetParameter : Real)
    (compactResolvent : triple.LagrangianCompactResolventAt
      condition compactParameter)
    (targetResolvent : triple.LagrangianBoundedResolventAt
      condition targetParameter) :
    IsCompactOperator
      (targetResolvent.ambientResolvent triple condition targetParameter) := by
  have hIdentity := triple.ambientResolvent_sub_resolvent condition
    targetParameter compactParameter targetResolvent compactResolvent.bounded
  have hComposition : IsCompactOperator
      ((targetResolvent.ambientResolvent triple condition targetParameter).comp
        (compactResolvent.bounded.ambientResolvent
          triple condition compactParameter)) :=
    compactResolvent.compact_ambient.clm_comp
      (targetResolvent.ambientResolvent triple condition targetParameter)
  have hCorrection : IsCompactOperator
      ((targetParameter - compactParameter) •
        ((targetResolvent.ambientResolvent triple condition targetParameter).comp
          (compactResolvent.bounded.ambientResolvent
            triple condition compactParameter))) :=
    hComposition.smul _
  have hSum : IsCompactOperator
      (compactResolvent.bounded.ambientResolvent
          triple condition compactParameter +
        (targetParameter - compactParameter) •
          ((targetResolvent.ambientResolvent triple condition targetParameter).comp
            (compactResolvent.bounded.ambientResolvent
              triple condition compactParameter))) :=
    compactResolvent.compact_ambient.add hCorrection
  have hTargetEquality :
      targetResolvent.ambientResolvent triple condition targetParameter =
        compactResolvent.bounded.ambientResolvent
            triple condition compactParameter +
          (targetParameter - compactParameter) •
            ((targetResolvent.ambientResolvent triple condition targetParameter).comp
              (compactResolvent.bounded.ambientResolvent
                triple condition compactParameter)) := by
    module at hIdentity ⊢
  rw [hTargetEquality]
  exact hSum

/-- Compact target resolvent package propagated from one compact parameter. -/
def compactResolventAt_of_compact
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (compactParameter targetParameter : Real)
    (compactResolvent : triple.LagrangianCompactResolventAt
      condition compactParameter)
    (targetResolvent : triple.LagrangianBoundedResolventAt
      condition targetParameter) :
    triple.LagrangianCompactResolventAt condition targetParameter where
  bounded := targetResolvent
  compact_ambient := triple.compact_ambientResolvent_of_compact condition
    compactParameter targetParameter compactResolvent targetResolvent

/-- Direct resolvent-identity certificate. -/
theorem directResolventIdentity_certificate
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (firstParameter secondParameter : Real)
    (firstResolvent : triple.LagrangianBoundedResolventAt
      condition firstParameter)
    (secondResolvent : triple.LagrangianBoundedResolventAt
      condition secondParameter) :
    firstResolvent.ambientResolvent triple condition firstParameter -
        secondResolvent.ambientResolvent triple condition secondParameter =
      (firstParameter - secondParameter) •
        ((firstResolvent.ambientResolvent triple condition firstParameter).comp
          (secondResolvent.ambientResolvent
            triple condition secondParameter)) ∧
      (firstResolvent.ambientResolvent triple condition firstParameter).comp
          (secondResolvent.ambientResolvent triple condition secondParameter) =
        (secondResolvent.ambientResolvent triple condition secondParameter).comp
          (firstResolvent.ambientResolvent triple condition firstParameter) :=
  ⟨triple.ambientResolvent_sub_resolvent condition
      firstParameter secondParameter firstResolvent secondResolvent,
    triple.ambientResolvent_commute condition
      firstParameter secondParameter firstResolvent secondResolvent⟩

end CanonicalScalarCompletedBoundaryTripleData

end
end P0EFTJanusMappingTorusScalarCompletedBoundaryTripleResolventIdentity4D
end JanusFormal
