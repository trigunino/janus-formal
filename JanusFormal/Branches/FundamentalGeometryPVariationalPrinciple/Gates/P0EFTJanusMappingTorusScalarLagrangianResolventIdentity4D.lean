import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarLagrangianCompactSpectrum4D

/-!
# Resolvent identity and compactness propagation

For a fixed closed Lagrangian scalar realization, bounded resolvents at two real
spectral parameters satisfy the first resolvent identity

`R_lambda - R_mu = (lambda - mu) R_lambda R_mu`.

The two ambient resolvents consequently commute.  More importantly, compactness
of the ambient resolvent at one point propagates to every other bounded
resolvent point.  Thus compact resolvent is a property of the realization, not
of the chosen reference parameter.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarLagrangianResolventIdentity4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarOperatorGraphCompletion4D
open P0EFTJanusMappingTorusScalarClosedGraphRealization4D
open P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D
open P0EFTJanusMappingTorusScalarLagrangianResolvent4D
open P0EFTJanusMappingTorusScalarLagrangianCompactSpectrum4D

universe u v w

variable {Domain : Type u} {Ambient : Type v} {Trace : Type w}
  [AddCommGroup Domain] [Module Real Domain]
  [NormedAddCommGroup Ambient] [InnerProductSpace Real Ambient]
  [CompleteSpace Ambient]
  [NormedAddCommGroup Trace] [InnerProductSpace Real Trace]
  [CompleteSpace Trace]

/-- Difference of two shifted operators on the same Lagrangian domain. -/
theorem canonicalScalarClosedLagrangianShiftedOperator_change_parameter
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (firstParameter secondParameter : Real)
    (field : canonicalScalarClosedLagrangianDomainSubmodule
      data hClosable traceBound condition) :
    canonicalScalarClosedLagrangianShiftedOperator
        data hClosable traceBound condition firstParameter field =
      canonicalScalarClosedLagrangianShiftedOperator
          data hClosable traceBound condition secondParameter field +
        (secondParameter - firstParameter) •
          canonicalScalarClosedLagrangianDomainInclusion
            data hClosable traceBound condition field := by
  rw [canonicalScalarClosedLagrangianShiftedOperator_apply,
    canonicalScalarClosedLagrangianShiftedOperator_apply]
  module

/-- Domain-valued first resolvent identity. -/
theorem canonicalScalarClosedLagrangian_resolvent_identity_domain
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (firstParameter secondParameter : Real)
    (firstResolvent : CanonicalScalarClosedLagrangianBoundedResolventAt
      data hClosable traceBound condition firstParameter)
    (secondResolvent : CanonicalScalarClosedLagrangianBoundedResolventAt
      data hClosable traceBound condition secondParameter)
    (source : Ambient) :
    firstResolvent.resolvent source - secondResolvent.resolvent source =
      (firstParameter - secondParameter) •
        firstResolvent.resolvent
          (canonicalScalarClosedLagrangianDomainInclusion
            data hClosable traceBound condition
              (secondResolvent.resolvent source)) := by
  apply (firstResolvent.resolventPoint
    data hClosable traceBound condition firstParameter).1
  rw [map_sub, map_smul,
    firstResolvent.left_inverse,
    firstResolvent.left_inverse]
  rw [canonicalScalarClosedLagrangianShiftedOperator_change_parameter
    data hClosable traceBound condition firstParameter secondParameter,
    secondResolvent.left_inverse]
  module

/-- Ambient first resolvent identity. -/
theorem canonicalScalarClosedLagrangian_resolvent_identity
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (firstParameter secondParameter : Real)
    (firstResolvent : CanonicalScalarClosedLagrangianBoundedResolventAt
      data hClosable traceBound condition firstParameter)
    (secondResolvent : CanonicalScalarClosedLagrangianBoundedResolventAt
      data hClosable traceBound condition secondParameter)
    (source : Ambient) :
    firstResolvent.ambientResolvent
          data hClosable traceBound condition firstParameter source -
        secondResolvent.ambientResolvent
          data hClosable traceBound condition secondParameter source =
      (firstParameter - secondParameter) •
        firstResolvent.ambientResolvent
          data hClosable traceBound condition firstParameter
          (secondResolvent.ambientResolvent
            data hClosable traceBound condition secondParameter source) := by
  change canonicalScalarClosedLagrangianDomainInclusion
        data hClosable traceBound condition
        (firstResolvent.resolvent source) -
      canonicalScalarClosedLagrangianDomainInclusion
        data hClosable traceBound condition
        (secondResolvent.resolvent source) = _
  rw [← map_sub,
    canonicalScalarClosedLagrangian_resolvent_identity_domain
      data hClosable traceBound condition firstParameter secondParameter
        firstResolvent secondResolvent source,
    map_smul]
  rfl

/-- The two ambient resolvents commute. -/
theorem canonicalScalarClosedLagrangian_resolvents_commute
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (firstParameter secondParameter : Real)
    (firstResolvent : CanonicalScalarClosedLagrangianBoundedResolventAt
      data hClosable traceBound condition firstParameter)
    (secondResolvent : CanonicalScalarClosedLagrangianBoundedResolventAt
      data hClosable traceBound condition secondParameter)
    (source : Ambient) :
    firstResolvent.ambientResolvent
        data hClosable traceBound condition firstParameter
        (secondResolvent.ambientResolvent
          data hClosable traceBound condition secondParameter source) =
      secondResolvent.ambientResolvent
        data hClosable traceBound condition secondParameter
        (firstResolvent.ambientResolvent
          data hClosable traceBound condition firstParameter source) := by
  by_cases hParameters : firstParameter = secondParameter
  · subst secondParameter
    rfl
  · have hFirst := canonicalScalarClosedLagrangian_resolvent_identity
      data hClosable traceBound condition firstParameter secondParameter
        firstResolvent secondResolvent source
    have hSecond := canonicalScalarClosedLagrangian_resolvent_identity
      data hClosable traceBound condition secondParameter firstParameter
        secondResolvent firstResolvent source
    have hCoefficient : firstParameter - secondParameter ≠ 0 :=
      sub_ne_zero.mpr hParameters
    have hMultiple :
        (firstParameter - secondParameter) •
          firstResolvent.ambientResolvent
            data hClosable traceBound condition firstParameter
            (secondResolvent.ambientResolvent
              data hClosable traceBound condition secondParameter source) =
        (firstParameter - secondParameter) •
          secondResolvent.ambientResolvent
            data hClosable traceBound condition secondParameter
            (firstResolvent.ambientResolvent
              data hClosable traceBound condition firstParameter source) := by
      rw [← hFirst]
      have hSecondNeg := congrArg Neg.neg hSecond
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hSecondNeg
    exact (smul_left_cancel₀ Ambient hCoefficient).mp hMultiple

/-- Continuous-linear-map form of resolvent commutation. -/
theorem canonicalScalarClosedLagrangian_resolvents_commute_clm
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (firstParameter secondParameter : Real)
    (firstResolvent : CanonicalScalarClosedLagrangianBoundedResolventAt
      data hClosable traceBound condition firstParameter)
    (secondResolvent : CanonicalScalarClosedLagrangianBoundedResolventAt
      data hClosable traceBound condition secondParameter) :
    (firstResolvent.ambientResolvent
        data hClosable traceBound condition firstParameter).comp
      (secondResolvent.ambientResolvent
        data hClosable traceBound condition secondParameter) =
    (secondResolvent.ambientResolvent
        data hClosable traceBound condition secondParameter).comp
      (firstResolvent.ambientResolvent
        data hClosable traceBound condition firstParameter) := by
  ext source
  exact canonicalScalarClosedLagrangian_resolvents_commute
    data hClosable traceBound condition firstParameter secondParameter
      firstResolvent secondResolvent source

/-- Operator equality form of the first resolvent identity. -/
theorem canonicalScalarClosedLagrangian_resolvent_identity_clm
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (firstParameter secondParameter : Real)
    (firstResolvent : CanonicalScalarClosedLagrangianBoundedResolventAt
      data hClosable traceBound condition firstParameter)
    (secondResolvent : CanonicalScalarClosedLagrangianBoundedResolventAt
      data hClosable traceBound condition secondParameter) :
    firstResolvent.ambientResolvent
          data hClosable traceBound condition firstParameter -
        secondResolvent.ambientResolvent
          data hClosable traceBound condition secondParameter =
      (firstParameter - secondParameter) •
        ((firstResolvent.ambientResolvent
          data hClosable traceBound condition firstParameter).comp
          (secondResolvent.ambientResolvent
            data hClosable traceBound condition secondParameter)) := by
  ext source
  exact canonicalScalarClosedLagrangian_resolvent_identity
    data hClosable traceBound condition firstParameter secondParameter
      firstResolvent secondResolvent source

/-- Compactness of the ambient resolvent propagates from one bounded resolvent
point to every other bounded resolvent point. -/
theorem canonicalScalarClosedLagrangian_compactResolvent_propagates
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (compactParameter otherParameter : Real)
    (compactResolvent : CanonicalScalarClosedLagrangianBoundedResolventAt
      data hClosable traceBound condition compactParameter)
    (otherResolvent : CanonicalScalarClosedLagrangianBoundedResolventAt
      data hClosable traceBound condition otherParameter)
    (hCompact : IsCompactOperator
      (compactResolvent.ambientResolvent
        data hClosable traceBound condition compactParameter)) :
    IsCompactOperator
      (otherResolvent.ambientResolvent
        data hClosable traceBound condition otherParameter) := by
  have hComposition : IsCompactOperator
      ((compactResolvent.ambientResolvent
          data hClosable traceBound condition compactParameter).comp
        (otherResolvent.ambientResolvent
          data hClosable traceBound condition otherParameter)) := by
    simpa [Function.comp_def] using
      hCompact.comp_clm
        (otherResolvent.ambientResolvent
          data hClosable traceBound condition otherParameter)
  have hScaled : IsCompactOperator
      ((compactParameter - otherParameter) •
        ((compactResolvent.ambientResolvent
            data hClosable traceBound condition compactParameter).comp
          (otherResolvent.ambientResolvent
            data hClosable traceBound condition otherParameter))) :=
    hComposition.smul (compactParameter - otherParameter)
  have hDifference : IsCompactOperator
      (compactResolvent.ambientResolvent
          data hClosable traceBound condition compactParameter -
        (compactParameter - otherParameter) •
          ((compactResolvent.ambientResolvent
              data hClosable traceBound condition compactParameter).comp
            (otherResolvent.ambientResolvent
              data hClosable traceBound condition otherParameter))) :=
    hCompact.sub hScaled
  have hIdentity := canonicalScalarClosedLagrangian_resolvent_identity_clm
    data hClosable traceBound condition compactParameter otherParameter
      compactResolvent otherResolvent
  rw [sub_eq_iff_eq_add] at hIdentity
  have hOther :
      otherResolvent.ambientResolvent
          data hClosable traceBound condition otherParameter =
        compactResolvent.ambientResolvent
            data hClosable traceBound condition compactParameter -
          (compactParameter - otherParameter) •
            ((compactResolvent.ambientResolvent
                data hClosable traceBound condition compactParameter).comp
              (otherResolvent.ambientResolvent
                data hClosable traceBound condition otherParameter)) := by
    module at hIdentity ⊢
  rw [hOther]
  exact hDifference

/-- Once one bounded resolvent is compact, all bounded resolvents are compact
and hence admit the compact self-adjoint spectral package. -/
theorem canonicalScalarClosedLagrangian_compactResolvent_independent_of_parameter
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (compactParameter otherParameter : Real)
    (compact : CanonicalScalarClosedLagrangianCompactResolventAt
      data hClosable traceBound condition compactParameter)
    (otherResolvent : CanonicalScalarClosedLagrangianBoundedResolventAt
      data hClosable traceBound condition otherParameter) :
    CanonicalScalarClosedLagrangianCompactResolventAt
      data hClosable traceBound condition otherParameter where
  bounded := otherResolvent
  compact_ambient :=
    canonicalScalarClosedLagrangian_compactResolvent_propagates
      data hClosable traceBound condition compactParameter otherParameter
        compact.bounded otherResolvent compact.compact_ambient

end
end P0EFTJanusMappingTorusScalarLagrangianResolventIdentity4D
end JanusFormal
