import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06RelativeNullLagrangianClassification4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06InvariantJetNullDensityClassification4D

/-!
# Stratified null/boundary normal form for T06

This gate forms the explicit product of the complete bounded invariant
second-jet class from T02 and the four-stratum relative density carrier used
by T05.  For the conjunctive nullity predicate on that product, a packet is
null exactly when it has a unique normal form consisting of one constant
local density and one normalized relative boundary primitive.

The two components are independent and the relative component is still the
integrated cellular realization.  This hybrid classification is support for,
rather than closure of, T06: a later gate must replace it by a common
covariant local density carrier.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06StratifiedNullBoundaryNormalForm4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 900000

noncomputable section

open P0EFTJanusProgramPRelativeJetVariationalBicomplexCore4D
open P0EFTJanusProgramPT02InvariantLocalFunctionalBasisTerminalCertificate4D
open P0EFTJanusProgramPT05ExactT03RelativeVariationalRealization4D
open P0EFTJanusProgramPT06RelativeNullLagrangianClassification4D
open P0EFTJanusProgramPT06InvariantJetNullDensityClassification4D
open P0EFTJanusProgramPActualPhysicalSecondOrderJetProductVectorBundleCore4D
open P0EFTJanusProgramPGlobalVariationalCohomology4D
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev LocalDensity :=
  ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod

private abbrev Fiber := ActualPhysicalSecondOrderJetProductFiber

local notation "Bicomplex" => programPT05ExactT03RelativeBicomplex

/-- Independent product of one bounded local invariant density and one
horizontal four-stratum relative density. -/
structure ProgramPT06StratifiedNullBoundaryPacket4D where
  localDensity : LocalDensity period hPeriod
  relativeDensity : ProgramPT06RelativeDensity4D
  relative_horizontal : IsHorizontalDensity relativeDensity

/-- Simultaneous local and relative variational nullity. -/
def IsStratifiedVariationallyNull
    (packet : ProgramPT06StratifiedNullBoundaryPacket4D period hPeriod) : Prop :=
  IsInvariantJetVariationallyNull period hPeriod packet.localDensity ∧
    IsRelativeNullLagrangian packet.relativeDensity

/-- A normal form is a constant local representative and a normalized
primitive of the relative boundary density. -/
def IsStratifiedBoundaryNormalForm
    (packet : ProgramPT06StratifiedNullBoundaryPacket4D period hPeriod)
    (normalForm : Real × ProgramPT06RelativeBoundaryPrimitive4D) : Prop :=
  packet.localDensity =
      programPT06ConstantInvariantJetDensity period hPeriod normalForm.1 ∧
    IsNormalizedRelativeBoundaryPrimitive normalForm.2 ∧
    (Bicomplex).dH 3 0 normalForm.2 = packet.relativeDensity

/-- Exhaustive normal-form theorem for the explicit product predicate. -/
theorem stratifiedVariationallyNull_iff_existsUnique_boundaryNormalForm
    (packet : ProgramPT06StratifiedNullBoundaryPacket4D period hPeriod) :
    IsStratifiedVariationallyNull period hPeriod packet ↔
      ∃! normalForm : Real × ProgramPT06RelativeBoundaryPrimitive4D,
        IsStratifiedBoundaryNormalForm period hPeriod packet normalForm := by
  constructor
  · rintro ⟨hLocalNull, hRelativeNull⟩
    obtain ⟨constant, hConstant, hConstantUnique⟩ :=
      (invariantJetVariationallyNull_iff_existsUnique_constant
        period hPeriod packet.localDensity).1 hLocalNull
    have hBoundary : IsRelativeBoundaryTerm packet.relativeDensity :=
      (horizontalDensity_null_iff_boundary packet.relativeDensity
        packet.relative_horizontal).1 hRelativeNull
    obtain ⟨primitive, hPrimitive, hPrimitiveUnique⟩ :=
      relativeBoundaryTerm_existsUnique_normalizedPrimitive
        packet.relativeDensity hBoundary
    refine ⟨(constant, primitive), ?_, ?_⟩
    · exact ⟨hConstant, hPrimitive.1, hPrimitive.2⟩
    · rintro ⟨otherConstant, otherPrimitive⟩ hOther
      apply Prod.ext
      · exact hConstantUnique otherConstant hOther.1
      · exact hPrimitiveUnique otherPrimitive ⟨hOther.2.1, hOther.2.2⟩
  · rintro ⟨⟨constant, primitive⟩, hNormal, _⟩
    constructor
    · unfold IsInvariantJetVariationallyNull
      apply (variationallyNull_iff_exists_constant
        (programPT06InvariantJetDensityEvaluation period hPeriod
          packet.localDensity)).2
      refine ⟨constant, ?_⟩
      intro jet
      rw [hNormal.1]
      exact programPT06ConstantInvariantJetDensity_evaluation
        period hPeriod constant jet
    · apply (horizontalDensity_null_iff_boundary packet.relativeDensity
        packet.relative_horizontal).2
      exact ⟨primitive, hNormal.2.2⟩

/-- Every product packet retains the genuine T02 transition invariance of its
local component; no claim is made for the independent relative component. -/
theorem stratifiedPacket_localDensity_transitionInvariant
    (packet : ProgramPT06StratifiedNullBoundaryPacket4D period hPeriod)
    (first second : ActualPhysicalSecondOrderJetProductBundleIndex period hPeriod)
    (base : MappingTorus (fixedEquatorData period hPeriod))
    (hBase : base ∈
      (actualPhysicalSecondOrderJetProductVectorBundleCore period hPeriod
        .positiveQuarter).baseSet first ∩
      (actualPhysicalSecondOrderJetProductVectorBundleCore period hPeriod
        .positiveQuarter).baseSet second)
    (jet : Fiber) :
    programPT06InvariantJetDensityEvaluation period hPeriod packet.localDensity
        ((actualPhysicalSecondOrderJetProductVectorBundleCore period hPeriod
          .positiveQuarter).coordChange first second base jet) =
      programPT06InvariantJetDensityEvaluation period hPeriod
        packet.localDensity jet :=
  programPT06InvariantJetDensity_transitionInvariant period hPeriod
    packet.localDensity first second base hBase jet

/-- Embed a horizontal relative density into the hybrid product with zero
local representative. -/
def relativeDensityPacket
    (density : ProgramPT06RelativeDensity4D)
    (hHorizontal : IsHorizontalDensity density) :
    ProgramPT06StratifiedNullBoundaryPacket4D period hPeriod where
  localDensity :=
    programPT06ConstantInvariantJetDensity period hPeriod 0
  relativeDensity := density
  relative_horizontal := hHorizontal

/-- On the relative embedding, product nullity is exactly the already proved
relative boundary condition. -/
theorem relativeDensityPacket_null_iff_boundary
    (density : ProgramPT06RelativeDensity4D)
    (hHorizontal : IsHorizontalDensity density) :
    IsStratifiedVariationallyNull period hPeriod
        (relativeDensityPacket period hPeriod density hHorizontal) ↔
      IsRelativeBoundaryTerm density := by
  constructor
  · intro hNull
    exact (horizontalDensity_null_iff_boundary density hHorizontal).1 hNull.2
  · intro hBoundary
    constructor
    · unfold IsInvariantJetVariationallyNull
      apply (variationallyNull_iff_exists_constant
        (programPT06InvariantJetDensityEvaluation period hPeriod
          (programPT06ConstantInvariantJetDensity period hPeriod 0))).2
      exact ⟨0, programPT06ConstantInvariantJetDensity_evaluation
        period hPeriod 0⟩
    · exact (horizontalDensity_null_iff_boundary density hHorizontal).2 hBoundary

end

end P0EFTJanusProgramPT06StratifiedNullBoundaryNormalForm4D
end JanusFormal
