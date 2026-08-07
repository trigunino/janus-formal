import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAH10RobinSixBlockBound4D

/-!
# Named bounds for the six non-Robin Candidate-A blocks

The indexed H11 interface is convenient for finite summation but inconvenient
for the actual PDE work.  This file exposes one named constant and estimate for
each remaining physical block and converts them to the finite indexed packet.
No estimate for matter, LL or Robin is accepted here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateASixNamedPhysicalBounds4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPGlobalCandidateASevenPhysicalContinuousExtension4D

variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]

/-- Six named continuous forms on the common H11 domain. -/
structure GlobalCandidateASixNamedPhysicalForms4D where
  candidateA : E →L[Real] E →L[Real] Real
  einsteinHilbertPlus : E →L[Real] E →L[Real] Real
  einsteinHilbertMinus : E →L[Real] E →L[Real] Real
  maxwellPlus : E →L[Real] E →L[Real] Real
  maxwellMinus : E →L[Real] E →L[Real] Real
  finiteBV : E →L[Real] E →L[Real] Real

/-- Convert the named forms to the exact six-element index used by H11. -/
def GlobalCandidateASixNamedPhysicalForms4D.indexed
    (forms : GlobalCandidateASixNamedPhysicalForms4D (E := E)) :
    GlobalCandidateANonRobinPhysicalBlock → E →L[Real] E →L[Real] Real
  | .candidateA => forms.candidateA
  | .einsteinHilbertPlus => forms.einsteinHilbertPlus
  | .einsteinHilbertMinus => forms.einsteinHilbertMinus
  | .maxwellPlus => forms.maxwellPlus
  | .maxwellMinus => forms.maxwellMinus
  | .finiteBV => forms.finiteBV

/-- One explicit product estimate for each of the six remaining blocks. -/
structure GlobalCandidateASixNamedPhysicalBounds4D
    (forms : GlobalCandidateASixNamedPhysicalForms4D (E := E)) : Prop where
  candidateAConstant : Real
  candidateAConstant_nonneg : 0 ≤ candidateAConstant
  candidateA_estimate : ∀ first second,
    ‖forms.candidateA first second‖ ≤
      candidateAConstant * ‖first‖ * ‖second‖
  einsteinHilbertPlusConstant : Real
  einsteinHilbertPlusConstant_nonneg : 0 ≤ einsteinHilbertPlusConstant
  einsteinHilbertPlus_estimate : ∀ first second,
    ‖forms.einsteinHilbertPlus first second‖ ≤
      einsteinHilbertPlusConstant * ‖first‖ * ‖second‖
  einsteinHilbertMinusConstant : Real
  einsteinHilbertMinusConstant_nonneg : 0 ≤ einsteinHilbertMinusConstant
  einsteinHilbertMinus_estimate : ∀ first second,
    ‖forms.einsteinHilbertMinus first second‖ ≤
      einsteinHilbertMinusConstant * ‖first‖ * ‖second‖
  maxwellPlusConstant : Real
  maxwellPlusConstant_nonneg : 0 ≤ maxwellPlusConstant
  maxwellPlus_estimate : ∀ first second,
    ‖forms.maxwellPlus first second‖ ≤
      maxwellPlusConstant * ‖first‖ * ‖second‖
  maxwellMinusConstant : Real
  maxwellMinusConstant_nonneg : 0 ≤ maxwellMinusConstant
  maxwellMinus_estimate : ∀ first second,
    ‖forms.maxwellMinus first second‖ ≤
      maxwellMinusConstant * ‖first‖ * ‖second‖
  finiteBVConstant : Real
  finiteBVConstant_nonneg : 0 ≤ finiteBVConstant
  finiteBV_estimate : ∀ first second,
    ‖forms.finiteBV first second‖ ≤
      finiteBVConstant * ‖first‖ * ‖second‖

/-- Indexed constants generated from the six named estimates. -/
def GlobalCandidateASixNamedPhysicalBounds4D.indexedConstant
    {forms : GlobalCandidateASixNamedPhysicalForms4D (E := E)}
    (bounds : GlobalCandidateASixNamedPhysicalBounds4D forms) :
    GlobalCandidateANonRobinPhysicalBlock → Real
  | .candidateA => bounds.candidateAConstant
  | .einsteinHilbertPlus => bounds.einsteinHilbertPlusConstant
  | .einsteinHilbertMinus => bounds.einsteinHilbertMinusConstant
  | .maxwellPlus => bounds.maxwellPlusConstant
  | .maxwellMinus => bounds.maxwellMinusConstant
  | .finiteBV => bounds.finiteBVConstant

/-- Every indexed constant is nonnegative. -/
theorem GlobalCandidateASixNamedPhysicalBounds4D.indexedConstant_nonneg
    {forms : GlobalCandidateASixNamedPhysicalForms4D (E := E)}
    (bounds : GlobalCandidateASixNamedPhysicalBounds4D forms) :
    ∀ block, 0 ≤ bounds.indexedConstant block := by
  intro block
  cases block with
  | candidateA => exact bounds.candidateAConstant_nonneg
  | einsteinHilbertPlus => exact bounds.einsteinHilbertPlusConstant_nonneg
  | einsteinHilbertMinus => exact bounds.einsteinHilbertMinusConstant_nonneg
  | maxwellPlus => exact bounds.maxwellPlusConstant_nonneg
  | maxwellMinus => exact bounds.maxwellMinusConstant_nonneg
  | finiteBV => exact bounds.finiteBVConstant_nonneg

/-- The six named estimates fill the indexed H11 estimate automatically. -/
theorem GlobalCandidateASixNamedPhysicalBounds4D.indexed_estimate
    {forms : GlobalCandidateASixNamedPhysicalForms4D (E := E)}
    (bounds : GlobalCandidateASixNamedPhysicalBounds4D forms) :
    ∀ block first second,
      ‖forms.indexed block first second‖ ≤
        bounds.indexedConstant block * ‖first‖ * ‖second‖ := by
  intro block first second
  cases block with
  | candidateA => exact bounds.candidateA_estimate first second
  | einsteinHilbertPlus =>
      exact bounds.einsteinHilbertPlus_estimate first second
  | einsteinHilbertMinus =>
      exact bounds.einsteinHilbertMinus_estimate first second
  | maxwellPlus => exact bounds.maxwellPlus_estimate first second
  | maxwellMinus => exact bounds.maxwellMinus_estimate first second
  | finiteBV => exact bounds.finiteBV_estimate first second

/-- Public conversion checkpoint from six named PDE estimates to the finite
indexed H11 format. -/
theorem candidateA_six_named_physical_bounds_gate
    (forms : GlobalCandidateASixNamedPhysicalForms4D (E := E))
    (bounds : GlobalCandidateASixNamedPhysicalBounds4D forms) :
    (∀ block, 0 ≤ bounds.indexedConstant block) ∧
    (∀ block first second,
      ‖forms.indexed block first second‖ ≤
        bounds.indexedConstant block * ‖first‖ * ‖second‖) :=
  ⟨bounds.indexedConstant_nonneg, bounds.indexed_estimate⟩

end
end P0EFTJanusProgramPGlobalCandidateASixNamedPhysicalBounds4D
end JanusFormal
