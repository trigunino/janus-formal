import Mathlib
import JanusFormal.Branches.RP4TwistedFourFormAlpha.Gates.P0EFTJanusLLBraneAuxiliaryFluxClosure

namespace JanusFormal.P0EFTJanusLLGhostOperatorFrontier

set_option autoImplicit false

open P0EFTJanusLLBraneAuxiliaryFluxClosure

/-- A ghost completion adds information absent from the reduced algebraic LL
constraint data. `ghostOperatorLabel` is only a discriminator. -/
structure LLReducedGhostCompletion where
  reduced : MinimalWrongSignMaxwellSector
  ghostOperatorLabel : ℝ

def completionWithLabel
    (reduced : MinimalWrongSignMaxwellSector) (label : ℝ) :
    LLReducedGhostCompletion :=
  { reduced := reduced, ghostOperatorLabel := label }

/-- The same reduced LL equations admit distinct ghost-operator labels. Thus
`F^2=1/2`, `M=1/8`, `a0=1/8` do not determine the LL FP/BV operator. -/
theorem reduced_ll_constraints_do_not_select_ghost_operator
    (reduced : MinimalWrongSignMaxwellSector) :
    (completionWithLabel reduced 0).reduced =
        (completionWithLabel reduced 1).reduced ∧
      (completionWithLabel reduced 0).ghostOperatorLabel ≠
        (completionWithLabel reduced 1).ghostOperatorLabel := by
  constructor
  · rfl
  · norm_num [completionWithLabel]

structure LLQuantumRGCompletion where
  reduced : MinimalWrongSignMaxwellSector
  gaugeFixedHessianLabel : ℝ
  sexticBetaContribution : ℝ

def quantumCompletion
    (reduced : MinimalWrongSignMaxwellSector) (label betaLL : ℝ) :
    LLQuantumRGCompletion :=
  { reduced := reduced
    gaugeFixedHessianLabel := label
    sexticBetaContribution := betaLL }

/-- Identical reduced LL constraints admit different quantum Hessians and beta
contributions. Therefore `beta_LL` cannot be extracted from the reduced saddle
equations alone. -/
theorem reduced_ll_constraints_do_not_determine_beta
    (reduced : MinimalWrongSignMaxwellSector) :
    (quantumCompletion reduced 0 0).reduced =
        (quantumCompletion reduced 1 1).reduced ∧
      (quantumCompletion reduced 0 0).gaugeFixedHessianLabel ≠
        (quantumCompletion reduced 1 1).gaugeFixedHessianLabel ∧
      (quantumCompletion reduced 0 0).sexticBetaContribution ≠
        (quantumCompletion reduced 1 1).sexticBetaContribution := by
  norm_num [quantumCompletion]

structure LLGhostDerivationStatus where
  localMeasureFieldsSpecified : Prop
  fullWorldvolumeGaugeGroupSpecified : Prop
  reducibilityTowerSpecified : Prop
  gaugeFermionSpecified : Prop
  fpOrBvOperatorDerived : Prop
  llGhostVerticesDerived : Prop
  globalZeroModesSeparated : Prop

def llGhostDerivationClosed (s : LLGhostDerivationStatus) : Prop :=
  s.localMeasureFieldsSpecified ∧
  s.fullWorldvolumeGaugeGroupSpecified ∧
  s.reducibilityTowerSpecified ∧
  s.gaugeFermionSpecified ∧
  s.fpOrBvOperatorDerived ∧
  s.llGhostVerticesDerived ∧
  s.globalZeroModesSeparated

end JanusFormal.P0EFTJanusLLGhostOperatorFrontier
