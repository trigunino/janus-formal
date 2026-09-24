import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12CurvatureJetSymbol4D
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-! Finite Maxwell density in the actual inverse metric and curvature slots. -/
namespace JanusFormal.P0EFTJanusProgramPT12MaxwellJetSymbol4D
set_option autoImplicit false
noncomputable section
open scoped ContDiff BigOperators
open P0EFTJanusProgramPT12CurvatureJetSymbol4D

abbrev MaxwellCurvature := Fin 2 → MetricMatrix
abbrev MaxwellJet := MetricMatrix × MaxwellCurvature
abbrev MaxwellSymbolInput := Real × MaxwellJet
local instance : NormedAddCommGroup MaxwellJet := inferInstance
local instance : NormedSpace Real MaxwellJet := inferInstance
local instance : NormedAddCommGroup MaxwellSymbolInput := inferInstance
local instance : NormedSpace Real MaxwellSymbolInput := inferInstance

def maxwellSymbol (input : MaxwellSymbolInput) : Real :=
  input.1 * (-(1 / 4 : Real) *
    ∑ component, ∑ row, ∑ column, ∑ first, ∑ second,
      input.2.1 row first * input.2.1 column second *
        input.2.2 component row column * input.2.2 component first second)

theorem maxwellSymbol_contDiff : ContDiff Real ∞ maxwellSymbol := by
  unfold maxwellSymbol
  fun_prop

theorem maxwellSymbol_jet_contDiff (volume : Real) :
    ContDiff Real ∞ (fun jet => maxwellSymbol (volume, jet)) :=
  maxwellSymbol_contDiff.comp (contDiff_const.prodMk contDiff_id)

def maxwellSymbolGradient (input : MaxwellSymbolInput) : MaxwellJet →L[Real] Real :=
  fderiv Real (fun jet => maxwellSymbol (input.1, jet)) input.2

theorem maxwellSymbolGradient_contDiff : ContDiff Real ∞ maxwellSymbolGradient := by
  have h : ContDiff Real ∞ (fun input : MaxwellSymbolInput × MaxwellJet =>
      maxwellSymbol (input.1.1, input.2)) :=
    maxwellSymbol_contDiff.comp (contDiff_fst.fst.prodMk contDiff_snd)
  exact h.fderiv (f := fun (input : MaxwellSymbolInput) (jet : MaxwellJet) =>
    maxwellSymbol (input.1, jet)) (g := fun input : MaxwellSymbolInput => input.2)
      contDiff_snd (by simp)

def maxwellSymbolHessian (input : MaxwellSymbolInput) : MaxwellJet →L[Real] MaxwellJet →L[Real] Real :=
  fderiv Real (fderiv Real (fun jet => maxwellSymbol (input.1, jet))) input.2

theorem maxwellSymbolHessian_contDiff : ContDiff Real ∞ maxwellSymbolHessian := by
  have h : ContDiff Real ∞ (fun input : MaxwellSymbolInput × MaxwellJet =>
      maxwellSymbolGradient (input.1.1, input.2)) :=
    maxwellSymbolGradient_contDiff.comp (contDiff_fst.fst.prodMk contDiff_snd)
  exact h.fderiv (f := fun (input : MaxwellSymbolInput) (jet : MaxwellJet) =>
    maxwellSymbolGradient (input.1, jet)) (g := fun input : MaxwellSymbolInput => input.2)
      contDiff_snd (by simp)

end
end JanusFormal.P0EFTJanusProgramPT12MaxwellJetSymbol4D
