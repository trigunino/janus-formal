import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12CurvatureJetJointSmooth4D
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-! Jointly smooth Einstein density and its partial metric-jet derivatives. -/
namespace JanusFormal.P0EFTJanusProgramPT12EinsteinSymbolJointSmooth4D
set_option autoImplicit false
noncomputable section
open scoped ContDiff
open P0EFTJanusProgramPT12CurvatureJetSymbol4D
open P0EFTJanusProgramPT12CurvatureJetJointSmooth4D

abbrev EinsteinSymbolParameters := Real × MetricFirstJet × MetricSecondJet
abbrev EinsteinSymbolInput := EinsteinSymbolParameters × CurvatureJet
local instance : NormedAddCommGroup CurvatureJet := inferInstance
local instance : NormedSpace Real CurvatureJet := inferInstance
local instance : NormedAddCommGroup EinsteinSymbolInput := inferInstance
local instance : NormedSpace Real EinsteinSymbolInput := inferInstance

def einsteinSymbol (gravitational cosmological : Real) (input : EinsteinSymbolInput) : Real :=
  input.1.1 * ((1 / (2 * gravitational)) *
    (jetScalarCurvature input.1.2.1 input.1.2.2 input.2 - 2 * cosmological))

theorem einsteinSymbol_contDiff (gravitational cosmological : Real) :
    ContDiff Real ∞ (einsteinSymbol gravitational cosmological) := by
  unfold einsteinSymbol
  fun_prop

def einsteinSymbolGradient (gravitational cosmological : Real) (input : EinsteinSymbolInput) :
    CurvatureJet →L[Real] Real :=
  fderiv Real (fun jet => einsteinSymbol gravitational cosmological (input.1, jet)) input.2

theorem einsteinSymbolGradient_contDiff (gravitational cosmological : Real) :
    ContDiff Real ∞ (einsteinSymbolGradient gravitational cosmological) := by
  have h : ContDiff Real ∞ (fun input : EinsteinSymbolInput × CurvatureJet =>
      einsteinSymbol gravitational cosmological (input.1.1, input.2)) :=
    (einsteinSymbol_contDiff gravitational cosmological).comp (contDiff_fst.fst.prodMk contDiff_snd)
  exact h.fderiv (f := fun (input : EinsteinSymbolInput) (jet : CurvatureJet) => einsteinSymbol gravitational cosmological (input.1, jet))
    (g := fun input : EinsteinSymbolInput => input.2) contDiff_snd (by simp)

def einsteinSymbolHessian (gravitational cosmological : Real) (input : EinsteinSymbolInput) :
    CurvatureJet →L[Real] CurvatureJet →L[Real] Real :=
  fderiv Real (fderiv Real (fun jet => einsteinSymbol gravitational cosmological (input.1, jet))) input.2

theorem einsteinSymbolHessian_contDiff (gravitational cosmological : Real) :
    ContDiff Real ∞ (einsteinSymbolHessian gravitational cosmological) := by
  have h : ContDiff Real ∞ (fun input : EinsteinSymbolInput × CurvatureJet =>
      einsteinSymbolGradient gravitational cosmological (input.1.1, input.2)) :=
    (einsteinSymbolGradient_contDiff gravitational cosmological).comp (contDiff_fst.fst.prodMk contDiff_snd)
  exact h.fderiv (f := fun (input : EinsteinSymbolInput) (jet : CurvatureJet) => einsteinSymbolGradient gravitational cosmological (input.1, jet))
    (g := fun input : EinsteinSymbolInput => input.2) contDiff_snd (by simp)

end
end JanusFormal.P0EFTJanusProgramPT12EinsteinSymbolJointSmooth4D
