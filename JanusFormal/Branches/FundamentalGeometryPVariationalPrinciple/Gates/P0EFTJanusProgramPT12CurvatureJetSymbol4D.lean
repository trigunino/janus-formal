import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! Finite polynomial formula for the native nonholonomic curvature.
The inverse metric is an independent slot here; the native bridge supplies its actual value. -/
namespace JanusFormal.P0EFTJanusProgramPT12CurvatureJetSymbol4D
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators ContDiff

abbrev MetricMatrix := Fin 4 → Fin 4 → Real
abbrev MetricFirstJet := Fin 4 → MetricMatrix
abbrev MetricSecondJet := Fin 4 → MetricFirstJet
abbrev CurvatureJet := MetricMatrix × MetricMatrix × MetricFirstJet × MetricSecondJet

def jetKoszul (bracket : MetricFirstJet) (jet : CurvatureJet) (first second lower : Fin 4) : Real :=
  (1 / 2 : Real) * (jet.2.2.1 first second lower + jet.2.2.1 second lower first -
    jet.2.2.1 lower first second - ∑ k, bracket second lower k * jet.1 first k +
    ∑ k, bracket lower first k * jet.1 second k + ∑ k, bracket first second k * jet.1 lower k)

def jetInverseDerivative (jet : CurvatureJet) (direction upper lower : Fin 4) : Real :=
  -∑ first, ∑ second, jet.2.1 upper first * jet.2.2.1 direction first second * jet.2.1 second lower

def jetStructureDerivative (bracket : MetricFirstJet) (bracketDerivative : MetricSecondJet)
    (jet : CurvatureJet) (direction first second contracted row column : Fin 4) : Real :=
  bracketDerivative direction first second contracted * jet.1 row column +
    bracket first second contracted * jet.2.2.1 direction row column

def jetKoszulDerivative (bracket : MetricFirstJet) (bracketDerivative : MetricSecondJet)
    (jet : CurvatureJet) (direction first second lower : Fin 4) : Real :=
  (1 / 2 : Real) * (jet.2.2.2 direction first second lower + jet.2.2.2 direction second lower first -
    jet.2.2.2 direction lower first second -
    ∑ k, jetStructureDerivative bracket bracketDerivative jet direction second lower k first k +
    ∑ k, jetStructureDerivative bracket bracketDerivative jet direction lower first k second k +
    ∑ k, jetStructureDerivative bracket bracketDerivative jet direction first second k lower k)

def jetChristoffel (bracket : MetricFirstJet) (jet : CurvatureJet) (upper first second : Fin 4) : Real :=
  ∑ lower, jet.2.1 upper lower * jetKoszul bracket jet first second lower

def jetChristoffelDerivative (bracket : MetricFirstJet) (bracketDerivative : MetricSecondJet)
    (jet : CurvatureJet) (direction upper first second : Fin 4) : Real :=
  ∑ lower, (jetInverseDerivative jet direction upper lower * jetKoszul bracket jet first second lower +
    jet.2.1 upper lower * jetKoszulDerivative bracket bracketDerivative jet direction first second lower)

def jetRiemann (bracket : MetricFirstJet) (bracketDerivative : MetricSecondJet)
    (jet : CurvatureJet) (upper lower first second : Fin 4) : Real :=
  jetChristoffelDerivative bracket bracketDerivative jet first upper second lower -
  jetChristoffelDerivative bracket bracketDerivative jet second upper first lower +
  ∑ k, jetChristoffel bracket jet k second lower * jetChristoffel bracket jet upper first k -
  ∑ k, jetChristoffel bracket jet k first lower * jetChristoffel bracket jet upper second k -
  ∑ k, bracket first second k * jetChristoffel bracket jet upper k lower

def jetRicci (bracket : MetricFirstJet) (bracketDerivative : MetricSecondJet)
    (jet : CurvatureJet) (first second : Fin 4) : Real :=
  ∑ k, jetRiemann bracket bracketDerivative jet k first k second

def jetScalarCurvature (bracket : MetricFirstJet) (bracketDerivative : MetricSecondJet)
    (jet : CurvatureJet) : Real :=
  ∑ first, ∑ second, jet.2.1 first second * jetRicci bracket bracketDerivative jet first second

@[fun_prop] theorem jetKoszul_contDiff (bracket : MetricFirstJet) (first second lower : Fin 4) :
    ContDiff Real ∞ (fun jet => jetKoszul bracket jet first second lower) := by
  unfold jetKoszul
  fun_prop

@[fun_prop] theorem jetInverseDerivative_contDiff (direction upper lower : Fin 4) :
    ContDiff Real ∞ (fun jet => jetInverseDerivative jet direction upper lower) := by
  unfold jetInverseDerivative
  fun_prop

@[fun_prop] theorem jetStructureDerivative_contDiff
    (bracket : MetricFirstJet) (bracketDerivative : MetricSecondJet)
    (direction first second contracted row column : Fin 4) :
    ContDiff Real ∞ (fun jet => jetStructureDerivative bracket bracketDerivative jet
      direction first second contracted row column) := by
  unfold jetStructureDerivative
  fun_prop

@[fun_prop] theorem jetKoszulDerivative_contDiff
    (bracket : MetricFirstJet) (bracketDerivative : MetricSecondJet) (direction first second lower : Fin 4) :
    ContDiff Real ∞ (fun jet => jetKoszulDerivative bracket bracketDerivative jet direction first second lower) := by
  unfold jetKoszulDerivative
  fun_prop

@[fun_prop] theorem jetChristoffel_contDiff (bracket : MetricFirstJet) (upper first second : Fin 4) :
    ContDiff Real ∞ (fun jet => jetChristoffel bracket jet upper first second) := by
  unfold jetChristoffel
  fun_prop

@[fun_prop] theorem jetChristoffelDerivative_contDiff
    (bracket : MetricFirstJet) (bracketDerivative : MetricSecondJet) (direction upper first second : Fin 4) :
    ContDiff Real ∞ (fun jet => jetChristoffelDerivative bracket bracketDerivative jet direction upper first second) := by
  unfold jetChristoffelDerivative
  fun_prop

@[fun_prop] theorem jetRiemann_contDiff
    (bracket : MetricFirstJet) (bracketDerivative : MetricSecondJet) (upper lower first second : Fin 4) :
    ContDiff Real ∞ (fun jet => jetRiemann bracket bracketDerivative jet upper lower first second) := by
  unfold jetRiemann
  fun_prop

@[fun_prop] theorem jetRicci_contDiff
    (bracket : MetricFirstJet) (bracketDerivative : MetricSecondJet) (first second : Fin 4) :
    ContDiff Real ∞ (fun jet => jetRicci bracket bracketDerivative jet first second) := by
  unfold jetRicci
  fun_prop

theorem jetScalarCurvature_contDiff (bracket : MetricFirstJet) (bracketDerivative : MetricSecondJet) :
    ContDiff Real ∞ (jetScalarCurvature bracket bracketDerivative) := by
  unfold jetScalarCurvature
  fun_prop

end
end JanusFormal.P0EFTJanusProgramPT12CurvatureJetSymbol4D
