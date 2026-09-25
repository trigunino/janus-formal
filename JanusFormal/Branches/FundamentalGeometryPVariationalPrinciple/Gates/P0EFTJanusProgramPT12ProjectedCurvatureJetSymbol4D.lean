import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! Finite polynomial for projected curvature on a redundant generating frame.
The inverse metric and its ordered first derivatives are independent feature slots. -/
namespace JanusFormal.P0EFTJanusProgramPT12ProjectedCurvatureJetSymbol4D
set_option autoImplicit false
noncomputable section
open scoped BigOperators ContDiff

abbrev MetricMatrix (n : Nat) := Fin n → Fin n → Real
abbrev MetricFirstJet (n : Nat) := Fin n → MetricMatrix n
abbrev MetricSecondJet (n : Nat) := Fin n → MetricFirstJet n
abbrev CurvatureJet (n : Nat) :=
  MetricMatrix n × MetricMatrix n × MetricFirstJet n × MetricSecondJet n × MetricFirstJet n
variable {n : Nat}

def projectedJetKoszul (bracket : MetricFirstJet n) (jet : CurvatureJet n) (first second lower : Fin n) : Real :=
  (1 / 2 : Real) * (jet.2.2.1 first second lower + jet.2.2.1 second first lower -
    jet.2.2.1 lower first second - ∑ k, bracket second lower k * jet.1 first k +
    ∑ k, bracket lower first k * jet.1 second k + ∑ k, bracket first second k * jet.1 lower k)

def projectedJetInverseDerivative (jet : CurvatureJet n) (direction upper lower : Fin n) : Real :=
  jet.2.2.2.2 direction upper lower

def projectedJetStructureDerivative (bracket : MetricFirstJet n) (bracketDerivative : MetricSecondJet n)
    (jet : CurvatureJet n) (direction first second contracted row column : Fin n) : Real :=
  bracketDerivative direction first second contracted * jet.1 row column +
    bracket first second contracted * jet.2.2.1 direction row column

def projectedJetKoszulDerivative (bracket : MetricFirstJet n) (bracketDerivative : MetricSecondJet n)
    (jet : CurvatureJet n) (direction first second lower : Fin n) : Real :=
  (1 / 2 : Real) * (jet.2.2.2.1 direction first second lower + jet.2.2.2.1 direction second first lower -
    jet.2.2.2.1 direction lower first second -
    ∑ k, projectedJetStructureDerivative bracket bracketDerivative jet direction second lower k first k +
    ∑ k, projectedJetStructureDerivative bracket bracketDerivative jet direction lower first k second k +
    ∑ k, projectedJetStructureDerivative bracket bracketDerivative jet direction first second k lower k)

def projectedJetChristoffel (bracket : MetricFirstJet n) (jet : CurvatureJet n) (upper first second : Fin n) : Real :=
  ∑ lower, jet.2.1 upper lower * projectedJetKoszul bracket jet first second lower

def projectedJetChristoffelDerivative (bracket : MetricFirstJet n) (bracketDerivative : MetricSecondJet n)
    (jet : CurvatureJet n) (direction upper first second : Fin n) : Real :=
  ∑ lower, (projectedJetInverseDerivative jet direction upper lower * projectedJetKoszul bracket jet first second lower +
    jet.2.1 upper lower * projectedJetKoszulDerivative bracket bracketDerivative jet direction first second lower)

def projectedJetRiemann (bracket : MetricFirstJet n) (bracketDerivative : MetricSecondJet n)
    (jet : CurvatureJet n) (upper lower first second : Fin n) : Real :=
  projectedJetChristoffelDerivative bracket bracketDerivative jet first upper second lower -
  projectedJetChristoffelDerivative bracket bracketDerivative jet second upper first lower +
  ∑ k, projectedJetChristoffel bracket jet k second lower * projectedJetChristoffel bracket jet upper first k -
  ∑ k, projectedJetChristoffel bracket jet k first lower * projectedJetChristoffel bracket jet upper second k -
  ∑ k, bracket first second k * projectedJetChristoffel bracket jet upper k lower

def projectedJetRicci (bracket : MetricFirstJet n) (bracketDerivative : MetricSecondJet n)
    (projection : MetricMatrix n)
    (jet : CurvatureJet n) (first second : Fin n) : Real :=
  ∑ traced, ∑ upper, projection upper traced * projectedJetRiemann bracket bracketDerivative jet upper first traced second

def projectedJetScalarCurvature (bracket : MetricFirstJet n) (bracketDerivative : MetricSecondJet n)
    (projection : MetricMatrix n)
    (jet : CurvatureJet n) : Real :=
  ∑ first, ∑ second, jet.2.1 first second * projectedJetRicci bracket bracketDerivative projection jet first second

@[fun_prop] theorem projectedJetKoszul_contDiff (bracket : MetricFirstJet n) (first second lower : Fin n) :
    ContDiff Real ∞ (fun jet => projectedJetKoszul bracket jet first second lower) := by
  unfold projectedJetKoszul
  fun_prop

@[fun_prop] theorem projectedJetInverseDerivative_contDiff (direction upper lower : Fin n) :
    ContDiff Real ∞ (fun jet => projectedJetInverseDerivative jet direction upper lower) := by
  unfold projectedJetInverseDerivative
  fun_prop

@[fun_prop] theorem projectedJetStructureDerivative_contDiff
    (bracket : MetricFirstJet n) (bracketDerivative : MetricSecondJet n)
    (direction first second contracted row column : Fin n) :
    ContDiff Real ∞ (fun jet => projectedJetStructureDerivative bracket bracketDerivative jet
      direction first second contracted row column) := by
  unfold projectedJetStructureDerivative
  fun_prop

@[fun_prop] theorem projectedJetKoszulDerivative_contDiff
    (bracket : MetricFirstJet n) (bracketDerivative : MetricSecondJet n) (direction first second lower : Fin n) :
    ContDiff Real ∞ (fun jet => projectedJetKoszulDerivative bracket bracketDerivative jet direction first second lower) := by
  unfold projectedJetKoszulDerivative
  fun_prop

@[fun_prop] theorem projectedJetChristoffel_contDiff (bracket : MetricFirstJet n) (upper first second : Fin n) :
    ContDiff Real ∞ (fun jet => projectedJetChristoffel bracket jet upper first second) := by
  unfold projectedJetChristoffel
  fun_prop

@[fun_prop] theorem projectedJetChristoffelDerivative_contDiff
    (bracket : MetricFirstJet n) (bracketDerivative : MetricSecondJet n) (direction upper first second : Fin n) :
    ContDiff Real ∞ (fun jet => projectedJetChristoffelDerivative bracket bracketDerivative jet direction upper first second) := by
  unfold projectedJetChristoffelDerivative
  fun_prop

@[fun_prop] theorem projectedJetRiemann_contDiff
    (bracket : MetricFirstJet n) (bracketDerivative : MetricSecondJet n) (upper lower first second : Fin n) :
    ContDiff Real ∞ (fun jet => projectedJetRiemann bracket bracketDerivative jet upper lower first second) := by
  unfold projectedJetRiemann
  fun_prop

@[fun_prop] theorem projectedJetRicci_contDiff
    (bracket : MetricFirstJet n) (bracketDerivative : MetricSecondJet n)
    (projection : MetricMatrix n) (first second : Fin n) :
    ContDiff Real ∞ (fun jet => projectedJetRicci bracket bracketDerivative projection jet first second) := by
  unfold projectedJetRicci
  fun_prop

@[fun_prop] theorem projectedJetScalarCurvature_contDiff (bracket : MetricFirstJet n) (bracketDerivative : MetricSecondJet n)
    (projection : MetricMatrix n) :
    ContDiff Real ∞ (projectedJetScalarCurvature bracket bracketDerivative projection) := by
  unfold projectedJetScalarCurvature
  fun_prop

/-- Polynomial in the genuine volume/curvature features, with fixed physical couplings. -/
def projectedJetEinsteinDensity (bracket : MetricFirstJet n) (bracketDerivative : MetricSecondJet n)
    (projection : MetricMatrix n) (gravitationalCoupling cosmologicalConstant : Real)
    (features : Real × CurvatureJet n) : Real :=
  features.1 * ((1 / (2 * gravitationalCoupling)) *
    (projectedJetScalarCurvature bracket bracketDerivative projection features.2 - 2 * cosmologicalConstant))

@[fun_prop] theorem projectedJetEinsteinDensity_contDiff
    (bracket : MetricFirstJet n) (bracketDerivative : MetricSecondJet n)
    (projection : MetricMatrix n) (gravitationalCoupling cosmologicalConstant : Real) :
    ContDiff Real ∞ (projectedJetEinsteinDensity bracket bracketDerivative projection
      gravitationalCoupling cosmologicalConstant) := by
  unfold projectedJetEinsteinDensity
  fun_prop

end
end JanusFormal.P0EFTJanusProgramPT12ProjectedCurvatureJetSymbol4D
