import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FiniteEinsteinJetCovector4D

/-! Explicit coefficient extraction for the finite Einstein test jets.
The tensor and relative slots remain distinct until the spatial reconstruction step. -/
namespace JanusFormal.P0EFTJanusProgramPT12FiniteEinsteinJetCoefficients4D
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open P0EFTJanusProgramPT12ProjectedCurvatureJetSymbol4D
open P0EFTJanusProgramPT12FiniteFrameMatrixFirstJet4D
open P0EFTJanusProgramPT12FrameFreeNativeEinsteinFeatureVariation4D
open P0EFTJanusProgramPT12FrameFreeEinsteinFiniteJetHessian4D
open P0EFTJanusProgramPT12FiniteEinsteinJetCovector4D
variable {n : Nat}

def tensorValueBasis (row column : Fin n) : FiniteEinsteinVariation n :=
  ((Pi.single row (Pi.single column 1), 0, 0), 0)

def tensorFirstBasis (direction row column : Fin n) : FiniteEinsteinVariation n :=
  ((0, Pi.single direction (Pi.single row (Pi.single column 1)), 0), 0)

def tensorSecondBasis (outer innerIndex row column : Fin n) : FiniteEinsteinVariation n :=
  ((0, 0, Pi.single outer (Pi.single innerIndex (Pi.single row (Pi.single column 1)))), 0)

def relativeValueBasis (row column : Fin n) : FiniteEinsteinVariation n :=
  (0, Pi.single row (Pi.single column 1), 0)

def relativeFirstBasis (direction row column : Fin n) : FiniteEinsteinVariation n :=
  (0, 0, Pi.single direction (Pi.single row (Pi.single column 1)))

theorem finiteEinsteinVariation_decomposition (jet : FiniteEinsteinVariation n) :
    jet =
      (∑ row, ∑ column, jet.1.1 row column • tensorValueBasis row column) +
      (∑ direction, ∑ row, ∑ column, jet.1.2.1 direction row column • tensorFirstBasis direction row column) +
      (∑ outer, ∑ innerIndex, ∑ row, ∑ column,
        jet.1.2.2 outer innerIndex row column • tensorSecondBasis outer innerIndex row column) +
      (∑ row, ∑ column, jet.2.1 row column • relativeValueBasis row column) +
      (∑ direction, ∑ row, ∑ column, jet.2.2 direction row column • relativeFirstBasis direction row column) := by
  rcases jet with ⟨⟨value, first, second⟩, ⟨relativeValue, relativeFirst⟩⟩
  ext <;> simp [tensorValueBasis, tensorFirstBasis, tensorSecondBasis, relativeValueBasis,
    relativeFirstBasis, Pi.single_apply, Prod.fst_sum, Prod.snd_sum, Finset.sum_apply]

def finiteEinsteinJetCoefficientDensity (linear : FiniteEinsteinVariation n →L[Real] Real)
    (jet : FiniteEinsteinVariation n) : Real :=
  (∑ row, ∑ column, linear (tensorValueBasis row column) * jet.1.1 row column) +
  (∑ direction, ∑ row, ∑ column, linear (tensorFirstBasis direction row column) * jet.1.2.1 direction row column) +
  (∑ outer, ∑ innerIndex, ∑ row, ∑ column,
    linear (tensorSecondBasis outer innerIndex row column) * jet.1.2.2 outer innerIndex row column) +
  (∑ row, ∑ column, linear (relativeValueBasis row column) * jet.2.1 row column) +
  (∑ direction, ∑ row, ∑ column, linear (relativeFirstBasis direction row column) * jet.2.2 direction row column)

theorem finiteEinsteinJetCovector_eq_coefficients (linear : FiniteEinsteinVariation n →L[Real] Real)
    (jet : FiniteEinsteinVariation n) :
    linear jet = finiteEinsteinJetCoefficientDensity linear jet := by
  refine (congrArg linear (finiteEinsteinVariation_decomposition jet)).trans ?_
  simp only [finiteEinsteinJetCoefficientDensity, map_add, map_sum, map_smul, smul_eq_mul, mul_comm]

theorem finiteEinsteinJetHessian_eq_coefficients
    (bracket : MetricFirstJet n) (bracketDerivative : MetricSecondJet n)
    (projection : MetricMatrix n) (gravitationalCoupling cosmologicalConstant : Real)
    (base : GroupedEinsteinJet n) (baseVolume : Real) (baseInverse : FiniteMatrixFirstJet n)
    (first second : FiniteEinsteinVariation n) :
    finiteEinsteinJetHessian bracket bracketDerivative projection gravitationalCoupling cosmologicalConstant
        base baseVolume baseInverse first second =
      finiteEinsteinJetCoefficientDensity
        (finiteEinsteinJetHessianRight bracket bracketDerivative projection gravitationalCoupling cosmologicalConstant
          base baseVolume baseInverse first) second :=
  (finiteEinsteinJetHessianRight_apply bracket bracketDerivative projection gravitationalCoupling cosmologicalConstant
    base baseVolume baseInverse first second).symm.trans
      (finiteEinsteinJetCovector_eq_coefficients _ second)

end
end JanusFormal.P0EFTJanusProgramPT12FiniteEinsteinJetCoefficients4D
