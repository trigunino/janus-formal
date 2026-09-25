import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeEinsteinFiniteJetHessian4D

/-! The finite Einstein Hessian is an explicit continuous covector in its test jet. -/
namespace JanusFormal.P0EFTJanusProgramPT12FiniteEinsteinJetCovector4D
set_option autoImplicit false
noncomputable section
open scoped Matrix.Norms.Elementwise
open P0EFTJanusProgramPT12ProjectedCurvatureJetSymbol4D
open P0EFTJanusProgramPT12FiniteFrameMatrixFirstJet4D
open P0EFTJanusProgramPT12FrameFreeNativeVolumeJet4D
open P0EFTJanusProgramPT12FrameFreeNativeEinsteinFeatureVariation4D
open P0EFTJanusProgramPT12FrameFreeEinsteinFiniteJetHessian4D
variable {n : Nat}
private abbrev Mat := Matrix (Fin n) (Fin n) Real
private abbrev Raw := MetricMatrix n × MetricFirstJet n × MetricSecondJet n

private def valueLinear : FiniteMatrixFirstJet n →ₗ[Real] Mat (n := n) where
  toFun jet := jet.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def firstLinear (direction : Fin n) : FiniteMatrixFirstJet n →ₗ[Real] Mat (n := n) where
  toFun jet := jet.2 direction
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def leftProduct (left : Mat (n := n)) : Mat (n := n) →ₗ[Real] Mat (n := n) where
  toFun right := left * right
  map_add' := Matrix.mul_add left
  map_smul' scalar right := Matrix.mul_smul left scalar right

private def rightProduct (right : Mat (n := n)) : Mat (n := n) →ₗ[Real] Mat (n := n) where
  toFun left := left * right
  map_add' first second := Matrix.add_mul first second right
  map_smul' scalar left := Matrix.smul_mul scalar left right

def finiteMatrixFirstJetLeft (first : FiniteMatrixFirstJet n) : FiniteMatrixFirstJet n →L[Real] FiniteMatrixFirstJet n :=
  LinearMap.toContinuousLinearMap {
    toFun := fun second => ((leftProduct first.1).comp valueLinear second,
      fun direction => ((leftProduct (first.2 direction)).comp valueLinear +
        (leftProduct first.1).comp (firstLinear direction)) second)
    map_add' := by intros; ext <;> simp only [map_add] <;> rfl
    map_smul' := by intros; ext <;> simp only [map_smul] <;> rfl }

def finiteMatrixFirstJetRight (second : FiniteMatrixFirstJet n) : FiniteMatrixFirstJet n →L[Real] FiniteMatrixFirstJet n :=
  LinearMap.toContinuousLinearMap {
    toFun := fun first => ((rightProduct second.1).comp valueLinear first,
      fun direction => ((rightProduct second.1).comp (firstLinear direction) +
        (rightProduct (second.2 direction)).comp valueLinear) first)
    map_add' := by intros; ext <;> simp only [map_add] <;> rfl
    map_smul' := by intros; ext <;> simp only [map_smul] <;> rfl }

theorem finiteMatrixFirstJetLeft_apply (first second : FiniteMatrixFirstJet n) :
    finiteMatrixFirstJetLeft first second = finiteMatrixFirstJetProduct first second := rfl

theorem finiteMatrixFirstJetRight_apply (first second : FiniteMatrixFirstJet n) :
    finiteMatrixFirstJetRight second first = finiteMatrixFirstJetProduct first second := rfl

private def relativeJet : FiniteEinsteinVariation n →L[Real] FiniteMatrixFirstJet n :=
  ContinuousLinearMap.snd Real (Raw (n := n)) (FiniteMatrixFirstJet n)

private def relativeValue : FiniteEinsteinVariation n →L[Real] Mat (n := n) :=
  (ContinuousLinearMap.fst Real (Mat (n := n)) (MetricFirstJet n)).comp relativeJet

def finiteEinsteinVelocityCLM (baseVolume : Real) (baseInverse : FiniteMatrixFirstJet n) :
    FiniteEinsteinVariation n →L[Real] GroupedEinsteinJet n :=
  ((fderiv Real (finiteVolumeSymbol (dimension := n) baseVolume) 1).comp relativeValue).prod
    ((ContinuousLinearMap.fst Real (Raw (n := n)) (FiniteMatrixFirstJet n)).prod
      (-((finiteMatrixFirstJetRight baseInverse).comp relativeJet)))

theorem finiteEinsteinVelocityCLM_apply (baseVolume : Real) (baseInverse : FiniteMatrixFirstJet n)
    (variation : FiniteEinsteinVariation n) :
    finiteEinsteinVelocityCLM baseVolume baseInverse variation =
      finiteEinsteinFeatureVelocity baseVolume baseInverse variation := rfl

def finiteEinsteinAccelerationRight (baseVolume : Real) (baseInverse : FiniteMatrixFirstJet n)
    (first : FiniteEinsteinVariation n) : FiniteEinsteinVariation n →L[Real] GroupedEinsteinJet n :=
  ((fderiv Real (fderiv Real (finiteVolumeSymbol (dimension := n) baseVolume)) 1 first.2.1).comp relativeValue).prod
    ((0 : FiniteEinsteinVariation n →L[Real] Raw (n := n)).prod
      ((finiteMatrixFirstJetRight baseInverse).comp
        (((finiteMatrixFirstJetRight first.2) + (finiteMatrixFirstJetLeft first.2)).comp relativeJet)))

theorem finiteEinsteinAccelerationRight_apply (baseVolume : Real) (baseInverse : FiniteMatrixFirstJet n)
    (first second : FiniteEinsteinVariation n) :
    finiteEinsteinAccelerationRight baseVolume baseInverse first second =
      finiteEinsteinFeatureAcceleration baseVolume baseInverse first second := rfl

variable (bracket : MetricFirstJet n) (bracketDerivative : MetricSecondJet n)
  (projection : MetricMatrix n) (gravitationalCoupling cosmologicalConstant : Real)
  (base : GroupedEinsteinJet n) (baseVolume : Real) (baseInverse : FiniteMatrixFirstJet n)
local notation "symbol" => groupedEinsteinDensity bracket bracketDerivative projection gravitationalCoupling cosmologicalConstant
local notation "velocity" => finiteEinsteinVelocityCLM baseVolume baseInverse

def finiteEinsteinJetHessianRight (first : FiniteEinsteinVariation n) : FiniteEinsteinVariation n →L[Real] Real :=
  (fderiv Real (fderiv Real symbol) base (velocity first)).comp velocity +
    (fderiv Real symbol base).comp (finiteEinsteinAccelerationRight baseVolume baseInverse first)

theorem finiteEinsteinJetHessianRight_apply (first second : FiniteEinsteinVariation n) :
    finiteEinsteinJetHessianRight bracket bracketDerivative projection gravitationalCoupling cosmologicalConstant
        base baseVolume baseInverse first second =
      finiteEinsteinJetHessian bracket bracketDerivative projection gravitationalCoupling cosmologicalConstant
        base baseVolume baseInverse first second := rfl

theorem finiteEinsteinJetHessian_bound (first second : FiniteEinsteinVariation n) :
    ‖finiteEinsteinJetHessian bracket bracketDerivative projection gravitationalCoupling cosmologicalConstant
        base baseVolume baseInverse first second‖ ≤
      ‖finiteEinsteinJetHessianRight bracket bracketDerivative projection gravitationalCoupling cosmologicalConstant
        base baseVolume baseInverse first‖ * ‖second‖ :=
  (finiteEinsteinJetHessianRight bracket bracketDerivative projection gravitationalCoupling cosmologicalConstant
    base baseVolume baseInverse first).le_opNorm second

end
end JanusFormal.P0EFTJanusProgramPT12FiniteEinsteinJetCovector4D
