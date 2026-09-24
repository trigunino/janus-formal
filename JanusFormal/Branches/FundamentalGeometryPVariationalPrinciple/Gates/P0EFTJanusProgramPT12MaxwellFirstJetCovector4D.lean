import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12MatrixFirstJetProduct4D

/-! The Maxwell Hessian as a covector on the relative matrix first jet. -/
namespace JanusFormal.P0EFTJanusProgramPT12MaxwellFirstJetCovector4D
set_option autoImplicit false
noncomputable section
open P0EFTJanusProgramPT12CurvatureJetSymbol4D
open P0EFTJanusProgramPT12MaxwellJetSymbol4D
open P0EFTJanusProgramPT12MaxwellTransportFirstJetSymbol4D
open P0EFTJanusProgramPT12MatrixFirstJetProduct4D
open scoped ContDiff BigOperators
private abbrev Matrix4 := Matrix (Fin 4) (Fin 4) Real

private def rightMultiply (inverse : Matrix4) : Matrix4 →ₗ[Real] Matrix4 where
  toFun matrix := matrix * inverse
  map_add' first second := Matrix.add_mul first second inverse
  map_smul' scalar matrix := Matrix.smul_mul scalar matrix inverse

def relativeInverseReadout (inverse : Matrix4) : MatrixFirstJet →L[Real] MetricMatrix :=
  LinearMap.toContinuousLinearMap {
    toFun := fun jet => rightMultiply inverse jet.1
    map_add' := by intros; exact map_add _ _ _
    map_smul' := by intros; exact map_smul _ _ _ }

def maxwellFirstJetVelocity (inverse : Matrix4) (parameters : TransportSymbolParameters) :
    MatrixFirstJet →L[Real] MaxwellJet :=
  (-relativeInverseReadout inverse).prod ((1 / 2 : Real) • transportCurvatureLinear parameters)

def maxwellFirstJetAcceleration (inverse : Matrix4) (parameters : TransportSymbolParameters)
    (first : MatrixFirstJet) : MatrixFirstJet →L[Real] MaxwellJet :=
  ((relativeInverseReadout inverse).comp (matrixFirstJetRight first + matrixFirstJetLeft first)).prod
    ((-(1 / 8 : Real)) • (transportCurvatureLinear parameters).comp
      (matrixFirstJetLeft first + matrixFirstJetRight first))

def maxwellFirstJetCovector (input : MaxwellSymbolInput) (parameters : TransportSymbolParameters)
    (first : MatrixFirstJet) : MatrixFirstJet →L[Real] Real :=
  (maxwellSymbolHessian input (maxwellFirstJetVelocity input.2.1 parameters first)).comp
      (maxwellFirstJetVelocity input.2.1 parameters) +
    (maxwellSymbolGradient input).comp (maxwellFirstJetAcceleration input.2.1 parameters first)

theorem relativeInverseReadout_contDiff :
    ContDiff Real ∞ (fun input : MetricMatrix × MatrixFirstJet => relativeInverseReadout input.1 input.2) := by
  change ContDiff Real ∞ (fun input : MetricMatrix × MatrixFirstJet =>
    fun row column => ∑ middle, input.2.1 row middle * input.1 middle column)
  fun_prop

theorem maxwellFirstJetVelocity_contDiff :
    ContDiff Real ∞ (fun input : MetricMatrix × TransportSymbolParameters × MatrixFirstJet =>
      maxwellFirstJetVelocity input.1 input.2.1 input.2.2) := by
  change ContDiff Real ∞ (fun input : MetricMatrix × TransportSymbolParameters × MatrixFirstJet =>
    (-relativeInverseReadout input.1 input.2.2,
      (1 / 2 : Real) • transportCurvatureSymbol input.2.1 input.2.2))
  exact (relativeInverseReadout_contDiff.comp (contDiff_fst.prodMk contDiff_snd.snd)).neg.prodMk
    ((transportCurvatureSymbol_contDiff.comp contDiff_snd).const_smul _)

theorem maxwellFirstJetAcceleration_apply (inverse : MetricMatrix) (parameters : TransportSymbolParameters)
    (first second : MatrixFirstJet) :
    maxwellFirstJetAcceleration inverse parameters first second =
      (relativeInverseReadout inverse (matrixFirstJetLeft second first + matrixFirstJetLeft first second),
       (-(1 / 8 : Real)) • transportCurvatureSymbol parameters
         (matrixFirstJetLeft first second + matrixFirstJetLeft second first)) := rfl

attribute [local irreducible] relativeInverseReadout matrixFirstJetLeft matrixFirstJetRight
  maxwellFirstJetAcceleration

theorem maxwellFirstJetAcceleration_contDiff :
    ContDiff Real ∞ (fun input : MetricMatrix × TransportSymbolParameters × MatrixFirstJet × MatrixFirstJet =>
      maxwellFirstJetAcceleration input.1 input.2.1 input.2.2.1 input.2.2.2) := by
  have hForward : ContDiff Real ∞
      (fun input : MetricMatrix × TransportSymbolParameters × MatrixFirstJet × MatrixFirstJet =>
        matrixFirstJetLeft input.2.2.1 input.2.2.2) :=
    matrixFirstJetLeft_contDiff.comp contDiff_snd.snd
  have hReverse : ContDiff Real ∞
      (fun input : MetricMatrix × TransportSymbolParameters × MatrixFirstJet × MatrixFirstJet =>
        matrixFirstJetLeft input.2.2.2 input.2.2.1) :=
    matrixFirstJetLeft_contDiff.comp (contDiff_snd.snd.snd.prodMk contDiff_snd.snd.fst)
  simp only [maxwellFirstJetAcceleration_apply]
  exact (relativeInverseReadout_contDiff.comp (contDiff_fst.prodMk (hReverse.add hForward))).prodMk
    ((transportCurvatureSymbol_contDiff.comp (contDiff_snd.fst.prodMk (hForward.add hReverse))).const_smul _)

attribute [local irreducible] maxwellFirstJetVelocity
  maxwellSymbolHessian maxwellSymbolGradient

theorem maxwellFirstJetCovector_contDiff (test : MatrixFirstJet) :
    ContDiff Real ∞ (fun input : MaxwellSymbolInput × TransportSymbolParameters × MatrixFirstJet =>
      maxwellFirstJetCovector input.1 input.2.1 input.2.2 test) := by
  have hFirst : ContDiff Real ∞ (fun input : MaxwellSymbolInput × TransportSymbolParameters × MatrixFirstJet =>
      maxwellFirstJetVelocity input.1.2.1 input.2.1 input.2.2) := maxwellFirstJetVelocity_contDiff.comp
    (contDiff_fst.snd.fst.prodMk contDiff_snd)
  have hTest : ContDiff Real ∞ (fun input : MaxwellSymbolInput × TransportSymbolParameters × MatrixFirstJet =>
      maxwellFirstJetVelocity input.1.2.1 input.2.1 test) := maxwellFirstJetVelocity_contDiff.comp
    (contDiff_fst.snd.fst.prodMk (contDiff_snd.fst.prodMk (contDiff_const (c := test))))
  have hAcceleration : ContDiff Real ∞ (fun input : MaxwellSymbolInput × TransportSymbolParameters × MatrixFirstJet =>
      maxwellFirstJetAcceleration input.1.2.1 input.2.1 input.2.2 test) := maxwellFirstJetAcceleration_contDiff.comp
    (contDiff_fst.snd.fst.prodMk
      (contDiff_snd.fst.prodMk (contDiff_snd.snd.prodMk (contDiff_const (c := test)))))
  exact (((maxwellSymbolHessian_contDiff.comp contDiff_fst).clm_apply hFirst).clm_apply hTest).add
    ((maxwellSymbolGradient_contDiff.comp contDiff_fst).clm_apply hAcceleration)

def matrixValueBasis (row column : Fin 4) : MatrixFirstJet :=
  (Pi.single row (Pi.single column 1), 0)

def matrixFirstBasis (direction row column : Fin 4) : MatrixFirstJet :=
  (0, Pi.single direction (Pi.single row (Pi.single column 1)))

theorem matrixFirstJet_decomposition (jet : MatrixFirstJet) :
    jet = (∑ row, ∑ column, jet.1 row column • matrixValueBasis row column) +
      (∑ direction, ∑ row, ∑ column, jet.2 direction row column • matrixFirstBasis direction row column) := by
  rcases jet with ⟨value, first⟩
  ext <;> simp [matrixValueBasis, matrixFirstBasis, Pi.single_apply, Prod.fst_sum, Prod.snd_sum, Finset.sum_apply]

theorem matrixFirstJetCovector_apply (linear : MatrixFirstJet →L[Real] Real) (jet : MatrixFirstJet) :
    linear jet = (∑ row, ∑ column, linear (matrixValueBasis row column) * jet.1 row column) +
      (∑ direction, ∑ row, ∑ column, linear (matrixFirstBasis direction row column) * jet.2 direction row column) := by
  calc
    linear jet = linear ((∑ row, ∑ column, jet.1 row column • matrixValueBasis row column) +
      (∑ direction, ∑ row, ∑ column, jet.2 direction row column • matrixFirstBasis direction row column)) :=
        congrArg linear (matrixFirstJet_decomposition jet)
    _ = _ := by simp only [map_add, map_sum, map_smul, smul_eq_mul, mul_comm]

end
end JanusFormal.P0EFTJanusProgramPT12MaxwellFirstJetCovector4D
