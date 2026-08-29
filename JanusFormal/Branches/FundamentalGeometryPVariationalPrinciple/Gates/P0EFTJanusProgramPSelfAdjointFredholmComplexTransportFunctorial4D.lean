import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointFredholmComplexTransport4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointFredholmDeterminantTransportFunctorial4D

/-!
# Functorial transport of the complexified Fredholm determinant line

Scalar extension along `Real -> Complex` preserves the exact identity and
composition laws of the actual Fredholm determinant transport.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPSelfAdjointFredholmComplexTransportFunctorial4D

set_option autoImplicit false
set_option maxHeartbeats 4200000
set_option synthInstance.maxHeartbeats 2100000

noncomputable section

open P0EFTJanusProgramPSelfAdjointFredholmDeterminantLineFamily4D
open P0EFTJanusProgramPSelfAdjointFredholmDeterminantTransportFunctorial4D
open P0EFTJanusProgramPSelfAdjointFredholmComplexification4D
open P0EFTJanusProgramPSelfAdjointFredholmComplexTransport4D

variable {E ZeroMode : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [CompleteSpace E]
  [Fintype ZeroMode] [DecidableEq ZeroMode] [LinearOrder ZeroMode]

namespace SelfAdjointFredholmDeterminantFamilyData

@[simp]
theorem complexifiedDeterminantTransport_self
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (parameter : Real) :
    data.complexifiedDeterminantTransport parameter parameter =
      LinearEquiv.refl Real _ := by
  unfold complexifiedDeterminantTransport
  rw [data.determinantTransport_self]
  exact LinearEquiv.lTensor_refl Complex _

/-- Exact composition law after complexification. -/
theorem complexifiedDeterminantTransport_trans
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (first second third : Real) :
    (data.complexifiedDeterminantTransport first second).trans
        (data.complexifiedDeterminantTransport second third) =
      data.complexifiedDeterminantTransport first third := by
  unfold complexifiedDeterminantTransport
  rw [← LinearEquiv.lTensor_trans]
  rw [data.determinantTransport_trans first second third]

/-- Basepoint trivializations recover direct transport by composition. -/
theorem complexifiedDeterminantBaseTrivialization_trans
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (first second : Real) :
    (data.complexifiedDeterminantBaseTrivialization first).symm.trans
        (data.complexifiedDeterminantBaseTrivialization second) =
      data.complexifiedDeterminantTransport first second := by
  unfold complexifiedDeterminantBaseTrivialization
  apply LinearEquiv.ext
  intro value
  have h := data.complexifiedDeterminantTransport_trans 0 first second
  have h0 :
      (data.complexifiedDeterminantTransport 0 first).symm.trans
          (data.complexifiedDeterminantTransport 0 first) =
        LinearEquiv.refl Real _ :=
    LinearEquiv.symm_trans_self _
  calc
    ((data.complexifiedDeterminantTransport 0 first).symm.trans
        (data.complexifiedDeterminantTransport 0 second)) value =
      ((data.complexifiedDeterminantTransport 0 first).symm.trans
        ((data.complexifiedDeterminantTransport 0 first).trans
          (data.complexifiedDeterminantTransport first second))) value := by
            rw [h]
    _ = data.complexifiedDeterminantTransport first second value := by
      simp

/-- Public functorial complex Fredholm transport checkpoint. -/
theorem self_adjoint_fredholm_complex_transport_functorial_gate
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode) :
    (∀ parameter,
      data.complexifiedDeterminantTransport parameter parameter =
        LinearEquiv.refl Real _) ∧
      (∀ first second third,
        (data.complexifiedDeterminantTransport first second).trans
            (data.complexifiedDeterminantTransport second third) =
          data.complexifiedDeterminantTransport first third) :=
  ⟨data.complexifiedDeterminantTransport_self,
    data.complexifiedDeterminantTransport_trans⟩

end SelfAdjointFredholmDeterminantFamilyData

end
end P0EFTJanusProgramPSelfAdjointFredholmComplexTransportFunctorial4D
end JanusFormal
