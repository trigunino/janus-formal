import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointFredholmDeterminantTransportLaws4D

/-!
# Functorial transport on the actual Fredholm Hom-line

The source and target top-exterior transports already satisfy exact identity
and composition laws. Their `arrowCongr` transport therefore makes
`Hom(det coker H_a, det ker H_a)` itself a functorial family.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPSelfAdjointFredholmDeterminantTransportFunctorial4D

set_option autoImplicit false
set_option maxHeartbeats 4200000
set_option synthInstance.maxHeartbeats 2100000

noncomputable section

open P0EFTJanusProgramPSelfAdjointFredholmDeterminantLineFamily4D
open P0EFTJanusProgramPSelfAdjointFredholmDeterminantTransportLaws4D

variable {E ZeroMode : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [CompleteSpace E]
  [Fintype ZeroMode] [DecidableEq ZeroMode] [LinearOrder ZeroMode]

namespace SelfAdjointFredholmDeterminantFamilyData

@[simp]
theorem determinantTransport_self
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (parameter : Real) :
    data.determinantTransport parameter parameter = LinearEquiv.refl Real _ := by
  unfold determinantTransport
  rw [data.cokernelTopTransport_self, data.kernelTopTransport_self]
  exact LinearEquiv.arrowCongr_refl

/-- Exact composition law on the actual Fredholm determinant line. -/
theorem determinantTransport_trans
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (first second third : Real) :
    (data.determinantTransport first second).trans
        (data.determinantTransport second third) =
      data.determinantTransport first third := by
  unfold determinantTransport
  rw [LinearEquiv.arrowCongr_trans]
  rw [data.cokernelTopTransport_trans first second third,
    data.kernelTopTransport_trans first second third]

/-- Public functoriality checkpoint for the actual Fredholm Hom-line. -/
theorem self_adjoint_fredholm_determinant_transport_functorial_gate
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode) :
    (∀ parameter,
      data.determinantTransport parameter parameter = LinearEquiv.refl Real _) ∧
      (∀ first second third,
        (data.determinantTransport first second).trans
            (data.determinantTransport second third) =
          data.determinantTransport first third) :=
  ⟨data.determinantTransport_self, data.determinantTransport_trans⟩

end SelfAdjointFredholmDeterminantFamilyData

end
end P0EFTJanusProgramPSelfAdjointFredholmDeterminantTransportFunctorial4D
end JanusFormal
