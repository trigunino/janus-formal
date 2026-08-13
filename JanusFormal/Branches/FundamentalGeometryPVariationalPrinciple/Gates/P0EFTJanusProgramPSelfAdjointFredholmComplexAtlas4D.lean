import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointFredholmComplexCoordinateFamily4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeZetaDeterminantLineAtlas4D

/-!
# Zeta atlases on the actual complexified Fredholm line

A local zeta atlas already has scalar determinants `D_i` and transitions
`g_ij = D_j / D_i`.  Here every `D_i` multiplies the same canonical actual
Fredholm frame in

`Complex ⊗[Real] Hom(det coker H_a, det ker H_a)`.

Thus the scalar Cech cocycle becomes a genuine gluing law for sections of the
actual complexified Fredholm fibre, without introducing an auxiliary line.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPSelfAdjointFredholmComplexAtlas4D

set_option autoImplicit false
set_option maxHeartbeats 5200000
set_option synthInstance.maxHeartbeats 2600000

noncomputable section

open P0EFTJanusProgramPSelfAdjointFredholmDeterminantLineFamily4D
open P0EFTJanusProgramPSelfAdjointFredholmComplexification4D
open P0EFTJanusProgramPRelativeZetaDeterminantCocycle4D
open P0EFTJanusProgramPRelativeZetaDeterminantLineAtlas4D

variable {E ZeroMode Index : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [CompleteSpace E]
  [Fintype ZeroMode] [DecidableEq ZeroMode] [LinearOrder ZeroMode]

/-- One local zeta determinant, placed in the actual complexified Fredholm
fibre at the same parameter. -/
def localComplexFredholmSection
    {operator : Real → E →L[Real] E}
    (fredholm : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (atlas : RelativeZetaLocalFamilyAtlasData Index)
    (index : Index) (parameter : Real) :
    fredholm.complexifiedDeterminantLine parameter :=
  fredholm.complexifiedDeterminantSection parameter
    (relativeZetaLocalDeterminant atlas index parameter)

/-- The local sections glue by the exact zeta transition function. -/
theorem localComplexFredholmSection_transition
    {operator : Real → E →L[Real] E}
    (fredholm : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (atlas : RelativeZetaLocalFamilyAtlasData Index)
    (first second : Index) (parameter : Real) :
    relativeZetaTransition atlas first second parameter •
        localComplexFredholmSection fredholm atlas first parameter =
      localComplexFredholmSection fredholm atlas second parameter := by
  unfold localComplexFredholmSection
    SelfAdjointFredholmDeterminantFamilyData.complexifiedDeterminantSection
  rw [smul_smul]
  rw [relativeZetaLocalDeterminant_transition atlas first second parameter]

/-- The transition cocycle acts associatively on the actual Fredholm fibre. -/
theorem localComplexFredholmSection_transition_cocycle
    {operator : Real → E →L[Real] E}
    (fredholm : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (atlas : RelativeZetaLocalFamilyAtlasData Index)
    (first second third : Index) (parameter : Real) :
    relativeZetaTransition atlas second third parameter •
        (relativeZetaTransition atlas first second parameter •
          localComplexFredholmSection fredholm atlas first parameter) =
      relativeZetaTransition atlas first third parameter •
        localComplexFredholmSection fredholm atlas first parameter := by
  rw [smul_smul]
  rw [relativeZetaTransition_cocycle atlas first second third parameter]

/-- Local determinant coordinates remain nonzero in every chart. -/
theorem localComplexFredholmCoordinate_ne_zero
    (atlas : RelativeZetaLocalFamilyAtlasData Index)
    (index : Index) (parameter : Real) :
    relativeZetaLocalDeterminant atlas index parameter ≠ 0 :=
  relativeZetaLocalDeterminant_ne_zero atlas index parameter

/-- Transition functions acting on the actual Fredholm frame never vanish. -/
theorem localComplexFredholmTransition_ne_zero
    (atlas : RelativeZetaLocalFamilyAtlasData Index)
    (first second : Index) (parameter : Real) :
    relativeZetaTransition atlas first second parameter ≠ 0 :=
  relativeZetaTransition_ne_zero atlas first second parameter

/-- Gauge covariance is inherited unchanged because all local scalar
coordinates multiply the same actual Fredholm frame. -/
theorem localComplexFredholmConnection_gauge
    (atlas : RelativeZetaLocalFamilyAtlasData Index)
    (first second : Index) (parameter : Real)
    (value derivative : Complex) :
    relativeZetaLocalConnectionAt atlas second parameter
        (relativeZetaTransition atlas first second parameter * value)
        (relativeZetaTransitionDerivative atlas first second parameter * value +
          relativeZetaTransition atlas first second parameter * derivative) =
      relativeZetaTransition atlas first second parameter *
        relativeZetaLocalConnectionAt atlas first parameter value derivative :=
  relativeZetaLocalConnection_gauge_covariant atlas first second parameter
    value derivative

/-- Public checkpoint for a zeta atlas acting on one actual complexified
Fredholm determinant family. -/
theorem self_adjoint_fredholm_complex_atlas_gate
    {operator : Real → E →L[Real] E}
    (fredholm : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (atlas : RelativeZetaLocalFamilyAtlasData Index) :
    (∀ first second parameter,
      relativeZetaTransition atlas first second parameter •
          localComplexFredholmSection fredholm atlas first parameter =
        localComplexFredholmSection fredholm atlas second parameter) ∧
      (∀ first second third parameter,
        relativeZetaTransition atlas second third parameter *
            relativeZetaTransition atlas first second parameter =
          relativeZetaTransition atlas first third parameter) ∧
      (∀ index parameter,
        relativeZetaLocalDeterminant atlas index parameter ≠ 0) :=
  ⟨localComplexFredholmSection_transition fredholm atlas,
    relativeZetaTransition_cocycle atlas,
    localComplexFredholmCoordinate_ne_zero atlas⟩

end
end P0EFTJanusProgramPSelfAdjointFredholmComplexAtlas4D
end JanusFormal
