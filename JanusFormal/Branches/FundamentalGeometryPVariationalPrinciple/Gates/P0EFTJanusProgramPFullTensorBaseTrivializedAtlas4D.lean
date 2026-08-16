import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointFredholmFullTensorTransport4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFullTensorZetaAtlas4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFullTensorZetaGluing4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFullTensorAtlasConnection4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFullTensorGauge4D

/-!
# Basepoint trivialization of the full determinant atlas

The full Fredholm--zeta fibres now carry canonical parameter transport.  Pulling
all local spectral-cut sections back to the fibre at parameter zero gives a
single fixed complex line.  In that fixed fibre the local section is exactly
the same canonical Fredholm frame weighted by the local zeta coordinate.

This is the correct setting for differentiating local coordinates: no derivative
of a varying subtype or varying tensor fibre is required.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFullTensorBaseTrivializedAtlas4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPSelfAdjointFredholmDeterminantLineFamily4D
open P0EFTJanusProgramPSelfAdjointFredholmFullTensorDeterminantFiber4D
open P0EFTJanusProgramPSelfAdjointFredholmFullTensorTransport4D
open P0EFTJanusProgramPFullTensorZetaAtlas4D
open P0EFTJanusProgramPFullTensorZetaGluing4D
open P0EFTJanusProgramPFullTensorAtlasConnection4D
open P0EFTJanusProgramPFullTensorGauge4D
open P0EFTJanusProgramPRelativeZetaDeterminantCocycle4D
open P0EFTJanusProgramPRelativeZetaDeterminantLineAtlas4D

variable {E ZeroMode Index : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [CompleteSpace E]
  [Fintype ZeroMode] [DecidableEq ZeroMode] [LinearOrder ZeroMode]

/-- Local spectral-cut determinant section transported back to the fixed
basepoint full determinant fibre. -/
def baseTrivializedLocalFullTensorSection
    {operator : Real → E →L[Real] E}
    (fredholm : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (atlas : RelativeZetaLocalFamilyAtlasData Index)
    (index : Index) (parameter : Real) :
    fredholm.fullTensorDeterminantLine 0 :=
  (fredholm.fullTensorDeterminantBaseTrivialization parameter).symm
    (localFullTensorSection fredholm atlas index parameter)

/-- In the basepoint fibre, the local section is exactly the local zeta
coordinate in the fixed canonical Fredholm frame. -/
theorem baseTrivializedLocalFullTensorSection_formula
    {operator : Real → E →L[Real] E}
    (fredholm : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (atlas : RelativeZetaLocalFamilyAtlasData Index)
    (index : Index) (parameter : Real) :
    baseTrivializedLocalFullTensorSection fredholm atlas index parameter =
      fredholm.fullTensorDeterminantSection 0
        (relativeZetaLocalDeterminant atlas index parameter) := by
  apply (fredholm.fullTensorDeterminantBaseTrivialization parameter).injective
  simp [baseTrivializedLocalFullTensorSection,
    localFullTensorSection,
    fredholm.fullTensorDeterminantBaseTrivialization_section]

/-- Spectral-cut gluing remains exact after all fibres are pulled back to the
same basepoint line. -/
theorem baseTrivializedLocalFullTensorSection_transition
    {operator : Real → E →L[Real] E}
    (fredholm : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (atlas : RelativeZetaLocalFamilyAtlasData Index)
    (first second : Index) (parameter : Real) :
    relativeZetaTransition atlas first second parameter •
        baseTrivializedLocalFullTensorSection fredholm atlas first parameter =
      baseTrivializedLocalFullTensorSection fredholm atlas second parameter := by
  apply (fredholm.fullTensorDeterminantBaseTrivialization parameter).injective
  rw [map_smul]
  simp only [baseTrivializedLocalFullTensorSection,
    LinearEquiv.apply_symm_apply]
  exact localFullTensorSection_transition fredholm atlas first second parameter

/-- Local connection represented directly in the fixed basepoint determinant
line. -/
def baseTrivializedLocalFullTensorConnectionAt
    {operator : Real → E →L[Real] E}
    (fredholm : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (atlas : RelativeZetaLocalFamilyAtlasData Index)
    (index : Index) (parameter : Real)
    (value derivative : Complex) :
    fredholm.fullTensorDeterminantLine 0 :=
  fredholm.fullTensorDeterminantSection 0
    (relativeZetaLocalConnectionAt atlas index parameter value derivative)

/-- Gauge covariance in the single fixed determinant fibre. -/
theorem baseTrivializedLocalFullTensorConnection_gauge
    {operator : Real → E →L[Real] E}
    (fredholm : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (atlas : RelativeZetaLocalFamilyAtlasData Index)
    (first second : Index) (parameter : Real)
    (value derivative : Complex) :
    baseTrivializedLocalFullTensorConnectionAt fredholm atlas second parameter
        (relativeZetaTransition atlas first second parameter * value)
        (relativeZetaTransitionDerivative atlas first second parameter * value +
          relativeZetaTransition atlas first second parameter * derivative) =
      relativeZetaTransition atlas first second parameter •
        baseTrivializedLocalFullTensorConnectionAt fredholm atlas first parameter
          value derivative := by
  unfold baseTrivializedLocalFullTensorConnectionAt
  have h := relativeZetaLocalConnection_gauge_covariant
    atlas first second parameter value derivative
  rw [h]
  exact (fredholm.fullTensorDeterminantSection_smul 0
    (relativeZetaTransition atlas first second parameter)
    (relativeZetaLocalConnectionAt atlas first parameter value derivative)).symm

/-- Public fixed-fibre determinant-atlas checkpoint. -/
theorem full_tensor_base_trivialized_atlas_gate
    {operator : Real → E →L[Real] E}
    (fredholm : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (atlas : RelativeZetaLocalFamilyAtlasData Index) :
    (∀ index parameter,
      baseTrivializedLocalFullTensorSection fredholm atlas index parameter =
        fredholm.fullTensorDeterminantSection 0
          (relativeZetaLocalDeterminant atlas index parameter)) ∧
    (∀ first second parameter,
      relativeZetaTransition atlas first second parameter •
          baseTrivializedLocalFullTensorSection fredholm atlas first parameter =
        baseTrivializedLocalFullTensorSection fredholm atlas second parameter) :=
  ⟨baseTrivializedLocalFullTensorSection_formula fredholm atlas,
    baseTrivializedLocalFullTensorSection_transition fredholm atlas⟩

end
end P0EFTJanusProgramPFullTensorBaseTrivializedAtlas4D
end JanusFormal
