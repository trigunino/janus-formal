import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointFredholmFullDeterminantTopologicalBundle4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointFredholmZetaFullTensor4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeZetaDeterminantConnection4D

/-!
# Continuous zeta section of the full determinant bundle

In the canonical full determinant coordinate the Fredholm--zeta section has
coordinate exactly `D_zeta(a)`.  The latter is differentiable by the existing
Mellin/zeta family theorem.  Hence the dependent full determinant section is a
continuous section of the registered complex vector bundle.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPSelfAdjointFredholmZetaTopologicalSection4D

set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option synthInstance.maxHeartbeats 5000000
noncomputable section

open Bundle Topology
open P0EFTJanusProgramPSelfAdjointFredholmDeterminantLineFamily4D
open P0EFTJanusProgramPSelfAdjointFredholmFullTensorDeterminantFiber4D
open P0EFTJanusProgramPSelfAdjointFredholmFullComplexCoordinate4D
open P0EFTJanusProgramPSelfAdjointFredholmFullDeterminantTopologicalBundle4D
open P0EFTJanusProgramPSelfAdjointFredholmZetaFullTensor4D
open P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D
open P0EFTJanusProgramPRelativeZetaDeterminantConnection4D

variable {E ZeroMode : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [CompleteSpace E]
  [Fintype ZeroMode] [DecidableEq ZeroMode] [LinearOrder ZeroMode]

/-- The intrinsic zeta determinant coordinate is continuous in the family
parameter. -/
theorem relativeHeatMellinZetaFamilyDeterminant_continuous
    (zetaFamily : RelativeHeatMellinZetaFamilyData) :
    Continuous (relativeHeatMellinZetaFamilyDeterminant zetaFamily) := by
  rw [continuous_iff_continuousAt]
  intro parameter
  exact (relativeZetaDeterminantCoordinate_hasDerivAt
    zetaFamily.toZetaFamily parameter).continuousAt

/-- Full dependent Fredholm--zeta section. -/
def fullDeterminantZetaSection
    {operator : Real → E →L[Real] E}
    (fredholm : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (zetaFamily : RelativeHeatMellinZetaFamilyData)
    (parameter : Real) :
    fredholm.FullDeterminantFiber parameter :=
  selfAdjointFredholmZetaFullTensorSection fredholm zetaFamily parameter

/-- The canonical fibre coordinate of the dependent zeta section is exactly
its intrinsic Mellin/zeta determinant. -/
@[simp]
theorem fullDeterminantZetaSection_coordinate
    {operator : Real → E →L[Real] E}
    (fredholm : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (zetaFamily : RelativeHeatMellinZetaFamilyData)
    (parameter : Real) :
    fredholm.fullTensorDeterminantCoordinateEquiv parameter
        (fullDeterminantZetaSection fredholm zetaFamily parameter) =
      relativeHeatMellinZetaFamilyDeterminant zetaFamily parameter := by
  simp [fullDeterminantZetaSection,
    selfAdjointFredholmZetaFullTensorSection]

/-- Zeta section as a map into the dependent total space. -/
def fullDeterminantZetaTotalSection
    {operator : Real → E →L[Real] E}
    (fredholm : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (zetaFamily : RelativeHeatMellinZetaFamilyData) :
    Real → TotalSpace Complex fredholm.FullDeterminantFiber :=
  fun parameter => ⟨parameter,
    fullDeterminantZetaSection fredholm zetaFamily parameter⟩

/-- In the global determinant trivialization, the total zeta section is the
graph of the scalar zeta determinant. -/
theorem fullDeterminantTotalSpaceHomeomorph_zetaSection
    {operator : Real → E →L[Real] E}
    (fredholm : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (zetaFamily : RelativeHeatMellinZetaFamilyData)
    (parameter : Real) :
    fredholm.fullDeterminantTotalSpaceHomeomorph
        (fullDeterminantZetaTotalSection fredholm zetaFamily parameter) =
      (parameter, relativeHeatMellinZetaFamilyDeterminant zetaFamily parameter) := by
  simp [fullDeterminantTotalSpaceHomeomorph,
    fullDeterminantGlobalTrivialization,
    fullDeterminantPretrivialization,
    fullDeterminantZetaTotalSection,
    fullDeterminantZetaSection,
    selfAdjointFredholmZetaFullTensorSection]

/-- The genuine dependent Fredholm--zeta section is continuous. -/
theorem fullDeterminantZetaTotalSection_continuous
    {operator : Real → E →L[Real] E}
    (fredholm : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (zetaFamily : RelativeHeatMellinZetaFamilyData) :
    Continuous (fullDeterminantZetaTotalSection fredholm zetaFamily) := by
  have hCoordinate : Continuous
      (fun parameter : Real =>
        (parameter,
          relativeHeatMellinZetaFamilyDeterminant zetaFamily parameter)) :=
    continuous_id.prod_mk
      (relativeHeatMellinZetaFamilyDeterminant_continuous zetaFamily)
  have hAfter : Continuous
      (fun parameter : Real =>
        fredholm.fullDeterminantTotalSpaceHomeomorph
          (fullDeterminantZetaTotalSection fredholm zetaFamily parameter)) := by
    simpa only [fullDeterminantTotalSpaceHomeomorph_zetaSection] using hCoordinate
  have hBack :=
    fredholm.fullDeterminantTotalSpaceHomeomorph.symm.continuous.comp hAfter
  simpa using hBack

/-- Public continuous full determinant-section checkpoint. -/
theorem self_adjoint_fredholm_zeta_topological_section_gate
    {operator : Real → E →L[Real] E}
    (fredholm : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (zetaFamily : RelativeHeatMellinZetaFamilyData) :
    Continuous (fullDeterminantZetaTotalSection fredholm zetaFamily) ∧
      (∀ parameter,
        fredholm.fullTensorDeterminantCoordinateEquiv parameter
            (fullDeterminantZetaSection fredholm zetaFamily parameter) =
          relativeHeatMellinZetaFamilyDeterminant zetaFamily parameter) :=
  ⟨fullDeterminantZetaTotalSection_continuous fredholm zetaFamily,
    fullDeterminantZetaSection_coordinate fredholm zetaFamily⟩

end
end P0EFTJanusProgramPSelfAdjointFredholmZetaTopologicalSection4D
end JanusFormal
