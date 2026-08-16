import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointFredholmComplexCoordinateFamily4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D

/-!
# Zeta coordinates as sections of the actual complexified Fredholm line

This file turns an honest Mellin/zeta determinant family into a section of the
actual scalar-extended Fredholm line

`Complex ⊗[Real] Hom(det coker H_a, det ker H_a)`.

The finite Fredholm frame is therefore no longer merely stored next to the
reduced zeta coordinate: the latter acts on the former.  The scalar derivative
and parallelism statements are inherited from the intrinsic zeta family.  A
later family-trivialization theorem may lift those scalar first-jet statements
to a covariant derivative of the varying Fredholm fibres themselves.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPSelfAdjointFredholmZetaDeterminantSection4D

set_option autoImplicit false
set_option maxHeartbeats 5200000
set_option synthInstance.maxHeartbeats 2600000

noncomputable section

open P0EFTJanusProgramPSelfAdjointFredholmDeterminantLineFamily4D
open P0EFTJanusProgramPSelfAdjointFredholmComplexification4D
open P0EFTJanusProgramPSelfAdjointFredholmComplexCoordinateFamily4D
open P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D
open P0EFTJanusProgramPRelativeZetaDeterminantConnection4D

variable {E ZeroMode : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [CompleteSpace E]
  [Fintype ZeroMode] [DecidableEq ZeroMode] [LinearOrder ZeroMode]

/-- Attach one intrinsic Mellin/zeta coordinate family to the actual Fredholm
line. -/
def selfAdjointFredholmZetaCoordinateFamily
    {operator : Real → E →L[Real] E}
    (fredholm : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (zetaFamily : RelativeHeatMellinZetaFamilyData) :
    SelfAdjointFredholmComplexCoordinateFamilyData fredholm where
  coordinate := relativeHeatMellinZetaFamilyDeterminant zetaFamily
  coordinate_ne_zero := by
    intro parameter
    exact relativeZetaDeterminantCoordinate_ne_zero
      zetaFamily.toZetaFamily parameter

/-- The genuine zeta-weighted section of the complexified Fredholm line. -/
def selfAdjointFredholmZetaDeterminantSection
    {operator : Real → E →L[Real] E}
    (fredholm : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (zetaFamily : RelativeHeatMellinZetaFamilyData)
    (parameter : Real) : fredholm.complexifiedDeterminantLine parameter :=
  (selfAdjointFredholmZetaCoordinateFamily fredholm zetaFamily).
    determinantSection parameter

/-- The determinant section is exactly the intrinsic reduced zeta coordinate
multiplying the canonical complexified finite Fredholm frame. -/
theorem selfAdjointFredholmZetaDeterminantSection_eq
    {operator : Real → E →L[Real] E}
    (fredholm : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (zetaFamily : RelativeHeatMellinZetaFamilyData)
    (parameter : Real) :
    selfAdjointFredholmZetaDeterminantSection fredholm zetaFamily parameter =
      relativeHeatMellinZetaFamilyDeterminant zetaFamily parameter •
        fredholm.complexifiedDeterminantFrame parameter :=
  rfl

/-- The scalar coordinate of the genuine Fredholm section has the exact zeta
first derivative already produced by the Mellin family. -/
theorem selfAdjointFredholmZetaCoordinate_hasDerivAt
    {operator : Real → E →L[Real] E}
    (fredholm : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (zetaFamily : RelativeHeatMellinZetaFamilyData)
    (parameter : Real) :
    HasDerivAt
      (selfAdjointFredholmZetaCoordinateFamily fredholm zetaFamily).coordinate
      (relativeZetaDeterminantCoordinateDerivative
        zetaFamily.toZetaFamily parameter) parameter := by
  simpa [selfAdjointFredholmZetaCoordinateFamily,
    relativeHeatMellinZetaFamilyDeterminant] using
    relativeZetaDeterminantCoordinate_hasDerivAt
      zetaFamily.toZetaFamily parameter

/-- In the canonical finite Fredholm frame the zeta-weighted section is
parallel for the intrinsic scalar Bismut--Freed connection. -/
theorem selfAdjointFredholmZetaCoordinate_parallel
    {operator : Real → E →L[Real] E}
    (fredholm : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (zetaFamily : RelativeHeatMellinZetaFamilyData)
    (parameter : Real) :
    relativeZetaConnectionAt zetaFamily.toZetaFamily parameter
        ((selfAdjointFredholmZetaCoordinateFamily fredholm zetaFamily).
          coordinate parameter)
        (relativeZetaDeterminantCoordinateDerivative
          zetaFamily.toZetaFamily parameter) = 0 := by
  simpa [selfAdjointFredholmZetaCoordinateFamily,
    relativeHeatMellinZetaFamilyDeterminant] using
    relativeZetaDeterminantCoordinate_parallel
      zetaFamily.toZetaFamily parameter

/-- A scalar reference change acts directly on the actual Fredholm section. -/
theorem selfAdjointFredholmZetaDeterminantSection_reference_change
    {operator : Real → E →L[Real] E}
    (fredholm : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (zetaFamily : RelativeHeatMellinZetaFamilyData)
    (parameter : Real) (transition : Complex) :
    transition •
        selfAdjointFredholmZetaDeterminantSection fredholm zetaFamily parameter =
      fredholm.complexifiedDeterminantSection parameter
        (transition * relativeHeatMellinZetaFamilyDeterminant
          zetaFamily parameter) := by
  exact
    (selfAdjointFredholmZetaCoordinateFamily fredholm zetaFamily).
      determinantSection_reference_change parameter transition

/-- Public checkpoint: the intrinsic Mellin determinant is now a genuine
coordinate on the actual complexified Fredholm line and remains parallel in
that canonical frame. -/
theorem self_adjoint_fredholm_zeta_determinant_section_gate
    {operator : Real → E →L[Real] E}
    (fredholm : SelfAdjointFredholmDeterminantFamilyData operator ZeroMode)
    (zetaFamily : RelativeHeatMellinZetaFamilyData) :
    (∀ parameter,
      selfAdjointFredholmZetaDeterminantSection fredholm zetaFamily parameter =
        relativeHeatMellinZetaFamilyDeterminant zetaFamily parameter •
          fredholm.complexifiedDeterminantFrame parameter) ∧
      (∀ parameter,
        (selfAdjointFredholmZetaCoordinateFamily fredholm zetaFamily).
          coordinate parameter ≠ 0) ∧
      (∀ parameter,
        relativeZetaConnectionAt zetaFamily.toZetaFamily parameter
            ((selfAdjointFredholmZetaCoordinateFamily fredholm zetaFamily).
              coordinate parameter)
            (relativeZetaDeterminantCoordinateDerivative
              zetaFamily.toZetaFamily parameter) = 0) :=
  ⟨selfAdjointFredholmZetaDeterminantSection_eq fredholm zetaFamily,
    (selfAdjointFredholmZetaCoordinateFamily fredholm zetaFamily).
      coordinate_ne_zero,
    selfAdjointFredholmZetaCoordinate_parallel fredholm zetaFamily⟩

end
end P0EFTJanusProgramPSelfAdjointFredholmZetaDeterminantSection4D
end JanusFormal
