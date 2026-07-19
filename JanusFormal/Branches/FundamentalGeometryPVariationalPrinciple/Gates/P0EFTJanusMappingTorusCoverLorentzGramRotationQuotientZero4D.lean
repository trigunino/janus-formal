import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCoverLorentzGramRotationSection4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusSmoothFieldDescent4D

/-!
# Quotient descent of the Lorentz--Gram rotation linearization

The already computed Lorentz--Gram linearization along each spatial rotation
is the zero smooth scalar field on the genuine cover.  Its zero value makes it
invariant under every deck winding, so it descends to the genuine smooth D8
quotient and remains identically zero there.

This descends the scalar output of `J_F(R(F))`.  It does not descend the
bundle-hom rotation direction itself or construct the full global `K/J`
complex.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCoverLorentzGramRotationQuotientZero4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusReflectionFixedThroat
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothDeckInvariantFields4D
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCoverLorentzGramFrechet4D
open P0EFTJanusMappingTorusCoverLorentzGramRotationSection4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveCover := MappingTorusCover (sphereData period hPeriod)
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

/-- The cover scalar `J_F(R(F))`, now equipped with all-winding deck
invariance. -/
def actualCoverLorentzGramRotationInvariantField
    (axis : Fin 3) (first second : CoverCoordinates) :
    SmoothDeckInvariantField period hPeriod Real where
  toFun :=
    actualCoverLorentzGramRotationLinearizationField period hPeriod axis
      first second
  contMDiff_toFun :=
    actualCoverLorentzGramRotationLinearizationField_contMDiff period hPeriod
      axis first second
  deck_invariant := by
    intro winding point
    have hZero :=
      actualCoverLorentzGramRotationLinearizationField_eq_zero period hPeriod
        axis first second
    exact (congrFun hZero (winding +ᵥ point)).trans
      (congrFun hZero point).symm

/-- Smooth descent of the zero Lorentz--Gram linearization to the genuine D8
quotient. -/
def quotientLorentzGramRotationLinearizationField
    (axis : Fin 3) (first second : CoverCoordinates) :
    SmoothQuotientField period hPeriod Real :=
  descendSmooth period hPeriod Real
    (actualCoverLorentzGramRotationInvariantField period hPeriod axis
      first second)

/-- The descended scalar linearization is identically zero on the true
quotient. -/
theorem quotientLorentzGramRotationLinearizationField_apply
    (axis : Fin 3) (first second : CoverCoordinates)
    (point : EffectiveQuotient period hPeriod) :
    quotientLorentzGramRotationLinearizationField period hPeriod axis
        first second point = 0 := by
  obtain ⟨coverPoint, rfl⟩ :=
    mappingTorusMk_surjective (sphereData period hPeriod) point
  change
    actualCoverLorentzGramRotationLinearizationField period hPeriod axis
      first second coverPoint = 0
  exact congrFun
    (actualCoverLorentzGramRotationLinearizationField_eq_zero period hPeriod
      axis first second) coverPoint

end

end P0EFTJanusMappingTorusCoverLorentzGramRotationQuotientZero4D
end JanusFormal
