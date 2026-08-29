import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeHeatMellinAnalyticDifferenceFamily4D

/-!
# Derive reference-atlas coefficients from analytic zeta differences

A spectral-cut atlas compares one actual heat family with several reference
families.  The local relative zeta coefficient should not be supplied
independently once the following are known:

* the actual zeta coefficient vanishes in the selected unitary frame;
* each standalone reference zeta coefficient is minus its logarithmic operator
  trace;
* each local relative continuation is the analytic continuation of
  `actual - reference`.

This file packages those inputs and derives all base and local coefficient
agreements required by the determinant atlas.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRelativeZetaReferenceAtlasDerivation4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPRelativeHeatMellinAnalyticDifferenceFamily4D
open P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D
open P0EFTJanusProgramPRelativeZetaDeterminantConnection4D

variable {Index : Type*}

/-- Actual/reference spectral data from which all relative connection
coefficients are derived. -/
structure RelativeZetaReferenceAtlasDerivationData (Index : Type*) where
  actualFamily : RelativeHeatMellinZetaFamilyData
  actualCoefficient_zero : ∀ parameter,
    relativeZetaConnectionCoefficient actualFamily.toZetaFamily parameter = 0
  baseRelativeFamily : RelativeHeatMellinZetaFamilyData
  baseReferenceFamily : RelativeHeatMellinZetaFamilyData
  baseReferenceTrace : Real → Real
  baseDifference : RelativeHeatMellinAnalyticDifferenceFamilyData
    baseRelativeFamily actualFamily baseReferenceFamily
  baseReferenceCoefficient : ∀ parameter,
    relativeZetaConnectionCoefficient baseReferenceFamily.toZetaFamily parameter =
      -baseReferenceTrace parameter
  localRelativeFamily : Index → RelativeHeatMellinZetaFamilyData
  localReferenceFamily : Index → RelativeHeatMellinZetaFamilyData
  localReferenceTrace : Index → Real → Real
  localDifference : ∀ index,
    RelativeHeatMellinAnalyticDifferenceFamilyData
      (localRelativeFamily index) actualFamily (localReferenceFamily index)
  localReferenceCoefficient : ∀ index parameter,
    relativeZetaConnectionCoefficient
        (localReferenceFamily index).toZetaFamily parameter =
      -localReferenceTrace index parameter

namespace RelativeZetaReferenceAtlasDerivationData

/-- Base relative coefficient equals the base reference logarithmic trace. -/
theorem baseCoefficient_eq_referenceTrace
    (data : RelativeZetaReferenceAtlasDerivationData Index)
    (parameter : Real) :
    relativeZetaConnectionCoefficient data.baseRelativeFamily.toZetaFamily
        parameter = data.baseReferenceTrace parameter :=
  data.baseDifference.connectionCoefficient_eq_referenceTrace
    data.actualCoefficient_zero data.baseReferenceTrace
      data.baseReferenceCoefficient parameter

/-- Every local relative coefficient equals its corresponding reference trace. -/
theorem localCoefficient_eq_referenceTrace
    (data : RelativeZetaReferenceAtlasDerivationData Index)
    (index : Index) (parameter : Real) :
    relativeZetaConnectionCoefficient
        (data.localRelativeFamily index).toZetaFamily parameter =
      data.localReferenceTrace index parameter :=
  (data.localDifference index).connectionCoefficient_eq_referenceTrace
    data.actualCoefficient_zero (data.localReferenceTrace index)
      (data.localReferenceCoefficient index) parameter

/-- Difference formula for every local regularized zeta derivative. -/
theorem localZetaPrime_eq_difference
    (data : RelativeZetaReferenceAtlasDerivationData Index)
    (index : Index) (parameter : Real) :
    (data.localRelativeFamily index).zetaPrimeAtZero parameter =
      data.actualFamily.zetaPrimeAtZero parameter -
        (data.localReferenceFamily index).zetaPrimeAtZero parameter :=
  (data.localDifference index).zetaPrimeAtZero_eq_difference parameter

/-- Quotient formula for every local determinant coordinate. -/
theorem localDeterminant_eq_div
    (data : RelativeZetaReferenceAtlasDerivationData Index)
    (index : Index) (parameter : Real) :
    relativeHeatMellinZetaFamilyDeterminant
        (data.localRelativeFamily index) parameter =
      relativeHeatMellinZetaFamilyDeterminant data.actualFamily parameter /
        relativeHeatMellinZetaFamilyDeterminant
          (data.localReferenceFamily index) parameter :=
  (data.localDifference index).determinant_eq_div parameter

/-- Public reference-atlas derivation checkpoint. -/
theorem relative_zeta_reference_atlas_derivation_gate
    (data : RelativeZetaReferenceAtlasDerivationData Index) :
    (∀ parameter,
      relativeZetaConnectionCoefficient data.baseRelativeFamily.toZetaFamily
          parameter = data.baseReferenceTrace parameter) ∧
    (∀ index parameter,
      relativeZetaConnectionCoefficient
          (data.localRelativeFamily index).toZetaFamily parameter =
        data.localReferenceTrace index parameter) ∧
    (∀ index parameter,
      relativeHeatMellinZetaFamilyDeterminant
          (data.localRelativeFamily index) parameter =
        relativeHeatMellinZetaFamilyDeterminant data.actualFamily parameter /
          relativeHeatMellinZetaFamilyDeterminant
            (data.localReferenceFamily index) parameter) :=
  ⟨data.baseCoefficient_eq_referenceTrace,
    data.localCoefficient_eq_referenceTrace,
    data.localDeterminant_eq_div⟩

end RelativeZetaReferenceAtlasDerivationData

end
end P0EFTJanusProgramPRelativeZetaReferenceAtlasDerivation4D
end JanusFormal
