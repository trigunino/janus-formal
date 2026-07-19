import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCompleteVariationBoundaryDomainBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCompleteVariationMatterLLActionHessian4D

/-!
# Matter/LL action, Hessian and boundary domain on one complete variation

The present matter plus differential-LL functional and its Hessian consume the
independent component of `ProgramPCompleteVariation4D`.  This gate proves
exactly that changing only the normal, tangent-ghost and full-metric completion
slots changes neither that functional nor its boundary admissibility.  It
therefore records the current sectorial agreement without pretending that EH
or Maxwell terms are present.
-/

namespace JanusFormal
namespace P0EFTJanusCompleteVariationMatterLLBoundaryAgreement4D

set_option autoImplicit false
noncomputable section

open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusInducedFieldVariation4D
open P0EFTJanusProgramPCommonGeometricDomain4D
open P0EFTJanusD8NormalBundleD9DisplacementBridge4D
open P0EFTJanusMappingTorusD8NonabelianGhostThroatBRST4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusMappingTorusScalarDiffeomorphismNoetherOperator4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusGlobalMatterMultipletActualEulerHessian4D
open P0EFTJanusCompleteVariationMatterLLActionHessian4D
open P0EFTJanusCompleteVariationBoundaryDomainBridge4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance : BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

theorem matterLLActionCurve_withGeometricCompletionSlots
    (data : MatterMultipletActionData period hPeriod)
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (variation : ProgramPCompleteVariation4D period hPeriod)
    (normalDisplacement : Sector → SmoothNormalDisplacement period hPeriod)
    (diffeomorphismGhost : Sector → CInfinityThroatGhost period hPeriod)
    (fullMetricPerturbation :
      Sector → SmoothSymmetricCovariantTwoTensor period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) (parameter : Real) :
    completeVariationMatterLLActionCurve period hPeriod data frame fields
        (withGeometricCompletionSlots period hPeriod variation
          normalDisplacement diffeomorphismGhost fullMetricPerturbation)
        mu parameter =
      completeVariationMatterLLActionCurve period hPeriod data frame fields
        variation mu parameter :=
  rfl

theorem matterLLFirstVariation_withGeometricCompletionSlots
    (data : MatterMultipletActionData period hPeriod)
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (variation : ProgramPCompleteVariation4D period hPeriod)
    (normalDisplacement : Sector → SmoothNormalDisplacement period hPeriod)
    (diffeomorphismGhost : Sector → CInfinityThroatGhost period hPeriod)
    (fullMetricPerturbation :
      Sector → SmoothSymmetricCovariantTwoTensor period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) :
    completeVariationMatterLLFirstVariation period hPeriod data frame fields
        (withGeometricCompletionSlots period hPeriod variation
          normalDisplacement diffeomorphismGhost fullMetricPerturbation) mu =
      completeVariationMatterLLFirstVariation period hPeriod data frame fields
        variation mu :=
  rfl

theorem matterLLHessian_withGeometricCompletionSlots
    (data : MatterMultipletActionData period hPeriod)
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (first second : ProgramPCompleteVariation4D period hPeriod)
    (firstNormal secondNormal :
      Sector → SmoothNormalDisplacement period hPeriod)
    (firstGhost secondGhost : Sector → CInfinityThroatGhost period hPeriod)
    (firstMetric secondMetric :
      Sector → SmoothSymmetricCovariantTwoTensor period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) :
    completeVariationMatterLLHessian period hPeriod data frame fields
        (withGeometricCompletionSlots period hPeriod first
          firstNormal firstGhost firstMetric)
        (withGeometricCompletionSlots period hPeriod second
          secondNormal secondGhost secondMetric) mu =
      completeVariationMatterLLHessian period hPeriod data frame fields
        first second mu :=
  rfl

end
end P0EFTJanusCompleteVariationMatterLLBoundaryAgreement4D
end JanusFormal
