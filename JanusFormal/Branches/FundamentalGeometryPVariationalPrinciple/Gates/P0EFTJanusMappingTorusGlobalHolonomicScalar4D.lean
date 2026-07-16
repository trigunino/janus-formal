import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusSmoothThroatTrace4D

/-!
# Global holonomic scalar fields on the effective D8 quotient

The covector field is the manifold differential of the same global smooth
scalar. Restriction to the throat obeys the exact manifold chain rule, and PT
pullback transports the differential by the PT tangent map. No metric
contraction, Sobolev completion or Euler equation is claimed here.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusGlobalHolonomicScalar4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusPTInvolution
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothPTInvolution
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothPTFieldAction4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D

variable (period : Real) (hPeriod : Not (period = 0))

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev throatData := fixedEquatorData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)
private abbrev EffectiveThroat := MappingTorus (throatData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

/-- The genuine manifold differential of a global scalar field. -/
def scalarDifferential
    (field : SmoothQuotientField period hPeriod Real)
    (point : EffectiveQuotient period hPeriod) :
    TangentSpace coverModelWithCorners point →L[Real] Real :=
  mfderiv coverModelWithCorners 𝓘(Real, Real) field.toFun point

/-- Independent scalar value plus its uniquely induced holonomic covector. -/
structure GlobalHolonomicScalar where
  value : SmoothQuotientField period hPeriod Real
  covector : forall point : EffectiveQuotient period hPeriod,
    TangentSpace coverModelWithCorners point →L[Real] Real
  holonomic : covector = scalarDifferential period hPeriod value

def GlobalHolonomicScalar.ofSmooth
    (field : SmoothQuotientField period hPeriod Real) :
    GlobalHolonomicScalar period hPeriod where
  value := field
  covector := scalarDifferential period hPeriod field
  holonomic := rfl

theorem existsUnique_holonomicCovector
    (field : SmoothQuotientField period hPeriod Real) :
    ∃! covector : forall point : EffectiveQuotient period hPeriod,
        TangentSpace coverModelWithCorners point →L[Real] Real,
      covector = scalarDifferential period hPeriod field := by
  exact ⟨scalarDifferential period hPeriod field, rfl,
    fun candidate hCandidate => hCandidate⟩

/-- The throat differential is exactly the pullback of the ambient
differential by the derivative of the actual throat inclusion. -/
theorem throatTrace_mfderiv
    (field : SmoothQuotientField period hPeriod Real)
    (point : EffectiveThroat period hPeriod) :
    mfderiv throatCoverModelWithCorners 𝓘(Real, Real)
        (throatTrace period hPeriod Real field).toFun point =
      (scalarDifferential period hPeriod field
        (fixedThroatQuotientInclusion period hPeriod point)).comp
        (mfderiv throatCoverModelWithCorners coverModelWithCorners
          (fixedThroatQuotientInclusion period hPeriod) point) := by
  have hOuter := field.contMDiff_toFun.mdifferentiableAt
    (x := fixedThroatQuotientInclusion period hPeriod point) (by simp)
  have hInner :=
    (fixedThroatQuotientInclusion_contMDiff period hPeriod).mdifferentiableAt
      (x := point) (by simp)
  exact mfderiv_comp point hOuter hInner

/-- PT pullback transports the holonomic covector by the tangent map of the
actual analytic PT diffeomorphism. -/
theorem ptPullback_mfderiv
    (field : SmoothQuotientField period hPeriod Real)
    (point : EffectiveQuotient period hPeriod) :
    scalarDifferential period hPeriod
        (ptPullback period hPeriod Real field) point =
      (scalarDifferential period hPeriod field
        (reflectedSpherePT period hPeriod point)).comp
        (mfderiv coverModelWithCorners coverModelWithCorners
          (reflectedSpherePT period hPeriod) point) := by
  have hOuter := field.contMDiff_toFun.mdifferentiableAt
    (x := reflectedSpherePT period hPeriod point) (by simp)
  have hInner :=
    (reflectedSpherePT_contMDiff period hPeriod).mdifferentiableAt
      (x := point) (by simp)
  exact mfderiv_comp point hOuter hInner

end

end P0EFTJanusMappingTorusGlobalHolonomicScalar4D
end JanusFormal
