import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusLatitudeCutoffCurrentZeroExtensionPrerequisite4D

namespace JanusFormal
namespace P0EFTJanusCanonicalLatitudeScalarCurrentJointSmooth4D
set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalNormalLiftContinuityReduction4D
open P0EFTJanusMappingTorusCanonicalLatitudeScalarIPP4D
open P0EFTJanusMappingTorusCanonicalLatitudeScalarGreenCurrent4D
open P0EFTJanusMappingTorusCanonicalLatitudeCutoffNormalField4D
open P0EFTJanusMappingTorusCanonicalLatitudeCutoffCurrentLocalStokes4D
open P0EFTJanusLatitudeCutoffCurrentZeroExtensionPrerequisite4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance : IsManifold coverModelWithCorners ω
    (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance : Fact (Module.finrank Real EuclideanR3 = 2 + 1) := ⟨by simp⟩

local instance : ChartedSpace (EuclideanSpace Real (Fin 2))
    (Metric.sphere (0 : EuclideanR3) 1) := inferInstance

local instance : ChartedSpace CanonicalLatitudeParameterModel
    CanonicalLatitudeParameter := inferInstance

def jointCanonicalLatitudeValue
    (field : SmoothQuotientField period hPeriod Real)
    (parameter : CanonicalLatitudeParameter) : Real :=
  field (canonicalLatitudeCollarMap period hPeriod parameter)

theorem jointCanonicalLatitudeValue_contMDiff
    (field : SmoothQuotientField period hPeriod Real) :
    ContMDiff canonicalLatitudeParameterModelWithCorners 𝓘(Real, Real) ∞
      (jointCanonicalLatitudeValue period hPeriod field) :=
  field.contMDiff_toFun.comp (canonicalLatitudeCollar_contMDiff period hPeriod)

theorem jointCanonicalLatitudeValue_eq
    (field : SmoothQuotientField period hPeriod Real)
    (parameter : CanonicalLatitudeParameter) :
    jointCanonicalLatitudeValue period hPeriod field parameter =
      canonicalLatitudeValue period hPeriod field parameter.1 parameter.2 := rfl

def jointCanonicalLatitudeDerivative
    (field : SmoothQuotientField period hPeriod Real)
    (parameter : CanonicalLatitudeParameter) : Real :=
  (tangentMap coverModelWithCorners 𝓘(Real, Real) field.toFun
    (canonicalLatitudeNormalLift period hPeriod parameter)).2

theorem jointCanonicalLatitudeDerivative_contMDiff
    (field : SmoothQuotientField period hPeriod Real) :
    ContMDiff canonicalLatitudeParameterModelWithCorners 𝓘(Real, Real) ∞
      (jointCanonicalLatitudeDerivative period hPeriod field) := by
  exact (contMDiff_snd_tangentBundle_modelSpace Real 𝓘(Real, Real)).comp
    ((field.contMDiff_toFun.contMDiff_tangentMap (by simp)).comp
      (canonicalLatitudeNormalLift_contMDiff period hPeriod))

theorem jointCanonicalLatitudeDerivative_eq
    (field : SmoothQuotientField period hPeriod Real)
    (parameter : CanonicalLatitudeParameter) :
    jointCanonicalLatitudeDerivative period hPeriod field parameter =
      canonicalLatitudeDerivative period hPeriod field parameter.1 parameter.2 := by
  rw [canonicalLatitudeDerivative_eq_mvfderiv_normal]
  rfl

def jointCutoffCollarScalarCurrentDensity
    (field test : SmoothQuotientField period hPeriod Real)
    (parameter : CanonicalLatitudeParameter) : Real :=
  canonicalLatitudeCollarCutoff parameter.2 *
    (jointCanonicalLatitudeValue period hPeriod field parameter *
        jointCanonicalLatitudeDerivative period hPeriod test parameter -
      jointCanonicalLatitudeDerivative period hPeriod field parameter *
        jointCanonicalLatitudeValue period hPeriod test parameter)

theorem jointCutoffCollarScalarCurrentDensity_contMDiff
    (field test : SmoothQuotientField period hPeriod Real) :
    ContMDiff canonicalLatitudeParameterModelWithCorners 𝓘(Real, Real) ∞
      (jointCutoffCollarScalarCurrentDensity period hPeriod field test) := by
  exact (canonicalLatitudeCollarCutoff_contDiff.contMDiff.comp contMDiff_snd).mul
    (((jointCanonicalLatitudeValue_contMDiff period hPeriod field).mul
      (jointCanonicalLatitudeDerivative_contMDiff period hPeriod test)).sub
      ((jointCanonicalLatitudeDerivative_contMDiff period hPeriod field).mul
        (jointCanonicalLatitudeValue_contMDiff period hPeriod test)))

theorem jointCutoffCollarScalarCurrentDensity_eq
    (field test : SmoothQuotientField period hPeriod Real)
    (parameter : CanonicalLatitudeParameter) :
    jointCutoffCollarScalarCurrentDensity period hPeriod field test parameter =
      cutoffCollarScalarCurrentDensity period hPeriod field test
        parameter.1 parameter.2 := by
  rw [jointCutoffCollarScalarCurrentDensity, cutoffCollarScalarCurrentDensity,
    canonicalLatitudeScalarGreenCurrent, jointCanonicalLatitudeValue_eq,
    jointCanonicalLatitudeValue_eq, jointCanonicalLatitudeDerivative_eq,
    jointCanonicalLatitudeDerivative_eq]

theorem jointCutoffCollarScalarCurrentDensity_eq_zero_of_one_le_abs
    (field test : SmoothQuotientField period hPeriod Real)
    (parameter : CanonicalLatitudeParameter)
    (hNormal : 1 ≤ |parameter.2|) :
    jointCutoffCollarScalarCurrentDensity period hPeriod field test parameter = 0 := by
  rw [jointCutoffCollarScalarCurrentDensity_eq]
  exact cutoffCollarScalarCurrentDensity_eq_zero_of_one_le_abs period hPeriod
    field test parameter.1 parameter.2 hNormal

theorem jointCutoffCollarScalarCurrentDensity_eventuallyEq_zero
    (field test : SmoothQuotientField period hPeriod Real)
    (parameter : CanonicalLatitudeParameter)
    (hNormal : 1 < |parameter.2|) :
    jointCutoffCollarScalarCurrentDensity period hPeriod field test =ᶠ[𝓝 parameter]
      0 := by
  have hOpen : IsOpen {current : CanonicalLatitudeParameter | 1 < |current.2|} :=
    isOpen_lt continuous_const (continuous_abs.comp continuous_snd)
  filter_upwards [hOpen.mem_nhds hNormal] with current hCurrent
  exact jointCutoffCollarScalarCurrentDensity_eq_zero_of_one_le_abs period hPeriod
    field test current (le_of_lt hCurrent)

end
end P0EFTJanusCanonicalLatitudeScalarCurrentJointSmooth4D
end JanusFormal
