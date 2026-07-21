import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusEquatorialTubularDiffeomorph4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCanonicalLatitudeScalarCurrentJointSmooth4D

namespace JanusFormal
namespace P0EFTJanusEquatorialBandScalarCurrentJointSmooth4D
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalNormalLiftContinuityReduction4D
open P0EFTJanusEquatorialTubularAmbientInverseJointSmooth4D
open P0EFTJanusEquatorialTubularDiffeomorph4D
open P0EFTJanusCanonicalLatitudeScalarCurrentJointSmooth4D

variable (period : Real) (hPeriod : period ≠ 0)

local instance : Fact (Module.finrank Real EuclideanR3 = 2 + 1) := ⟨by simp⟩

def equatorialBandCanonicalParameter
    (input : equatorialSphericalBandOpen × Real) : CanonicalLatitudeParameter :=
  (((equatorialTwoSphereHomeomorph
      (equatorialTubularSmoothInverse input.1).1), input.2),
    (equatorialTubularSmoothInverse input.1).2.1)

theorem equatorialBandCanonicalParameter_contMDiff :
    ContMDiff ((𝓡 3).prod 𝓘(Real, Real))
      canonicalLatitudeParameterModelWithCorners ∞
      equatorialBandCanonicalParameter := by
  have hFst : ContMDiff ((𝓡 3).prod 𝓘(Real, Real)) (𝓡 3) ∞
      (fun input : equatorialSphericalBandOpen × Real => input.1) := contMDiff_fst
  have hInverse : ContMDiff ((𝓡 3).prod 𝓘(Real, Real))
      ((𝓡 2).prod 𝓘(Real, Real)) ∞
      (fun input : equatorialSphericalBandOpen × Real =>
        equatorialTubularSmoothInverse input.1) :=
    equatorialTubularSmoothInverse_contMDiff.comp hFst
  have hBaseEquatorial : ContMDiff ((𝓡 3).prod 𝓘(Real, Real)) (𝓡 2) ∞
      (fun input : equatorialSphericalBandOpen × Real =>
        (equatorialTubularSmoothInverse input.1).1) := contMDiff_fst.comp hInverse
  have hBaseStandard :=
    (chartedSpacePullback_toFun_contMDiff (𝓡 2) ∞
      equatorialTwoSphereHomeomorph).comp hBaseEquatorial
  have hTime : ContMDiff ((𝓡 3).prod 𝓘(Real, Real)) 𝓘(Real, Real) ∞
      (fun input : equatorialSphericalBandOpen × Real => input.2) := contMDiff_snd
  have hNormalSubtype := contMDiff_snd.comp hInverse
  have hNormal : ContMDiff ((𝓡 3).prod 𝓘(Real, Real)) 𝓘(Real, Real) ∞
      (fun input : equatorialSphericalBandOpen × Real =>
        (equatorialTubularSmoothInverse input.1).2.1) :=
    contMDiff_subtype_val.comp hNormalSubtype
  exact (hBaseStandard.prodMk hTime).prodMk hNormal

def equatorialBandScalarCurrentDensity
    (field test : SmoothQuotientField period hPeriod Real)
    (input : equatorialSphericalBandOpen × Real) : Real :=
  jointCutoffCollarScalarCurrentDensity period hPeriod field test
    (equatorialBandCanonicalParameter input)

theorem equatorialBandScalarCurrentDensity_contMDiff
    (field test : SmoothQuotientField period hPeriod Real) :
    ContMDiff ((𝓡 3).prod 𝓘(Real, Real)) 𝓘(Real, Real) ∞
      (equatorialBandScalarCurrentDensity period hPeriod field test) :=
  (jointCutoffCollarScalarCurrentDensity_contMDiff period hPeriod field test).comp
    equatorialBandCanonicalParameter_contMDiff

end
end P0EFTJanusEquatorialBandScalarCurrentJointSmooth4D
end JanusFormal
