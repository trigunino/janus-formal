import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGlobalHolonomicScalarStaticH1ContinuousFrameControl4D

/-!
# Finite generator patches and the preferred-chart transition lock

The closed supports of the partition used to construct
`finiteSmoothTangentFrame` give the required finite compact cover.  The only
datum not supplied by the manifold API is continuity, on those patches, of
the raw `CoverCoordinates` value of a smooth tangent-bundle section.  This is
not the same as continuity of the section in the tangent-bundle topology.

This gate isolates that exact preferred-chart transition property and proves
that it constructs the local-finite holonomic coefficient data, hence the
uniform graph ellipticity bridge, with no further analytic hypothesis.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusGlobalHolonomicScalarStaticH1FiniteFramePatchClosure4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff BigOperators Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarWeakJacobiRiesz4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarStaticH1UniformEllipticity4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarStaticH1ContinuousFrameControl4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

private def finiteGeneratorPatchEquivFin :
    FiniteTangentGeneratorPatch period hPeriod ≃
      Fin (Fintype.card (FiniteTangentGeneratorPatch period hPeriod)) :=
  Fintype.equivFin (FiniteTangentGeneratorPatch period hPeriod)

/-- Exact missing regularity: on each tangent-trivialization patch, the raw
model coordinate of every generator is continuous.
`SmoothD8Frame.contMDiff_vector` only states smoothness into the nontrivial
tangent bundle and does not imply this projection property. -/
structure FiniteSmoothTangentFrameRawPatchContinuity : Prop where
  continuousOn_vector : ∀
      (patch : FiniteTangentGeneratorPatch period hPeriod)
      (frameIndex : Fin (finiteSmoothTangentFrame period hPeriod).count),
    ContinuousOn
      (fun point : EffectiveQuotient period hPeriod =>
        (finiteSmoothTangentFrame period hPeriod).vectorAt point frameIndex)
      (finiteTangentGeneratorOpenPatch period hPeriod patch)

theorem FiniteSmoothTangentFrameRawPatchContinuity.coefficient_continuousOn
    (regularity : FiniteSmoothTangentFrameRawPatchContinuity period hPeriod)
    (patch : FiniteTangentGeneratorPatch period hPeriod)
    (frameIndex : Fin (finiteSmoothTangentFrame period hPeriod).count)
    (holonomicIndex : Fin 4) :
    ContinuousOn
      (fun point : EffectiveQuotient period hPeriod =>
        smoothFrameHolonomicCoefficient period hPeriod
          (finiteSmoothTangentFrame period hPeriod) point frameIndex
            holonomicIndex)
      (finiteTangentGeneratorClosedPatch period hPeriod patch) := by
  have hVector := (regularity.continuousOn_vector patch frameIndex).mono
    (finiteTangentGeneratorClosedPatch_subset_openPatch period hPeriod patch)
  change ContinuousOn
    (fun point : EffectiveQuotient period hPeriod =>
      ((finiteSmoothTangentFrame period hPeriod).vectorAt point frameIndex :
        CoverCoordinates))
    (finiteTangentGeneratorClosedPatch period hPeriod patch) at hVector
  refine Fin.cases ?_ (fun spatial => ?_) holonomicIndex
  · simpa [smoothFrameHolonomicCoefficient, holonomicVectorCoefficient,
      Function.comp_def] using
      hVector.snd
  · simpa [smoothFrameHolonomicCoefficient, holonomicVectorCoefficient,
      Function.comp_def] using
      (PiLp.continuous_apply 2
        (fun _ : Fin 3 => Real) spatial).continuousOn.comp
          hVector.fst fun _ _ => Set.mem_univ _

/-- The finite partition cover plus raw transition regularity construct the
previously isolated local-finite coefficient datum. -/
def FiniteSmoothTangentFrameRawPatchContinuity.toLocalFiniteCoefficients
    (regularity : FiniteSmoothTangentFrameRawPatchContinuity period hPeriod) :
    LocalFiniteHolonomicFrameCoefficients period hPeriod
      (finiteSmoothTangentFrame period hPeriod) where
  patchCount := Fintype.card (FiniteTangentGeneratorPatch period hPeriod)
  closedPatch patch := finiteTangentGeneratorClosedPatch period hPeriod
    ((finiteGeneratorPatchEquivFin period hPeriod).symm patch)
  closedPatch_isClosed patch :=
    finiteTangentGeneratorClosedPatch_isClosed period hPeriod
      ((finiteGeneratorPatchEquivFin period hPeriod).symm patch)
  covers point := by
    obtain ⟨patch, hPatch⟩ :=
      finiteTangentGeneratorClosedPatch_covers period hPeriod point
    exact ⟨finiteGeneratorPatchEquivFin period hPeriod patch, by simpa⟩
  coefficients _patch point frameIndex holonomicIndex :=
    smoothFrameHolonomicCoefficient period hPeriod
      (finiteSmoothTangentFrame period hPeriod) point frameIndex holonomicIndex
  continuousOn_coefficients patch frameIndex holonomicIndex :=
    FiniteSmoothTangentFrameRawPatchContinuity.coefficient_continuousOn
      period hPeriod regularity
      ((finiteGeneratorPatchEquivFin period hPeriod).symm patch)
        frameIndex holonomicIndex
  covector_decomposition _patch point _hPoint frameIndex covector :=
    smoothFrameHolonomicCoefficient_covector_decomposition period hPeriod
      (finiteSmoothTangentFrame period hPeriod) point frameIndex covector

/-- The exact preferred-chart transition property closes uniform graph
ellipticity for the actual finite smooth tangent family. -/
def FiniteSmoothTangentFrameRawPatchContinuity.toUniformGraphEllipticity
    (regularity : FiniteSmoothTangentFrameRawPatchContinuity period hPeriod)
    (data : PositiveStaticGlobalScalarData period hPeriod) :
    StaticScalarUniformGraphEllipticity period hPeriod data
      (finiteSmoothTangentFrame period hPeriod) :=
  finiteSmoothTangentFrameUniformGraphEllipticity period hPeriod data
    (FiniteSmoothTangentFrameRawPatchContinuity.toLocalFiniteCoefficients
      period hPeriod regularity)

end

end P0EFTJanusMappingTorusGlobalHolonomicScalarStaticH1FiniteFramePatchClosure4D
end JanusFormal
