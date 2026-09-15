import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06FaithfulPhysicalFaceIncidence4D

/-!
# Covered faithful physical null-face atlas

This gate packages the local incidence of Gate 1070 into a family of patches
covering every source point of every face of the same faithful realization.
It derives global pointwise nullity, screen orthogonality, and the induced
screen metric for the Candidate-A base metric.

The covered atlas remains supplied data.  No canonical inhabitant, transition
orientation, measure, or integrated statement is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06FaithfulPhysicalFaceAtlas4D

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000

noncomputable section

open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalProductEuler4D
open P0EFTJanusFiniteNullFaceMobileGeometricRealization4D
open P0EFTJanusFiniteNullFaceMobileCanonicalFaithfulness4D
open P0EFTJanusProgramPT06AmbientNullFluxPullback4D
open P0EFTJanusProgramPT06PhysicalCoordinateMetricDensityCorrection4D
open P0EFTJanusProgramPT06FaithfulPhysicalFaceIncidence4D

variable (period : Real) (hPeriod : period ≠ 0)
variable {NullFace : Type*} [Fintype NullFace]

/-- A common family of physical face charts covering every faithful source
coordinate.  The same patch type is used for all admissible inputs and faces. -/
structure ProgramPT06FaithfulPhysicalFaceAtlasDatum
    (plusBase : RegularGeneralLorentzMetric period hPeriod)
    (faithful :
      FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace) where
  Patch : Type*
  incidence :
    (input : FiniteNullFacePhysicalHilbert NullFace) →
      (hInput : input ∈ faithful.realization.geometry.domain) →
        (face : NullFace) → Patch →
          ProgramPT06FaithfulPhysicalFaceIncidenceDatum
            period hPeriod plusBase faithful input face
  cover :
    ∀ (input : FiniteNullFacePhysicalHilbert NullFace)
      (hInput : input ∈ faithful.realization.geometry.domain)
      (face : NullFace) (source : ProgramPT06NullFaceSource3),
      ∃ patch : Patch,
        source ∈ (incidence input hInput face patch).sourceDomain

/-- Every faithful face coordinate is represented in at least one physical
chart whose metric germ is the Candidate-A base metric. -/
theorem ProgramPT06FaithfulPhysicalFaceAtlasDatum.exists_metric_identification
    {plusBase : RegularGeneralLorentzMetric period hPeriod}
    {faithful :
      FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace}
    (atlas : ProgramPT06FaithfulPhysicalFaceAtlasDatum
      period hPeriod plusBase faithful)
    (input : FiniteNullFacePhysicalHilbert NullFace)
    (hInput : input ∈ faithful.realization.geometry.domain)
    (face : NullFace) (source : ProgramPT06NullFaceSource3) :
    ∃ patch : atlas.Patch,
      faithful.realization.geometry.ambientMetric input face
          (faithful.realization.geometry.embedding input face source) =
        programPT06PhysicalCoordinateMetricMatrix period hPeriod
          (atlas.incidence input hInput face patch).physicalChart
          plusBase.metric
          (faithful.realization.geometry.embedding input face source) := by
  obtain ⟨patch, hSource⟩ := atlas.cover input hInput face source
  exact ⟨patch,
    programPT06FaithfulAmbientMetric_eq_physical_on_face period hPeriod
      (atlas.incidence input hInput face patch) hSource⟩

/-- The faithful generator is physically null at every covered source point. -/
theorem ProgramPT06FaithfulPhysicalFaceAtlasDatum.generator_null
    {plusBase : RegularGeneralLorentzMetric period hPeriod}
    {faithful :
      FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace}
    (atlas : ProgramPT06FaithfulPhysicalFaceAtlasDatum
      period hPeriod plusBase faithful)
    (input : FiniteNullFacePhysicalHilbert NullFace)
    (hInput : input ∈ faithful.realization.geometry.domain)
    (face : NullFace) (source : ProgramPT06NullFaceSource3) :
    ∃ patch : atlas.Patch,
      finiteNullFaceAmbientMetricPairing
          (programPT06PhysicalCoordinateMetricMatrix period hPeriod
            (atlas.incidence input hInput face patch).physicalChart
            plusBase.metric
            (faithful.realization.geometry.embedding input face source))
          (faithful.realization.geometry.generatorDifferential
            input face source.1 source.2 1)
          (faithful.realization.geometry.generatorDifferential
            input face source.1 source.2 1) = 0 := by
  obtain ⟨patch, hSource⟩ := atlas.cover input hInput face source
  exact ⟨patch,
    programPT06FaithfulGeneratorTangent_null_physical period hPeriod
      (atlas.incidence input hInput face patch) hSource⟩

/-- The faithful screen metric is physically induced in a covering chart at
every source point. -/
theorem ProgramPT06FaithfulPhysicalFaceAtlasDatum.screenMetric_induced
    {plusBase : RegularGeneralLorentzMetric period hPeriod}
    {faithful :
      FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace}
    (atlas : ProgramPT06FaithfulPhysicalFaceAtlasDatum
      period hPeriod plusBase faithful)
    (input : FiniteNullFacePhysicalHilbert NullFace)
    (hInput : input ∈ faithful.realization.geometry.domain)
    (face : NullFace) (source : ProgramPT06NullFaceSource3)
    (first second : Fin 2) :
    ∃ patch : atlas.Patch,
      faithful.realization.geometry.screenMetric input face source.1
          first second =
        finiteNullFaceInducedScreenMetricComponent
          (programPT06PhysicalCoordinateMetricMatrix period hPeriod
            (atlas.incidence input hInput face patch).physicalChart
            plusBase.metric
            (faithful.realization.geometry.embedding input face source))
          (faithful.realization.geometry.screenDifferential
            input face source.1 source.2) first second := by
  obtain ⟨patch, hSource⟩ := atlas.cover input hInput face source
  exact ⟨patch,
    programPT06FaithfulScreenMetric_eq_physical_induced period hPeriod
      (atlas.incidence input hInput face patch) hSource first second⟩

/-- The faithful null generator is physically orthogonal to each screen
direction at every source point. -/
theorem ProgramPT06FaithfulPhysicalFaceAtlasDatum.generator_screen_orthogonal
    {plusBase : RegularGeneralLorentzMetric period hPeriod}
    {faithful :
      FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace}
    (atlas : ProgramPT06FaithfulPhysicalFaceAtlasDatum
      period hPeriod plusBase faithful)
    (input : FiniteNullFacePhysicalHilbert NullFace)
    (hInput : input ∈ faithful.realization.geometry.domain)
    (face : NullFace) (source : ProgramPT06NullFaceSource3)
    (index : Fin 2) :
    ∃ patch : atlas.Patch,
      finiteNullFaceAmbientMetricPairing
          (programPT06PhysicalCoordinateMetricMatrix period hPeriod
            (atlas.incidence input hInput face patch).physicalChart
            plusBase.metric
            (faithful.realization.geometry.embedding input face source))
          (faithful.realization.geometry.generatorDifferential
            input face source.1 source.2 1)
          (faithful.realization.geometry.screenDifferential
            input face source.1 source.2
              (EuclideanSpace.single index 1)) = 0 := by
  obtain ⟨patch, hSource⟩ := atlas.cover input hInput face source
  exact ⟨patch,
    programPT06FaithfulGeneratorTangent_screen_orthogonal_physical
      period hPeriod (atlas.incidence input hInput face patch) hSource index⟩

end
end P0EFTJanusProgramPT06FaithfulPhysicalFaceAtlas4D
end JanusFormal
