import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteNullFaceMobileCanonicalFaithfulness4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06PhysicalCoordinateMetricDensityCorrection4D

/-!
# Faithful null-face incidence in the physical bulk metric

This gate states the missing compatibility between one supplied faithful
T03/T05 null-face realization and the actual Candidate-A bulk metric.  It
places the same faithful face on the cut boundary through a physical partial
diffeomorphism and identifies its ambient metric matrix with the coordinate
matrix of `plusBase.metric` as a germ along the selected source patch.

No faithful realization or incidence datum is constructed here, and no
action, Euler, or density data are duplicated.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06FaithfulPhysicalFaceIncidence4D

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000

noncomputable section

open Filter Set Topology
open scoped Manifold ContDiff Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCutThroatBoundaryDoubleCover4D
open P0EFTJanusMappingTorusCutThroatSmoothFiniteCollar4D
open P0EFTJanusMappingTorusPositiveHemisphereCutBulk4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalProductEuler4D
open P0EFTJanusFiniteNullFaceMobileGeometricRealization4D
open P0EFTJanusFiniteNullFaceMobileCanonicalFaithfulness4D
open P0EFTJanusProgramPT06AmbientNullFluxPullback4D
open P0EFTJanusProgramPT06LocalC3NullFaceCutCollarIncidence4D
open P0EFTJanusProgramPT06PhysicalCoordinateMetricDensityCorrection4D

variable (period : Real) (hPeriod : period ≠ 0)
variable {NullFace : Type*} [Fintype NullFace] {face : NullFace}

local instance boundaryChartedSpace :
    ChartedSpace ThroatCoverModel (CutThroatBoundary period hPeriod) :=
  cutThroatBoundaryChartedSpace period hPeriod

local instance effectiveBulkChartedSpace :
    ChartedSpace CoverModel (ProgramPT06EffectiveBulk period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveBulkIsManifold :
    IsManifold coverModelWithCorners ω
      (ProgramPT06EffectiveBulk period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- Incidence data identifying the coordinate geometry of the supplied
faithful T03/T05 face with the actual physical bulk metric. -/
structure ProgramPT06FaithfulPhysicalFaceIncidenceDatum
    (plusBase : RegularGeneralLorentzMetric period hPeriod)
    (faithful :
      FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace)
    (face : NullFace) where
  input_mem_domain :
    input ∈ faithful.realization.geometry.domain
  sourceDomain : Set ProgramPT06NullFaceSource3
  sourceDomain_isOpen : IsOpen sourceDomain
  sourceDomain_nonempty : sourceDomain.Nonempty
  boundaryMap : ProgramPT06NullFaceSource3 →
    CutThroatBoundary period hPeriod
  boundaryMap_contMDiffOn :
    ContMDiffOn (modelWithCornersSelf Real ProgramPT06NullFaceSource3)
      throatCoverModelWithCorners 3 boundaryMap sourceDomain
  physicalChart : ProgramPT06PhysicalCoordinateChart period hPeriod
  face_mem_chart : ∀ source, source ∈ sourceDomain →
    cutThroatBoundaryToBulk period hPeriod (boundaryMap source) ∈
      physicalChart.source
  face_coordinate : ∀ source, source ∈ sourceDomain →
    physicalChart
        (cutThroatBoundaryToBulk period hPeriod (boundaryMap source)) =
      faithful.realization.geometry.embedding input face source
  ambientMetric_eventuallyEq_physical :
    ∀ source, source ∈ sourceDomain →
      faithful.realization.geometry.ambientMetric input face =ᶠ[
        𝓝 (faithful.realization.geometry.embedding input face source)]
        programPT06PhysicalCoordinateMetricMatrix
          period hPeriod physicalChart plusBase.metric

/-- Physical bulk point represented by one faithful null-face coordinate. -/
def programPT06FaithfulPhysicalFacePoint
    {plusBase : RegularGeneralLorentzMetric period hPeriod}
    {faithful :
      FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace}
    {input : FiniteNullFacePhysicalHilbert NullFace}
    (incidence : ProgramPT06FaithfulPhysicalFaceIncidenceDatum
      period hPeriod plusBase faithful input face)
    (source : ProgramPT06NullFaceSource3) :
    ProgramPT06EffectiveBulk period hPeriod :=
  cutThroatBoundaryToBulk period hPeriod (incidence.boundaryMap source)

theorem programPT06FaithfulPhysicalFacePoint_mem_chart
    {plusBase : RegularGeneralLorentzMetric period hPeriod}
    {faithful :
      FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace}
    {input : FiniteNullFacePhysicalHilbert NullFace}
    (incidence : ProgramPT06FaithfulPhysicalFaceIncidenceDatum
      period hPeriod plusBase faithful input face)
    {source : ProgramPT06NullFaceSource3}
    (hSource : source ∈ incidence.sourceDomain) :
    programPT06FaithfulPhysicalFacePoint period hPeriod incidence source ∈
      incidence.physicalChart.source :=
  incidence.face_mem_chart source hSource

/-- The faithful coordinate lies in the target of the physical chart. -/
theorem programPT06FaithfulFaceCoordinate_mem_chartTarget
    {plusBase : RegularGeneralLorentzMetric period hPeriod}
    {faithful :
      FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace}
    {input : FiniteNullFacePhysicalHilbert NullFace}
    (incidence : ProgramPT06FaithfulPhysicalFaceIncidenceDatum
      period hPeriod plusBase faithful input face)
    {source : ProgramPT06NullFaceSource3}
    (hSource : source ∈ incidence.sourceDomain) :
    faithful.realization.geometry.embedding input face source ∈
      incidence.physicalChart.target := by
  rw [← incidence.face_coordinate source hSource]
  exact incidence.physicalChart.map_source
    (incidence.face_mem_chart source hSource)

/-- Inverting the physical coordinate returns the selected cut-boundary
point. -/
theorem programPT06FaithfulPhysicalFacePoint_roundTrip
    {plusBase : RegularGeneralLorentzMetric period hPeriod}
    {faithful :
      FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace}
    {input : FiniteNullFacePhysicalHilbert NullFace}
    (incidence : ProgramPT06FaithfulPhysicalFaceIncidenceDatum
      period hPeriod plusBase faithful input face)
    {source : ProgramPT06NullFaceSource3}
    (hSource : source ∈ incidence.sourceDomain) :
    incidence.physicalChart.symm
        (faithful.realization.geometry.embedding input face source) =
      programPT06FaithfulPhysicalFacePoint period hPeriod incidence source := by
  rw [← incidence.face_coordinate source hSource]
  exact incidence.physicalChart.left_inv
    (incidence.face_mem_chart source hSource)

/-- Germ compatibility specializes to equality of the faithful ambient
matrix and the physical coordinate matrix on the face. -/
theorem programPT06FaithfulAmbientMetric_eq_physical_on_face
    {plusBase : RegularGeneralLorentzMetric period hPeriod}
    {faithful :
      FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace}
    {input : FiniteNullFacePhysicalHilbert NullFace}
    (incidence : ProgramPT06FaithfulPhysicalFaceIncidenceDatum
      period hPeriod plusBase faithful input face)
    {source : ProgramPT06NullFaceSource3}
    (hSource : source ∈ incidence.sourceDomain) :
    faithful.realization.geometry.ambientMetric input face
        (faithful.realization.geometry.embedding input face source) =
      programPT06PhysicalCoordinateMetricMatrix
        period hPeriod incidence.physicalChart plusBase.metric
        (faithful.realization.geometry.embedding input face source) :=
  (incidence.ambientMetric_eventuallyEq_physical source hSource).eq_of_nhds

/-- The faithful generator is null for the actual Candidate-A metric in the
physical face coordinate. -/
theorem programPT06FaithfulGeneratorTangent_null_physical
    {plusBase : RegularGeneralLorentzMetric period hPeriod}
    {faithful :
      FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace}
    {input : FiniteNullFacePhysicalHilbert NullFace}
    (incidence : ProgramPT06FaithfulPhysicalFaceIncidenceDatum
      period hPeriod plusBase faithful input face)
    {source : ProgramPT06NullFaceSource3}
    (hSource : source ∈ incidence.sourceDomain) :
    finiteNullFaceAmbientMetricPairing
        (programPT06PhysicalCoordinateMetricMatrix
          period hPeriod incidence.physicalChart plusBase.metric
          (faithful.realization.geometry.embedding input face source))
        (faithful.realization.geometry.generatorDifferential
          input face source.1 source.2 1)
        (faithful.realization.geometry.generatorDifferential
          input face source.1 source.2 1) = 0 := by
  rw [← programPT06FaithfulAmbientMetric_eq_physical_on_face
    period hPeriod incidence hSource]
  exact faithful.realization.geometry.generatorTangent_null
    input incidence.input_mem_domain face source.1 source.2

/-- The faithful homogeneous screen metric is the metric induced by the
actual Candidate-A physical coordinate matrix. -/
theorem programPT06FaithfulScreenMetric_eq_physical_induced
    {plusBase : RegularGeneralLorentzMetric period hPeriod}
    {faithful :
      FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace}
    {input : FiniteNullFacePhysicalHilbert NullFace}
    (incidence : ProgramPT06FaithfulPhysicalFaceIncidenceDatum
      period hPeriod plusBase faithful input face)
    {source : ProgramPT06NullFaceSource3}
    (hSource : source ∈ incidence.sourceDomain)
    (first second : Fin 2) :
    faithful.realization.geometry.screenMetric input face source.1
        first second =
      finiteNullFaceInducedScreenMetricComponent
        (programPT06PhysicalCoordinateMetricMatrix
          period hPeriod incidence.physicalChart plusBase.metric
          (faithful.realization.geometry.embedding input face source))
        (faithful.realization.geometry.screenDifferential
          input face source.1 source.2) first second := by
  rw [← programPT06FaithfulAmbientMetric_eq_physical_on_face
    period hPeriod incidence hSource]
  exact faithful.realization.geometry.screenMetric_eq_induced
    input incidence.input_mem_domain face source.1 source.2 first second

/-- The faithful generator remains orthogonal to both physical screen
directions after identifying the two metric matrices. -/
theorem programPT06FaithfulGeneratorTangent_screen_orthogonal_physical
    {plusBase : RegularGeneralLorentzMetric period hPeriod}
    {faithful :
      FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace}
    {input : FiniteNullFacePhysicalHilbert NullFace}
    (incidence : ProgramPT06FaithfulPhysicalFaceIncidenceDatum
      period hPeriod plusBase faithful input face)
    {source : ProgramPT06NullFaceSource3}
    (hSource : source ∈ incidence.sourceDomain)
    (index : Fin 2) :
    finiteNullFaceAmbientMetricPairing
        (programPT06PhysicalCoordinateMetricMatrix
          period hPeriod incidence.physicalChart plusBase.metric
          (faithful.realization.geometry.embedding input face source))
        (faithful.realization.geometry.generatorDifferential
          input face source.1 source.2 1)
        (faithful.realization.geometry.screenDifferential
          input face source.1 source.2 (EuclideanSpace.single index 1)) = 0 := by
  rw [← programPT06FaithfulAmbientMetric_eq_physical_on_face
    period hPeriod incidence hSource]
  exact faithful.realization.geometry.generatorTangent_screen_orthogonal
    input incidence.input_mem_domain face source.1 source.2 index

end
end P0EFTJanusProgramPT06FaithfulPhysicalFaceIncidence4D
end JanusFormal
