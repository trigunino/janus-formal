import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameSylvesterCornerLocalRoot4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalLocalVariationalChart4D

/-!
# Local Candidate-A root on the intrinsic Sylvester-regular stratum

The ambient equivalence and its compatibility with the finite-frame projector
give bijectivity on the complete corner.  The existing Banach inverse theorem
then supplies the open local `C²` root germ.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameSylvesterRegularStratumLocalRoot4D

set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option synthInstance.maxHeartbeats 500000

noncomputable section

open scoped Manifold ContDiff Topology BigOperators
open MeasureTheory Set Topology Filter TopologicalSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0Space4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0CoreClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0FiniteMatrixProduct4D
open P0EFTJanusProgramPGlobalCandidateAGeometry4D
open P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameCorner4D
open P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameCornerAlgebra4D
open P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameCornerLocalRoot4D
open P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameSylvesterRegularity4D
open P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameSylvesterLocalRoot4D
open P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameSylvesterCornerLocalRoot4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCovariantAction4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev StrongScalar :=
  CanonicalPhysicalScalarStrongH1C0Core period hPeriod

private abbrev StrongFrameMatrix (frame : SmoothD8Frame period hPeriod) :=
  StrongFiniteMatrix period hPeriod frame.count

private abbrev physicalMeasure :=
  intrinsicCanonicalLorentzVolumeMeasure period hPeriod

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance effectiveQuotientMetrizableSpace :
    MetrizableSpace (EffectiveQuotient period hPeriod) :=
  Manifold.metrizableSpace coverModelWithCorners _

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance physicalMeasureFinite :
    IsFiniteMeasure (physicalMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

local instance strongCoreNormedAddCommGroup :
    NormedAddCommGroup (StrongScalar period hPeriod) :=
  (canonicalPhysicalScalarStrongH1C0CoreSubmodule
    period hPeriod).normedAddCommGroup

local instance strongCoreNormedSpace :
    NormedSpace Real (StrongScalar period hPeriod) :=
  inferInstance

local instance strongCoreCompleteSpace :
    CompleteSpace (StrongScalar period hPeriod) :=
  canonicalPhysicalScalarStrongH1C0CoreCompleteSpace period hPeriod

local instance strongFiniteFrameCornerNormedAddCommGroup
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    NormedAddCommGroup
      (StrongFiniteFrameCorner period hPeriod frame metric) :=
  (strongFiniteFrameCornerSubmodule
    period hPeriod frame metric).normedAddCommGroup

local instance strongFiniteFrameCornerNormedSpace
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (StrongFiniteFrameCorner period hPeriod frame metric) :=
  inferInstance

local instance strongFiniteFrameCornerCompleteSpaceInstance
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    CompleteSpace (StrongFiniteFrameCorner period hPeriod frame metric) :=
  strongFiniteFrameCornerCompleteSpace period hPeriod frame metric

/-- Intrinsic Sylvester regularity as an explicit stratum predicate, not an
extra field of the unqualified physical geometry. -/
def IsGlobalCandidateASylvesterRegular
    (geometry : GlobalCandidateAGeometry period hPeriod) : Prop :=
  ∀ point, Function.Bijective
    (intrinsicCandidateASylvesterAt period hPeriod geometry point)

/-- The honest regular stratum of general Candidate-A geometries. -/
abbrev GlobalCandidateASylvesterRegularGeometry :=
  { geometry : GlobalCandidateAGeometry period hPeriod //
    IsGlobalCandidateASylvesterRegular period hPeriod geometry }

/-- A local action chart stays in the intrinsic regular stratum at every
admissible parameter. -/
def IsGlobalCandidateALocalVariationalChartSylvesterRegular
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure) : Prop :=
  ∀ point (hPoint : point ∈ chart.family.domain),
    IsGlobalCandidateASylvesterRegular period hPeriod
      ((chart.family.datumAt point hPoint).1).geometry

/-- Intrinsic pointwise Sylvester regularity transports to bijectivity of the
strong Sylvester derivative on the complete projector corner. -/
theorem strongFiniteFrameCornerSylvester_bijective_of_intrinsic
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (frame : SmoothD8Frame period hPeriod)
    (hRegular : ∀ point, Function.Bijective
      (intrinsicCandidateASylvesterAt period hPeriod geometry point)) :
    Function.Bijective
      (strongFiniteFrameCornerSylvester
        period hPeriod frame geometry.plusMetric
        (strongGlobalCandidateAFiniteFrameRootCorner
          period hPeriod geometry frame)) := by
  let ambientEquiv := strongFiniteFrameExtendedSylvesterEquiv
    period hPeriod geometry frame hRegular
  let ambient := strongFiniteFrameExtendedSylvester
    period hPeriod geometry frame
  let corner := strongFiniteFrameCornerProjection
    period hPeriod frame geometry.plusMetric
  have hForward :
      (ambientEquiv : StrongFrameMatrix period hPeriod frame →L[Real]
        StrongFrameMatrix period hPeriod frame) = ambient :=
    strongFiniteFrameExtendedSylvesterEquiv_forward_eq
      period hPeriod geometry frame hRegular
  have hAmbientInjective : Function.Injective ambient := by
    intro first second hEqual
    apply ambientEquiv.injective
    have hFirst := congrArg (fun operator :
      StrongFrameMatrix period hPeriod frame →L[Real]
        StrongFrameMatrix period hPeriod frame => operator first) hForward
    have hSecond := congrArg (fun operator :
      StrongFrameMatrix period hPeriod frame →L[Real]
        StrongFrameMatrix period hPeriod frame => operator second) hForward
    exact hFirst.trans (hEqual.trans hSecond.symm)
  constructor
  · intro first second hEqual
    apply Subtype.ext
    apply hAmbientInjective
    have hFirst := strongFiniteFrameExtendedSylvester_corner
      period hPeriod geometry frame first
    have hSecond := strongFiniteFrameExtendedSylvester_corner
      period hPeriod geometry frame second
    exact hFirst.trans ((congrArg Subtype.val hEqual).trans hSecond.symm)
  · intro target
    obtain ⟨preimage, hPreimage⟩ := ambientEquiv.surjective target.1
    have hAtPreimage := congrArg (fun operator :
      StrongFrameMatrix period hPeriod frame →L[Real]
        StrongFrameMatrix period hPeriod frame => operator preimage) hForward
    have hAmbient : ambient preimage = target.1 :=
      hAtPreimage.symm.trans hPreimage
    have hTargetCorner : corner target.1 = target.1 :=
      (strongFiniteFrameCorner_mem_iff
        period hPeriod frame geometry.plusMetric target.1).mp target.2
    have hSameOutput : ambient (corner preimage) = ambient preimage := by
      calc
        ambient (corner preimage) = corner (ambient preimage) :=
          strongFiniteFrameExtendedSylvester_commutes_cornerProjection
            period hPeriod geometry frame preimage
        _ = corner target.1 := congrArg corner hAmbient
        _ = target.1 := hTargetCorner
        _ = ambient preimage := hAmbient.symm
    have hPreimageCorner : corner preimage = preimage :=
      hAmbientInjective hSameOutput
    have hPreimageMem : preimage ∈ strongFiniteFrameCornerSubmodule
        period hPeriod frame geometry.plusMetric :=
      (strongFiniteFrameCorner_mem_iff
        period hPeriod frame geometry.plusMetric preimage).mpr hPreimageCorner
    let source : StrongFiniteFrameCorner
        period hPeriod frame geometry.plusMetric :=
      ⟨preimage, hPreimageMem⟩
    refine ⟨source, ?_⟩
    apply Subtype.ext
    have hRestriction := strongFiniteFrameExtendedSylvester_corner
      period hPeriod geometry frame source
    exact hRestriction.symm.trans hAmbient

/-- Final regular-stratum bridge: intrinsic pointwise regularity yields both
the strong corner Sylvester equivalence and the existing open local `C²` root
germ. -/
theorem global_candidate_a_strong_finite_frame_sylvester_local_root_gate
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (frame : SmoothD8Frame period hPeriod)
    (hRegular : ∀ point, Function.Bijective
      (intrinsicCandidateASylvesterAt period hPeriod geometry point)) :
    Function.Bijective
        (strongFiniteFrameCornerSylvester
          period hPeriod frame geometry.plusMetric
          (strongGlobalCandidateAFiniteFrameRootCorner
            period hPeriod geometry frame)) ∧
      HasLocalC2InverseGerm
        (StrongFiniteFrameCorner period hPeriod frame geometry.plusMetric)
        (strongFiniteFrameCornerSquare
          period hPeriod frame geometry.plusMetric)
        (strongGlobalCandidateAFiniteFrameRootCorner
          period hPeriod geometry frame) := by
  have hStrong := strongFiniteFrameCornerSylvester_bijective_of_intrinsic
    period hPeriod geometry frame hRegular
  exact ⟨hStrong,
    global_candidate_a_strong_finite_frame_corner_local_root_gate
      period hPeriod geometry frame hStrong⟩

/-- Full regular-stratum bridge with a branch `C²` on the whole open
perturbation domain, rather than only at its center. -/
theorem global_candidate_a_strong_finite_frame_sylvester_contDiff_local_root_gate
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (frame : SmoothD8Frame period hPeriod)
    (hRegular : ∀ point, Function.Bijective
      (intrinsicCandidateASylvesterAt period hPeriod geometry point)) :
    Function.Bijective
        (strongFiniteFrameCornerSylvester
          period hPeriod frame geometry.plusMetric
          (strongGlobalCandidateAFiniteFrameRootCorner
            period hPeriod geometry frame)) ∧
      HasLocalC2InverseOpenBranch
        (StrongFiniteFrameCorner period hPeriod frame geometry.plusMetric)
        (strongFiniteFrameCornerSquare
          period hPeriod frame geometry.plusMetric)
        (strongGlobalCandidateAFiniteFrameRootCorner
          period hPeriod geometry frame) := by
  have hStrong := strongFiniteFrameCornerSylvester_bijective_of_intrinsic
    period hPeriod geometry frame hRegular
  exact ⟨hStrong,
    global_candidate_a_strong_finite_frame_corner_contDiff_local_root_gate
      period hPeriod geometry frame hStrong⟩

/-- On the explicit regular-geometry subtype, the full local-root conclusion
is unconditional. -/
theorem global_candidate_a_sylvester_regular_geometry_local_root_gate
    (geometry : GlobalCandidateASylvesterRegularGeometry period hPeriod)
    (frame : SmoothD8Frame period hPeriod) :
    Function.Bijective
        (strongFiniteFrameCornerSylvester
          period hPeriod frame geometry.1.plusMetric
          (strongGlobalCandidateAFiniteFrameRootCorner
            period hPeriod geometry.1 frame)) ∧
      HasLocalC2InverseOpenBranch
        (StrongFiniteFrameCorner period hPeriod frame geometry.1.plusMetric)
        (strongFiniteFrameCornerSquare
          period hPeriod frame geometry.1.plusMetric)
        (strongGlobalCandidateAFiniteFrameRootCorner
          period hPeriod geometry.1 frame) :=
  global_candidate_a_strong_finite_frame_sylvester_contDiff_local_root_gate
    period hPeriod geometry.1 frame geometry.2

/-- Every admissible point of an explicitly regular local variational chart
inherits the full strong-corner local-root branch. -/
theorem global_candidate_a_sylvester_regular_local_variational_chart_root_gate
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (hRegular : IsGlobalCandidateALocalVariationalChartSylvesterRegular
      period hPeriod chart)
    (point : chart.Model) (hPoint : point ∈ chart.family.domain)
    (frame : SmoothD8Frame period hPeriod) :
    let geometry := ((chart.family.datumAt point hPoint).1).geometry
    Function.Bijective
        (strongFiniteFrameCornerSylvester
          period hPeriod frame geometry.plusMetric
          (strongGlobalCandidateAFiniteFrameRootCorner
            period hPeriod geometry frame)) ∧
      HasLocalC2InverseOpenBranch
        (StrongFiniteFrameCorner period hPeriod frame geometry.plusMetric)
        (strongFiniteFrameCornerSquare
          period hPeriod frame geometry.plusMetric)
        (strongGlobalCandidateAFiniteFrameRootCorner
          period hPeriod geometry frame) := by
  dsimp only
  exact global_candidate_a_strong_finite_frame_sylvester_contDiff_local_root_gate
    period hPeriod ((chart.family.datumAt point hPoint).1).geometry frame
      (hRegular point hPoint)

end
end P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameSylvesterRegularStratumLocalRoot4D
end JanusFormal
