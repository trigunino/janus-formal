import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06WarpedNullCollarPhysicalMetricRegularity4D

/-!
# Physical face geometry of the warped-null collar

At a face point where Gate 1056's physical pullback metric agrees with the
warped metric, this gate identifies the selected pullback-coordinate data. The
generator is null, the screen metric is the induced physical metric, and an
explicit complementary null rigging is normalized by `g(N,k) = -1`.
Contracting the physical metric volume with that rigging and the oriented
face frame gives exactly the homogeneous screen area `exp u`.

The result is point-local and conditional on the existing incidence,
transition, and face-metric data.  Regional compatibility and existence of
those data remain separate obligations.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06WarpedNullCollarPhysicalFaceGeometry4D

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000

noncomputable section

open Filter Topology
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalProductEuler4D
open P0EFTJanusFiniteNullFaceMobileGeometricRealization4D
open P0EFTJanusProgramPT06AmbientNullFluxPullback4D
open P0EFTJanusProgramPT06AmbientSignedVectorPullbackPiola4D
open P0EFTJanusProgramPT06AmbientAbsoluteVectorPullbackPiola4D
open P0EFTJanusProgramPT06TrueCutCollarNormalAlignment4D
open P0EFTJanusProgramPT06ExplicitWarpedNullHyperplaneGeometry4D
open P0EFTJanusProgramPT06WarpedNullHyperplaneFluxRestriction4D
open P0EFTJanusProgramPT06ExplicitWarpedNullLinearCollar4D
open P0EFTJanusProgramPT06WarpedNullCollarOrientation4D
open P0EFTJanusProgramPT06LocalC3NullFaceCutCollarIncidence4D
open P0EFTJanusProgramPT06WarpedNullClosedHalfCollar4D
open P0EFTJanusProgramPT06WarpedNullMappingTorusFaceIncidence4D
open P0EFTJanusProgramPT06WarpedNullCollarChartTransition4D
open P0EFTJanusProgramPT06WarpedNullCollarFluxCovariance4D
open P0EFTJanusProgramPT06WarpedNullCollarMetricDivergenceNaturality4D
open P0EFTJanusProgramPT06WarpedNullCollarPhysicalMetricGerm4D
open P0EFTJanusProgramPT06WarpedNullCollarPhysicalMetricPullback4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- The complementary null rigging halfway between the coordinate rigging
`e₀` and the lower-collar outward vector `-e₃`. -/
def programPT06WarpedNullNormalizedNullRigging
    (source : ProgramPT06NullFaceSource3) :
    ProgramPT06AmbientCoordinate4 :=
  (2 : Real)⁻¹ •
    (programPT06WarpedNullHyperplaneRawTransverse source +
      programPT06WarpedNullCollarZeroBoundaryOutward)

@[simp] theorem programPT06WarpedNullNormalizedNullRigging_apply
    (source : ProgramPT06NullFaceSource3) :
    programPT06WarpedNullNormalizedNullRigging source =
      (EuclideanSpace.equiv (Fin 4) Real).symm
        ![(2 : Real)⁻¹, 0, 0, -(2 : Real)⁻¹] := by
  apply (EuclideanSpace.equiv (Fin 4) Real).injective
  funext index
  fin_cases index <;>
    simp [programPT06WarpedNullNormalizedNullRigging,
      programPT06WarpedNullHyperplaneRawTransverse,
      programPT06WarpedNullCollarZeroBoundaryOutward,
      programPT06AmbientCoordinateBasis]

/-- The normalized null rigging has the same positive unit face orientation
as the raw rigging and the lower-collar outward vector. -/
theorem programPT06WarpedNullNormalizedNullRigging_flux_eq_one
    (source : ProgramPT06NullFaceSource3) :
    programPT06AmbientSignedVolume.curryLeft
        (programPT06WarpedNullNormalizedNullRigging source)
        (programPT06FiniteNullFaceGeometricTangentFrame
          (programPT06ExplicitWarpedNullHyperplaneGeometry Unit)
          0 () source) = 1 := by
  unfold programPT06WarpedNullNormalizedNullRigging
  rw [map_smul, ContinuousAlternatingMap.smul_apply,
    map_add, ContinuousAlternatingMap.add_apply,
    programPT06WarpedNullHyperplaneRawTransverse_flux_eq_one,
    programPT06WarpedNullCollarZeroBoundaryOutward_flux_eq_one]
  norm_num

/-- Lower-face collar-factor vector transported to the cut-collar chart. -/
def programPT06WarpedNullTransportedLowerCollarOutward
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    (datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource) :
    ProgramPT06AmbientCoordinate4 :=
  programPT06WarpedNullCollarTransitionJacobian period hPeriod datum
    programPT06WarpedNullCollarZeroBoundaryOutward

/-- The transported lower-face vector is the negative of the positive
unit-speed collar-factor direction.  This is not a metric unit normal. -/
theorem programPT06WarpedNullTransportedLowerCollarOutward_eq_neg_trueCollarDirection
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    (datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource) :
    programPT06WarpedNullTransportedLowerCollarOutward period hPeriod datum =
      -programPT06TrueCutBulkChartUnitNormal period hPeriod incidence
        (programPT06LocalC3NullCollarMap period hPeriod incidence
          (programPT06WarpedNullZeroFace source)) := by
  rw [datum.trueCutBulkChartUnitNormal period hPeriod]
  simp [programPT06WarpedNullTransportedLowerCollarOutward,
    programPT06WarpedNullCollarZeroBoundaryOutward]

/-- Face tangent frame transported to the cut-collar chart. -/
def programPT06WarpedNullTransportedFaceTangentFrame
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    (datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource) :
    Fin 3 → ProgramPT06AmbientCoordinate4 :=
  fun direction =>
    programPT06WarpedNullCollarTransitionJacobian period hPeriod datum
      (programPT06FiniteNullFaceGeometricTangentFrame
        (programPT06ExplicitWarpedNullHyperplaneGeometry Unit)
        0 () source direction)

/-- Because the collar transition restricts to the identity on the warped
face germ, its Jacobian fixes all three face tangents. -/
theorem programPT06WarpedNullTransportedFaceTangentFrame_eq
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    (datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource) :
    programPT06WarpedNullTransportedFaceTangentFrame period hPeriod datum =
      programPT06FiniteNullFaceGeometricTangentFrame
        (programPT06ExplicitWarpedNullHyperplaneGeometry Unit)
        0 () source := by
  let embedding : ProgramPT06NullFaceSource3 →
      ProgramPT06AmbientCoordinate4 :=
    programPT06WarpedNullHyperplaneEmbedding
  have hEmbedding : DifferentiableAt Real embedding source :=
    programPT06WarpedNullHyperplaneEmbedding.differentiableAt
  have hTransition : DifferentiableAt Real datum.transition
      (embedding source) :=
    (datum.transition_isLocalDiffeomorphAt.mdifferentiableAt
      (by norm_num)).differentiableAt
  have hComposition :
      fderiv Real (datum.transition ∘ embedding) source =
        (fderiv Real datum.transition (embedding source)).comp
          (fderiv Real embedding source) :=
    fderiv_comp source hTransition hEmbedding
  have hGerm : datum.transition ∘ embedding =ᶠ[𝓝 source] embedding :=
    programPT06WarpedNullCollarTransition_warpedFace_eventuallyEq
      period hPeriod datum
  have hDerivative :
      (fderiv Real datum.transition (embedding source)).comp
          (fderiv Real embedding source) =
        fderiv Real embedding source := by
    rw [← hComposition, hGerm.fderiv_eq]
  have hJacobian :
      (programPT06WarpedNullCollarTransitionJacobian
          period hPeriod datum :
        ProgramPT06AmbientCoordinate4 →L[Real]
          ProgramPT06AmbientCoordinate4) =
        fderiv Real datum.transition (embedding source) := by
    rw [programPT06WarpedNullCollarTransitionJacobian_coe,
      mfderiv_eq_fderiv]
  have hGeometric :=
    programPT06FiniteNullFaceEmbeddingTangentFrame_eq_geometric
      (programPT06ExplicitWarpedNullHyperplaneGeometry Unit)
      (0 : FiniteNullFacePhysicalHilbert Unit) (Set.mem_univ _) () source
  funext direction
  have hApplied := DFunLike.congr_fun hDerivative
    (programPT06NullFaceSourceFrame direction)
  unfold programPT06WarpedNullTransportedFaceTangentFrame
  rw [← hGeometric]
  unfold programPT06NullFaceEmbeddingTangentFrame
  change
    ((programPT06WarpedNullCollarTransitionJacobian
        period hPeriod datum :
      ProgramPT06AmbientCoordinate4 →L[Real]
        ProgramPT06AmbientCoordinate4)
      (fderiv Real embedding source
        (programPT06NullFaceSourceFrame direction))) =
      fderiv Real embedding source
        (programPT06NullFaceSourceFrame direction)
  rw [hJacobian]
  simpa [ContinuousLinearMap.comp_apply] using hApplied

/-- The signed transition Jacobian is exactly the coordinate-volume flux of
the transported lower-face collar vector through the transported frame. -/
theorem programPT06WarpedNullTransportedLowerCollarOutward_flux_eq_signedJacobian
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    (datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource) :
    programPT06AmbientSignedVolume.curryLeft
        (programPT06WarpedNullTransportedLowerCollarOutward period hPeriod datum)
        (programPT06WarpedNullTransportedFaceTangentFrame
          period hPeriod datum) =
      programPT06WarpedNullCollarTransitionSignedJacobian
        period hPeriod datum := by
  let jacobian : ProgramPT06AmbientCoordinate4 →L[Real]
      ProgramPT06AmbientCoordinate4 :=
    programPT06WarpedNullCollarTransitionJacobian period hPeriod datum
  let tangentFrame :=
    programPT06FiniteNullFaceGeometricTangentFrame
      (programPT06ExplicitWarpedNullHyperplaneGeometry Unit)
      0 () source
  have hFrame :
      Matrix.vecCons
          (programPT06WarpedNullTransportedLowerCollarOutward period hPeriod datum)
          (programPT06WarpedNullTransportedFaceTangentFrame period hPeriod datum) =
        jacobian ∘ Matrix.vecCons
          programPT06WarpedNullCollarZeroBoundaryOutward tangentFrame := by
    funext direction
    refine Fin.cases ?_ (fun direction3 => ?_) direction
    · rfl
    · rfl
  have hDeterminant := congrArg
    (fun form : ProgramPT06AmbientCoordinate4 [⋀^Fin 4]→L[Real] Real =>
      form (Matrix.vecCons
        programPT06WarpedNullCollarZeroBoundaryOutward tangentFrame))
    (programPT06AmbientSignedTopForm_comp
      programPT06AmbientSignedVolume jacobian)
  change programPT06AmbientSignedVolume
      (Matrix.vecCons
        (programPT06WarpedNullTransportedLowerCollarOutward period hPeriod datum)
        (programPT06WarpedNullTransportedFaceTangentFrame period hPeriod datum)) = _
  rw [hFrame]
  change (programPT06AmbientSignedVolume.compContinuousLinearMap jacobian)
      (Matrix.vecCons
        programPT06WarpedNullCollarZeroBoundaryOutward tangentFrame) = _
  rw [hDeterminant]
  change LinearMap.det jacobian.toLinearMap *
      programPT06AmbientSignedVolume.curryLeft
        programPT06WarpedNullCollarZeroBoundaryOutward tangentFrame = _
  rw [programPT06WarpedNullCollarZeroBoundaryOutward_flux_eq_one, mul_one]
  rfl

/-- The signed Jacobian is the fixed-coordinate flux of the negative
unit-speed cut-collar direction through the face frame fixed by the
transition. -/
theorem programPT06WarpedNullCollarTransitionSignedJacobian_eq_trueLowerCollarFlux
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    (datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource) :
    programPT06WarpedNullCollarTransitionSignedJacobian
        period hPeriod datum =
      programPT06AmbientSignedVolume.curryLeft
        (-programPT06TrueCutBulkChartUnitNormal period hPeriod incidence
          (programPT06LocalC3NullCollarMap period hPeriod incidence
            (programPT06WarpedNullZeroFace source)))
        (programPT06FiniteNullFaceGeometricTangentFrame
          (programPT06ExplicitWarpedNullHyperplaneGeometry Unit)
          0 () source) := by
  rw [← programPT06WarpedNullTransportedLowerCollarOutward_eq_neg_trueCollarDirection
      period hPeriod datum,
    ← programPT06WarpedNullTransportedFaceTangentFrame_eq period hPeriod datum,
    programPT06WarpedNullTransportedLowerCollarOutward_flux_eq_signedJacobian]

/-- Positive transition orientation is equivalent to positive
coordinate-volume flux of the lower-face collar direction. -/
theorem programPT06WarpedNullCollarTransition_orientation_iff_trueLowerCollarFlux_pos
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    (datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource) :
    0 < programPT06WarpedNullCollarTransitionSignedJacobian
        period hPeriod datum ↔
      0 < programPT06AmbientSignedVolume.curryLeft
        (-programPT06TrueCutBulkChartUnitNormal period hPeriod incidence
          (programPT06LocalC3NullCollarMap period hPeriod incidence
            (programPT06WarpedNullZeroFace source)))
        (programPT06FiniteNullFaceGeometricTangentFrame
          (programPT06ExplicitWarpedNullHyperplaneGeometry Unit)
          0 () source) := by
  rw [programPT06WarpedNullCollarTransitionSignedJacobian_eq_trueLowerCollarFlux]

/-- A positive lower-collar coordinate flux discharges Gate 1051's signed
face-flux hypothesis.  The sign remains external orientation data. -/
theorem programPT06WarpedNullCollarTransitionAbsolute_fluxRestriction_eq_of_trueLowerCollarFlux
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    (datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource)
    (current : ProgramPT06AmbientCurrent4D)
    (hOutward : 0 < programPT06AmbientSignedVolume.curryLeft
      (-programPT06TrueCutBulkChartUnitNormal period hPeriod incidence
        (programPT06LocalC3NullCollarMap period hPeriod incidence
          (programPT06WarpedNullZeroFace source)))
      (programPT06FiniteNullFaceGeometricTangentFrame
        (programPT06ExplicitWarpedNullHyperplaneGeometry Unit)
        0 () source)) :
    programPT06WarpedNullHyperplaneFluxRestriction
        (programPT06WarpedNullCollarTransitionAbsolutePullbackCurrent
          period hPeriod datum current) source =
      programPT06WarpedNullHyperplaneFluxRestriction current source := by
  apply programPT06WarpedNullCollarTransitionAbsolute_fluxRestriction_eq
    period hPeriod datum current
  exact
    (programPT06WarpedNullCollarTransition_orientation_iff_trueLowerCollarFlux_pos
      period hPeriod datum).2 hOutward

/-- The physical collar metric makes the warped generator null at the
selected true face point. -/
theorem ProgramPT06WarpedNullCollarPhysicalMetricFaceDatum.generator_null
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    {datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource}
    (physical : ProgramPT06WarpedNullCollarPhysicalMetricFaceDatum
      period hPeriod datum) :
    finiteNullFaceAmbientMetricPairing
        (programPT06WarpedNullCollarPhysicalPullbackMetric
          period hPeriod datum physical.physicalMetric
          (programPT06WarpedNullHyperplaneEmbedding source))
        (programPT06WarpedNullHyperplaneGeneratorDifferential 1)
        (programPT06WarpedNullHyperplaneGeneratorDifferential 1) = 0 := by
  rw [physical.pullback_metric_face]
  simp [finiteNullFaceAmbientMetricPairing,
    programPT06WarpedNullHyperplaneAmbientMetric,
    programPT06WarpedNullHyperplaneAmbientWeight, Fin.sum_univ_four]

/-- The physical collar metric makes the generator orthogonal to both screen
directions at the selected face point. -/
theorem ProgramPT06WarpedNullCollarPhysicalMetricFaceDatum.generator_screen_orthogonal
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    {datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource}
    (physical : ProgramPT06WarpedNullCollarPhysicalMetricFaceDatum
      period hPeriod datum)
    (index : Fin 2) :
    finiteNullFaceAmbientMetricPairing
        (programPT06WarpedNullCollarPhysicalPullbackMetric
          period hPeriod datum physical.physicalMetric
          (programPT06WarpedNullHyperplaneEmbedding source))
        (programPT06WarpedNullHyperplaneGeneratorDifferential 1)
        (programPT06WarpedNullHyperplaneScreenDifferential
          (EuclideanSpace.single index 1)) = 0 := by
  rw [physical.pullback_metric_face]
  fin_cases index <;>
    simp [finiteNullFaceAmbientMetricPairing,
      programPT06WarpedNullHyperplaneAmbientMetric,
      programPT06WarpedNullHyperplaneAmbientWeight, Fin.sum_univ_four]

/-- The physical collar metric induces exactly the explicit positive screen
metric on the two screen directions. -/
theorem ProgramPT06WarpedNullCollarPhysicalMetricFaceDatum.inducedScreenMetric_eq_explicit
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    {datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource}
    (physical : ProgramPT06WarpedNullCollarPhysicalMetricFaceDatum
      period hPeriod datum)
    (first second : Fin 2) :
    finiteNullFaceInducedScreenMetricComponent
        (programPT06WarpedNullCollarPhysicalPullbackMetric
          period hPeriod datum physical.physicalMetric
          (programPT06WarpedNullHyperplaneEmbedding source))
        programPT06WarpedNullHyperplaneScreenDifferential first second =
      programPT06WarpedNullHyperplaneScreenMetric source.1 first second := by
  rw [physical.pullback_metric_face]
  fin_cases first <;> fin_cases second <;>
    simp [finiteNullFaceInducedScreenMetricComponent,
      finiteNullFaceAmbientMetricPairing,
      programPT06WarpedNullHyperplaneAmbientMetric,
      programPT06WarpedNullHyperplaneAmbientWeight,
      programPT06WarpedNullHyperplaneScreenMetric, Fin.sum_univ_four]

/-- The physically induced screen matrix has positive determinant and is
nondegenerate. -/
theorem ProgramPT06WarpedNullCollarPhysicalMetricFaceDatum.inducedScreenMetric_det_pos
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    {datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource}
    (physical : ProgramPT06WarpedNullCollarPhysicalMetricFaceDatum
      period hPeriod datum) :
    0 < Matrix.det
      (fun first second : Fin 2 =>
        finiteNullFaceInducedScreenMetricComponent
          (programPT06WarpedNullCollarPhysicalPullbackMetric
            period hPeriod datum physical.physicalMetric
            (programPT06WarpedNullHyperplaneEmbedding source))
          programPT06WarpedNullHyperplaneScreenDifferential first second) := by
  have hMatrix :
      (fun first second : Fin 2 =>
        finiteNullFaceInducedScreenMetricComponent
          (programPT06WarpedNullCollarPhysicalPullbackMetric
            period hPeriod datum physical.physicalMetric
            (programPT06WarpedNullHyperplaneEmbedding source))
          programPT06WarpedNullHyperplaneScreenDifferential first second) =
        programPT06WarpedNullHyperplaneScreenMetric source.1 := by
    funext first second
    exact
      ProgramPT06WarpedNullCollarPhysicalMetricFaceDatum.inducedScreenMetric_eq_explicit
        period hPeriod physical first second
  rw [hMatrix, programPT06WarpedNullHyperplaneScreenMetric_det]
  positivity

/-- The normalized rigging is null for the physical collar metric. -/
theorem ProgramPT06WarpedNullCollarPhysicalMetricFaceDatum.rigging_null
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    {datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource}
    (physical : ProgramPT06WarpedNullCollarPhysicalMetricFaceDatum
      period hPeriod datum) :
    finiteNullFaceAmbientMetricPairing
        (programPT06WarpedNullCollarPhysicalPullbackMetric
          period hPeriod datum physical.physicalMetric
          (programPT06WarpedNullHyperplaneEmbedding source))
        (programPT06WarpedNullNormalizedNullRigging source)
        (programPT06WarpedNullNormalizedNullRigging source) = 0 := by
  rw [physical.pullback_metric_face]
  simp [finiteNullFaceAmbientMetricPairing,
    programPT06WarpedNullHyperplaneAmbientMetric,
    programPT06WarpedNullHyperplaneAmbientWeight, Fin.sum_univ_four]

/-- The complementary null rigging has the canonical normalization
`g(N,k) = -1`. -/
theorem ProgramPT06WarpedNullCollarPhysicalMetricFaceDatum.rigging_generator
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    {datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource}
    (physical : ProgramPT06WarpedNullCollarPhysicalMetricFaceDatum
      period hPeriod datum) :
    finiteNullFaceAmbientMetricPairing
        (programPT06WarpedNullCollarPhysicalPullbackMetric
          period hPeriod datum physical.physicalMetric
          (programPT06WarpedNullHyperplaneEmbedding source))
        (programPT06WarpedNullNormalizedNullRigging source)
        (programPT06WarpedNullHyperplaneGeneratorDifferential 1) = -1 := by
  rw [physical.pullback_metric_face]
  simp [finiteNullFaceAmbientMetricPairing,
    programPT06WarpedNullHyperplaneAmbientMetric,
    programPT06WarpedNullHyperplaneAmbientWeight, Fin.sum_univ_four]
  norm_num

/-- The normalized rigging is physically orthogonal to both screen
directions. -/
theorem ProgramPT06WarpedNullCollarPhysicalMetricFaceDatum.rigging_screen_orthogonal
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    {datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource}
    (physical : ProgramPT06WarpedNullCollarPhysicalMetricFaceDatum
      period hPeriod datum)
    (index : Fin 2) :
    finiteNullFaceAmbientMetricPairing
        (programPT06WarpedNullCollarPhysicalPullbackMetric
          period hPeriod datum physical.physicalMetric
          (programPT06WarpedNullHyperplaneEmbedding source))
        (programPT06WarpedNullNormalizedNullRigging source)
        (programPT06WarpedNullHyperplaneScreenDifferential
          (EuclideanSpace.single index 1)) = 0 := by
  rw [physical.pullback_metric_face]
  fin_cases index <;>
    simp [finiteNullFaceAmbientMetricPairing,
      programPT06WarpedNullHyperplaneAmbientMetric,
      programPT06WarpedNullHyperplaneAmbientWeight, Fin.sum_univ_four]

/-- The oriented physical face density obtained by contracting the metric
volume with the normalized rigging. -/
def programPT06WarpedNullPhysicalFaceDensity
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    {datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource}
    (physical : ProgramPT06WarpedNullCollarPhysicalMetricFaceDatum
      period hPeriod datum) : Real :=
  programPT06AmbientMatrixMetricVolumeDensity
      (programPT06WarpedNullCollarPhysicalPullbackMetric
        period hPeriod datum physical.physicalMetric)
      (programPT06WarpedNullHyperplaneEmbedding source) *
    programPT06AmbientSignedVolume.curryLeft
      (programPT06WarpedNullNormalizedNullRigging source)
      (programPT06FiniteNullFaceGeometricTangentFrame
        (programPT06ExplicitWarpedNullHyperplaneGeometry Unit)
        0 () source)

/-- The physical face density is exactly the homogeneous screen area. -/
theorem ProgramPT06WarpedNullCollarPhysicalMetricFaceDatum.faceDensity_eq_screenArea
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    {datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource}
    (physical : ProgramPT06WarpedNullCollarPhysicalMetricFaceDatum
      period hPeriod datum) :
    programPT06WarpedNullPhysicalFaceDensity period hPeriod physical =
      finiteNullFaceHomogeneousScreenArea
        programPT06WarpedNullHyperplaneScreenMetric source.1 := by
  unfold programPT06WarpedNullPhysicalFaceDensity
  rw [programPT06WarpedNullNormalizedNullRigging_flux_eq_one,
    physical.volumeDensity_face_eq_screenArea, mul_one]

/-- The rigging-oriented pullback density is strictly positive in the warped
coordinate convention.  This does not choose the cut-collar transition sign. -/
theorem ProgramPT06WarpedNullCollarPhysicalMetricFaceDatum.faceDensity_pos
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    {datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource}
    (physical : ProgramPT06WarpedNullCollarPhysicalMetricFaceDatum
      period hPeriod datum) :
    0 < programPT06WarpedNullPhysicalFaceDensity period hPeriod physical := by
  rw [ProgramPT06WarpedNullCollarPhysicalMetricFaceDatum.faceDensity_eq_screenArea
    period hPeriod physical]
  simpa using Real.exp_pos source.1

/-- Point-local physical null-face geometry bundle. -/
theorem programPT06WarpedNullCollarPhysicalFaceGeometry_bundle
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    {datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource}
    (physical : ProgramPT06WarpedNullCollarPhysicalMetricFaceDatum
      period hPeriod datum) :
    finiteNullFaceAmbientMetricPairing
        (programPT06WarpedNullCollarPhysicalPullbackMetric
          period hPeriod datum physical.physicalMetric
          (programPT06WarpedNullHyperplaneEmbedding source))
        (programPT06WarpedNullHyperplaneGeneratorDifferential 1)
        (programPT06WarpedNullHyperplaneGeneratorDifferential 1) = 0 ∧
      (∀ index : Fin 2,
        finiteNullFaceAmbientMetricPairing
            (programPT06WarpedNullCollarPhysicalPullbackMetric
              period hPeriod datum physical.physicalMetric
              (programPT06WarpedNullHyperplaneEmbedding source))
            (programPT06WarpedNullHyperplaneGeneratorDifferential 1)
            (programPT06WarpedNullHyperplaneScreenDifferential
              (EuclideanSpace.single index 1)) = 0) ∧
      (∀ first second : Fin 2,
        finiteNullFaceInducedScreenMetricComponent
            (programPT06WarpedNullCollarPhysicalPullbackMetric
              period hPeriod datum physical.physicalMetric
              (programPT06WarpedNullHyperplaneEmbedding source))
            programPT06WarpedNullHyperplaneScreenDifferential first second =
          programPT06WarpedNullHyperplaneScreenMetric source.1 first second) ∧
      0 < Matrix.det
        (fun first second : Fin 2 =>
          finiteNullFaceInducedScreenMetricComponent
            (programPT06WarpedNullCollarPhysicalPullbackMetric
              period hPeriod datum physical.physicalMetric
              (programPT06WarpedNullHyperplaneEmbedding source))
            programPT06WarpedNullHyperplaneScreenDifferential first second) ∧
      finiteNullFaceAmbientMetricPairing
          (programPT06WarpedNullCollarPhysicalPullbackMetric
            period hPeriod datum physical.physicalMetric
            (programPT06WarpedNullHyperplaneEmbedding source))
          (programPT06WarpedNullNormalizedNullRigging source)
          (programPT06WarpedNullNormalizedNullRigging source) = 0 ∧
      finiteNullFaceAmbientMetricPairing
          (programPT06WarpedNullCollarPhysicalPullbackMetric
            period hPeriod datum physical.physicalMetric
            (programPT06WarpedNullHyperplaneEmbedding source))
          (programPT06WarpedNullNormalizedNullRigging source)
          (programPT06WarpedNullHyperplaneGeneratorDifferential 1) = -1 ∧
      (∀ index : Fin 2,
        finiteNullFaceAmbientMetricPairing
            (programPT06WarpedNullCollarPhysicalPullbackMetric
              period hPeriod datum physical.physicalMetric
              (programPT06WarpedNullHyperplaneEmbedding source))
            (programPT06WarpedNullNormalizedNullRigging source)
            (programPT06WarpedNullHyperplaneScreenDifferential
              (EuclideanSpace.single index 1)) = 0) ∧
      programPT06WarpedNullPhysicalFaceDensity period hPeriod physical =
        finiteNullFaceHomogeneousScreenArea
          programPT06WarpedNullHyperplaneScreenMetric source.1 ∧
      0 < programPT06WarpedNullPhysicalFaceDensity period hPeriod physical := by
  exact ⟨ProgramPT06WarpedNullCollarPhysicalMetricFaceDatum.generator_null
      period hPeriod physical,
    ProgramPT06WarpedNullCollarPhysicalMetricFaceDatum.generator_screen_orthogonal
      period hPeriod physical,
    ProgramPT06WarpedNullCollarPhysicalMetricFaceDatum.inducedScreenMetric_eq_explicit
      period hPeriod physical,
    ProgramPT06WarpedNullCollarPhysicalMetricFaceDatum.inducedScreenMetric_det_pos
      period hPeriod physical,
    ProgramPT06WarpedNullCollarPhysicalMetricFaceDatum.rigging_null
      period hPeriod physical,
    ProgramPT06WarpedNullCollarPhysicalMetricFaceDatum.rigging_generator
      period hPeriod physical,
    ProgramPT06WarpedNullCollarPhysicalMetricFaceDatum.rigging_screen_orthogonal
      period hPeriod physical,
    ProgramPT06WarpedNullCollarPhysicalMetricFaceDatum.faceDensity_eq_screenArea
      period hPeriod physical,
    ProgramPT06WarpedNullCollarPhysicalMetricFaceDatum.faceDensity_pos
      period hPeriod physical⟩

end
end P0EFTJanusProgramPT06WarpedNullCollarPhysicalFaceGeometry4D
end JanusFormal
