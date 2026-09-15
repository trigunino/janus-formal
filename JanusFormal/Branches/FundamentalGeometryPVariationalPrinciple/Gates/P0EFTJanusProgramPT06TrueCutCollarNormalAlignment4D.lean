import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06LocalC3NullFaceCutCollarIncidence4D

/-!
# True cut-collar normal alignment

This gate isolates the remaining first-jet compatibility between the genuine
`[0,1]` collar normal and Gate 1033's chosen ambient transverse direction.
The unit tangent used here is certified by the derivative of the actual
subtype inclusion `[0,1] → ℝ`.  A conditional alignment datum then says
that the `C³` chart representative of Gate 1034 maps this tangent to the fixed
pure-transverse ambient vector.

Under that condition, Gate 1033's normal-constant current has zero derivative
along the genuine collar normal, while its affine current realizes exactly
the prescribed transverse slope.  These remain coordinate-current statements;
the alignment fixes scale and orientation, not only the normal line.  No metric,
volume, conormal or invariant-divergence transport is asserted, and the actual
zero face is not proved to have zero transverse coordinate in the chosen split.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06TrueCutCollarNormalAlignment4D

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCutThroatBoundaryDoubleCover4D
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusCutThroatSmoothFiniteCollar4D
open P0EFTJanusMappingTorusCutCollarNormalDerivativeIsomorphism4D
open P0EFTJanusMappingTorusCutBulkFiniteCollarAmbientDerivativeIsomorphism4D
open P0EFTJanusMappingTorusHolonomicCoordinateEquiv4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalProductEuler4D
open P0EFTJanusFiniteNullFaceMobileGeometricRealization4D
open P0EFTJanusProgramPT06AmbientNullFluxPullback4D
open P0EFTJanusProgramPT06ThroatSignedDifferentialFormPiola4D
open P0EFTJanusProgramPT06RadialAmbientCurrentExtension4D
open P0EFTJanusProgramPT06RegularRadialProductCollarDivergence4D
open P0EFTJanusProgramPT06LocalC3NullFaceCutCollarIncidence4D

variable (period : Real) (hPeriod : period ≠ 0)

local instance boundaryChartedSpace :
    ChartedSpace ThroatCoverModel (CutThroatBoundary period hPeriod) :=
  cutThroatBoundaryChartedSpace period hPeriod

local instance finiteCollarChartedSpace :
    ChartedSpace CutCollarModel (CutThroatFiniteCollar period hPeriod) :=
  cutThroatFiniteCollarChartedSpace period hPeriod

local instance effectiveBulkChartedSpace :
    ChartedSpace CoverModel (ProgramPT06EffectiveBulk period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveBulkIsManifold :
    IsManifold coverModelWithCorners ω
      (ProgramPT06EffectiveBulk period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- Positive unit speed in the actual collar interval, with zero source-face
component. -/
def programPT06LocalC3NullCollarUnitNormal
    (parameter : ProgramPT06NullFaceFiniteCollar) :
    TangentSpace programPT06NullFaceCollarModelWithCorners parameter :=
  (0, (cutCollarNormalDerivativeEquiv parameter.2).symm 1)

/-- The second component of the chosen tangent has unit derivative under the
actual inclusion `[0,1] → ℝ`, including at both endpoints. -/
theorem programPT06LocalC3NullCollarUnitNormal_intervalDerivative
    (parameter : ProgramPT06NullFaceFiniteCollar) :
    cutCollarNormalDerivativeEquiv parameter.2
        (programPT06LocalC3NullCollarUnitNormal parameter).2 = 1 := by
  exact (cutCollarNormalDerivativeEquiv parameter.2).apply_symm_apply 1

theorem programPT06LocalC3NullCollarUnitNormal_ne_zero
    (parameter : ProgramPT06NullFaceFiniteCollar) :
    programPT06LocalC3NullCollarUnitNormal parameter ≠ 0 := by
  intro hZero
  have hSecond :
      (cutCollarNormalDerivativeEquiv parameter.2).symm 1 = 0 := by
    exact congrArg Prod.snd hZero
  have hUnit := congrArg (cutCollarNormalDerivativeEquiv parameter.2) hSecond
  have hUnit' : (1 : TangentSpace
      (modelWithCornersSelf Real Real) parameter.2.1) = 0 := by
    simpa using hUnit
  change (1 : Real) = 0 at hUnit'
  exact one_ne_zero hUnit'

/-- Positive unit speed in the normal factor of the genuine finite cut
collar. -/
def programPT06CutCollarUnitNormal
    (parameter : CutThroatFiniteCollar period hPeriod) :
    TangentSpace cutCollarModelWithCorners parameter :=
  (0, (cutCollarNormalDerivativeEquiv parameter.2).symm 1)

theorem programPT06CutCollarUnitNormal_intervalDerivative
    (parameter : CutThroatFiniteCollar period hPeriod) :
    cutCollarNormalDerivativeEquiv parameter.2
        (programPT06CutCollarUnitNormal period hPeriod parameter).2 = 1 := by
  exact (cutCollarNormalDerivativeEquiv parameter.2).apply_symm_apply 1

theorem programPT06CutCollarUnitNormal_ne_zero
    (parameter : CutThroatFiniteCollar period hPeriod) :
    programPT06CutCollarUnitNormal period hPeriod parameter ≠ 0 := by
  intro hZero
  have hSecond :
      (cutCollarNormalDerivativeEquiv parameter.2).symm 1 = 0 := by
    exact congrArg Prod.snd hZero
  have hUnit := congrArg (cutCollarNormalDerivativeEquiv parameter.2) hSecond
  have hUnit' : (1 : TangentSpace
      (modelWithCornersSelf Real Real) parameter.2.1) = 0 := by
    simpa using hUnit
  change (1 : Real) = 0 at hUnit'
  exact one_ne_zero hUnit'

/-- The genuine collar normal transported into the effective bulk. -/
def programPT06TrueCutBulkUnitNormal
    (parameter : CutThroatFiniteCollar period hPeriod) :
    TangentSpace coverModelWithCorners
      (cutBulkFiniteCollarToAmbient period hPeriod parameter) :=
  mfderiv cutCollarModelWithCorners coverModelWithCorners
    (cutBulkFiniteCollarToAmbient period hPeriod) parameter
    (programPT06CutCollarUnitNormal period hPeriod parameter)

theorem programPT06TrueCutBulkUnitNormal_ne_zero
    (parameter : CutThroatFiniteCollar period hPeriod) :
    programPT06TrueCutBulkUnitNormal period hPeriod parameter ≠ 0 := by
  obtain ⟨derivative, hDerivative⟩ :=
    cutBulkFiniteCollarToAmbient_derivative_isomorphism
      period hPeriod parameter
  intro hZero
  have hImageZero :
      derivative (programPT06CutCollarUnitNormal
        period hPeriod parameter) = 0 := by
    calc
      _ = mfderiv cutCollarModelWithCorners coverModelWithCorners
          (cutBulkFiniteCollarToAmbient period hPeriod) parameter
          (programPT06CutCollarUnitNormal period hPeriod parameter) :=
        DFunLike.congr_fun hDerivative _
      _ = 0 := by
        simpa [programPT06TrueCutBulkUnitNormal] using hZero
  apply programPT06CutCollarUnitNormal_ne_zero period hPeriod parameter
  exact derivative.injective (by simpa using hImageZero)

/-- The genuine bulk normal expressed in the selected ambient chart. -/
def programPT06TrueCutBulkChartUnitNormal
    {NullFace : Type*} [Fintype NullFace]
    {geometry : FiniteNullFaceMobileGeometricDatum NullFace}
    {input : FiniteNullFacePhysicalHilbert NullFace} {face : NullFace}
    (datum : ProgramPT06LocalC3NullIncidenceDatum
      period hPeriod geometry input face)
    (parameter : CutThroatFiniteCollar period hPeriod) :
    ProgramPT06AmbientCoordinate4 :=
  mfderiv coverModelWithCorners
    (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
    (programPT06EffectiveBulkChartCoordinate
      period hPeriod datum.chartAnchor)
    (cutBulkFiniteCollarToAmbient period hPeriod parameter)
    (programPT06TrueCutBulkUnitNormal period hPeriod parameter)

theorem programPT06LocalC3NullChartCoordinate_mdifferentiableAt
    {NullFace : Type*} [Fintype NullFace]
    {geometry : FiniteNullFaceMobileGeometricDatum NullFace}
    {input : FiniteNullFacePhysicalHilbert NullFace} {face : NullFace}
    (datum : ProgramPT06LocalC3NullIncidenceDatum
      period hPeriod geometry input face)
    (parameter : ProgramPT06NullFaceFiniteCollar)
    (hParameter : parameter ∈
      programPT06LocalC3NullCollarDomain period hPeriod datum) :
    MDifferentiableAt programPT06NullFaceCollarModelWithCorners
      (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
      (programPT06LocalC3NullChartCoordinate period hPeriod datum)
      parameter := by
  have hAt := (programPT06LocalC3NullChartCoordinate_contMDiffOn
    period hPeriod datum).contMDiffAt
      ((programPT06LocalC3NullCollarDomain_isOpen
        period hPeriod datum).mem_nhds hParameter)
  exact hAt.mdifferentiableAt (by norm_num)

theorem programPT06LocalC3NullCollarMap_unitNormal_mfderiv
    {NullFace : Type*} [Fintype NullFace]
    {geometry : FiniteNullFaceMobileGeometricDatum NullFace}
    {input : FiniteNullFacePhysicalHilbert NullFace} {face : NullFace}
    (datum : ProgramPT06LocalC3NullIncidenceDatum
      period hPeriod geometry input face)
    (parameter : ProgramPT06NullFaceFiniteCollar)
    (hParameter : parameter ∈
      programPT06LocalC3NullCollarDomain period hPeriod datum) :
    mfderiv programPT06NullFaceCollarModelWithCorners
        cutCollarModelWithCorners
        (programPT06LocalC3NullCollarMap period hPeriod datum)
        parameter (programPT06LocalC3NullCollarUnitNormal parameter) =
      programPT06CutCollarUnitNormal period hPeriod
        (programPT06LocalC3NullCollarMap
          period hPeriod datum parameter) := by
  have hBoundary : MDifferentiableAt
      (modelWithCornersSelf Real ProgramPT06NullFaceSource3)
      throatCoverModelWithCorners datum.boundaryMap parameter.1 :=
    ((datum.boundaryMap_contMDiffOn parameter.1 hParameter.1).contMDiffAt
      (datum.sourceDomain_isOpen.mem_nhds hParameter.1)).mdifferentiableAt
        (by norm_num)
  change mfderiv programPT06NullFaceCollarModelWithCorners
      cutCollarModelWithCorners
      (Prod.map datum.boundaryMap (id : CutCollarInterval → CutCollarInterval))
      parameter
      (0, (cutCollarNormalDerivativeEquiv parameter.2).symm 1) =
    (0, (cutCollarNormalDerivativeEquiv parameter.2).symm 1)
  rw [mfderiv_prodMap hBoundary mdifferentiableAt_id, mfderiv_id]
  change
    (mfderiv (modelWithCornersSelf Real ProgramPT06NullFaceSource3)
        throatCoverModelWithCorners datum.boundaryMap parameter.1 0,
      (cutCollarNormalDerivativeEquiv parameter.2).symm 1) =
    (0, (cutCollarNormalDerivativeEquiv parameter.2).symm 1)
  rw [map_zero]

theorem programPT06LocalC3NullAmbientMap_unitNormal_mfderiv
    {NullFace : Type*} [Fintype NullFace]
    {geometry : FiniteNullFaceMobileGeometricDatum NullFace}
    {input : FiniteNullFacePhysicalHilbert NullFace} {face : NullFace}
    (datum : ProgramPT06LocalC3NullIncidenceDatum
      period hPeriod geometry input face)
    (parameter : ProgramPT06NullFaceFiniteCollar)
    (hParameter : parameter ∈
      programPT06LocalC3NullCollarDomain period hPeriod datum) :
    mfderiv programPT06NullFaceCollarModelWithCorners coverModelWithCorners
        (programPT06LocalC3NullAmbientMap period hPeriod datum) parameter
        (programPT06LocalC3NullCollarUnitNormal parameter) =
      programPT06TrueCutBulkUnitNormal period hPeriod
        (programPT06LocalC3NullCollarMap
          period hPeriod datum parameter) := by
  have hCollar : MDifferentiableAt
      programPT06NullFaceCollarModelWithCorners cutCollarModelWithCorners
      (programPT06LocalC3NullCollarMap period hPeriod datum) parameter :=
    ((programPT06LocalC3NullCollarMap_contMDiffOn
      period hPeriod datum).contMDiffAt
        ((programPT06LocalC3NullCollarDomain_isOpen
          period hPeriod datum).mem_nhds hParameter)).mdifferentiableAt
      (by norm_num)
  have hBulk : MDifferentiableAt cutCollarModelWithCorners
      coverModelWithCorners (cutBulkFiniteCollarToAmbient period hPeriod)
      (programPT06LocalC3NullCollarMap
        period hPeriod datum parameter) :=
    (cutBulkFiniteCollarToAmbient_contMDiff
      period hPeriod).mdifferentiableAt (by simp)
  change mfderiv programPT06NullFaceCollarModelWithCorners
      coverModelWithCorners
      (cutBulkFiniteCollarToAmbient period hPeriod ∘
        programPT06LocalC3NullCollarMap period hPeriod datum)
      parameter (programPT06LocalC3NullCollarUnitNormal parameter) = _
  calc
    _ = mfderiv cutCollarModelWithCorners coverModelWithCorners
          (cutBulkFiniteCollarToAmbient period hPeriod)
          (programPT06LocalC3NullCollarMap
            period hPeriod datum parameter)
          (mfderiv programPT06NullFaceCollarModelWithCorners
            cutCollarModelWithCorners
            (programPT06LocalC3NullCollarMap period hPeriod datum)
            parameter
            (programPT06LocalC3NullCollarUnitNormal parameter)) :=
      mfderiv_comp_apply parameter hBulk hCollar
        (programPT06LocalC3NullCollarUnitNormal parameter)
    _ = _ := by
      rw [programPT06LocalC3NullCollarMap_unitNormal_mfderiv
        period hPeriod datum parameter hParameter]
      rfl

theorem programPT06EffectiveBulkChartCoordinate_mdifferentiableAt
    (anchor point : ProgramPT06EffectiveBulk period hPeriod)
    (hPoint : point ∈ (chartAt CoverModel anchor).source) :
    MDifferentiableAt coverModelWithCorners
      (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
      (programPT06EffectiveBulkChartCoordinate period hPeriod anchor)
      point := by
  have hChart : ContMDiffOn coverModelWithCorners
      (modelWithCornersSelf Real CoverCoordinates) 3
      (extChartAt coverModelWithCorners anchor)
      (chartAt CoverModel anchor).source :=
    contMDiffOn_extChartAt
  have hCoordinate : ContMDiffOn coverModelWithCorners
      (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4) 3
      (programPT06EffectiveBulkChartCoordinate period hPeriod anchor)
      (chartAt CoverModel anchor).source :=
    programPT06AmbientHolonomicEquiv.symm.contDiff.contMDiff.comp_contMDiffOn
      (holonomicCoordinateEquiv.contDiff.contMDiff.comp_contMDiffOn hChart)
  exact ((hCoordinate point hPoint).contMDiffAt
    ((chartAt CoverModel anchor).open_source.mem_nhds hPoint))
      |>.mdifferentiableAt (by norm_num)

theorem programPT06LocalC3NullChartCoordinate_unitNormal_mfderiv_eq_trueCutBulkChartUnitNormal
    {NullFace : Type*} [Fintype NullFace]
    {geometry : FiniteNullFaceMobileGeometricDatum NullFace}
    {input : FiniteNullFacePhysicalHilbert NullFace} {face : NullFace}
    (datum : ProgramPT06LocalC3NullIncidenceDatum
      period hPeriod geometry input face)
    (parameter : ProgramPT06NullFaceFiniteCollar)
    (hParameter : parameter ∈
      programPT06LocalC3NullCollarDomain period hPeriod datum) :
    mfderiv programPT06NullFaceCollarModelWithCorners
        (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
        (programPT06LocalC3NullChartCoordinate period hPeriod datum) parameter
        (programPT06LocalC3NullCollarUnitNormal parameter) =
      programPT06TrueCutBulkChartUnitNormal period hPeriod datum
        (programPT06LocalC3NullCollarMap
          period hPeriod datum parameter) := by
  have hAmbient : MDifferentiableAt
      programPT06NullFaceCollarModelWithCorners coverModelWithCorners
      (programPT06LocalC3NullAmbientMap period hPeriod datum) parameter :=
    ((programPT06LocalC3NullAmbientMap_contMDiffOn
      period hPeriod datum).contMDiffAt
        ((programPT06LocalC3NullCollarDomain_isOpen
          period hPeriod datum).mem_nhds hParameter)).mdifferentiableAt
      (by norm_num)
  have hImage :
      programPT06LocalC3NullAmbientMap period hPeriod datum parameter ∈
        (chartAt CoverModel datum.chartAnchor).source := by
    simpa [programPT06LocalC3NullAmbientMap,
      programPT06LocalC3NullCollarMap] using
      datum.collar_image_mem_chart parameter.1 hParameter.1 parameter.2
  have hCoordinate :=
    programPT06EffectiveBulkChartCoordinate_mdifferentiableAt
      period hPeriod datum.chartAnchor
        (programPT06LocalC3NullAmbientMap period hPeriod datum parameter)
        hImage
  change mfderiv programPT06NullFaceCollarModelWithCorners
      (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
      (programPT06EffectiveBulkChartCoordinate
        period hPeriod datum.chartAnchor ∘
          programPT06LocalC3NullAmbientMap period hPeriod datum)
      parameter (programPT06LocalC3NullCollarUnitNormal parameter) = _
  calc
    _ = mfderiv coverModelWithCorners
          (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
          (programPT06EffectiveBulkChartCoordinate
            period hPeriod datum.chartAnchor)
          (programPT06LocalC3NullAmbientMap period hPeriod datum parameter)
          (mfderiv programPT06NullFaceCollarModelWithCorners
            coverModelWithCorners
            (programPT06LocalC3NullAmbientMap period hPeriod datum)
            parameter
            (programPT06LocalC3NullCollarUnitNormal parameter)) :=
      mfderiv_comp_apply parameter hCoordinate hAmbient
        (programPT06LocalC3NullCollarUnitNormal parameter)
    _ = _ := by
      rw [programPT06LocalC3NullAmbientMap_unitNormal_mfderiv
        period hPeriod datum parameter hParameter]
      rfl

/-- Exact scale-and-orientation compatibility of the genuine collar normal
with the fixed ambient split used by Gates 1032--1033, on the selected collar
patch. -/
structure ProgramPT06TrueCutCollarNormalAlignmentDatum
    {NullFace : Type*} [Fintype NullFace]
    {geometry : FiniteNullFaceMobileGeometricDatum NullFace}
    {input : FiniteNullFacePhysicalHilbert NullFace} {face : NullFace}
    (incidence : ProgramPT06LocalC3NullIncidenceDatum
      period hPeriod geometry input face) where
  true_chart_normal : ∀ parameter,
    parameter ∈ programPT06LocalC3NullCollarDomain
        period hPeriod incidence →
      programPT06TrueCutBulkChartUnitNormal period hPeriod incidence
          (programPT06LocalC3NullCollarMap
            period hPeriod incidence parameter) =
        programPT06PureTransverseEmbedding 1

theorem ProgramPT06TrueCutCollarNormalAlignmentDatum.coordinate_normal
    {NullFace : Type*} [Fintype NullFace]
    {geometry : FiniteNullFaceMobileGeometricDatum NullFace}
    {input : FiniteNullFacePhysicalHilbert NullFace} {face : NullFace}
    {incidence : ProgramPT06LocalC3NullIncidenceDatum
      period hPeriod geometry input face}
    (alignment : ProgramPT06TrueCutCollarNormalAlignmentDatum
      period hPeriod incidence)
    (parameter : ProgramPT06NullFaceFiniteCollar)
    (hParameter : parameter ∈
      programPT06LocalC3NullCollarDomain period hPeriod incidence) :
    mfderiv programPT06NullFaceCollarModelWithCorners
        (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
        (programPT06LocalC3NullChartCoordinate period hPeriod incidence)
        parameter (programPT06LocalC3NullCollarUnitNormal parameter) =
      programPT06PureTransverseEmbedding 1 := by
  rw [programPT06LocalC3NullChartCoordinate_unitNormal_mfderiv_eq_trueCutBulkChartUnitNormal
    period hPeriod incidence parameter hParameter]
  exact alignment.true_chart_normal parameter hParameter

theorem ProgramPT06TrueCutCollarNormalAlignmentDatum.throatProjection_zero
    {NullFace : Type*} [Fintype NullFace]
    {geometry : FiniteNullFaceMobileGeometricDatum NullFace}
    {input : FiniteNullFacePhysicalHilbert NullFace} {face : NullFace}
    {incidence : ProgramPT06LocalC3NullIncidenceDatum
      period hPeriod geometry input face}
    (alignment : ProgramPT06TrueCutCollarNormalAlignmentDatum
      period hPeriod incidence)
    (parameter : ProgramPT06NullFaceFiniteCollar)
    (hParameter : parameter ∈
      programPT06LocalC3NullCollarDomain period hPeriod incidence) :
    programPT06AmbientThroatProjection
        (mfderiv programPT06NullFaceCollarModelWithCorners
          (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
          (programPT06LocalC3NullChartCoordinate period hPeriod incidence)
          parameter
          (programPT06LocalC3NullCollarUnitNormal parameter)) = 0 := by
  rw [ProgramPT06TrueCutCollarNormalAlignmentDatum.coordinate_normal
    period hPeriod alignment parameter hParameter]
  exact programPT06AmbientThroatProjection_pureTransverse 1

theorem ProgramPT06TrueCutCollarNormalAlignmentDatum.transverseProjection_one
    {NullFace : Type*} [Fintype NullFace]
    {geometry : FiniteNullFaceMobileGeometricDatum NullFace}
    {input : FiniteNullFacePhysicalHilbert NullFace} {face : NullFace}
    {incidence : ProgramPT06LocalC3NullIncidenceDatum
      period hPeriod geometry input face}
    (alignment : ProgramPT06TrueCutCollarNormalAlignmentDatum
      period hPeriod incidence)
    (parameter : ProgramPT06NullFaceFiniteCollar)
    (hParameter : parameter ∈
      programPT06LocalC3NullCollarDomain period hPeriod incidence) :
    programPT06AmbientTransverseProjection
        (mfderiv programPT06NullFaceCollarModelWithCorners
          (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
          (programPT06LocalC3NullChartCoordinate period hPeriod incidence)
          parameter
          (programPT06LocalC3NullCollarUnitNormal parameter)) = 1 := by
  rw [ProgramPT06TrueCutCollarNormalAlignmentDatum.coordinate_normal
    period hPeriod alignment parameter hParameter]
  exact programPT06AmbientTransverseProjection_pureTransverse 1

/-- Gate 1033's affine current evaluated along the selected true-collar
coordinate representative. -/
def programPT06LocalC3AffineRadialCurrent
    {NullFace : Type*} [Fintype NullFace]
    {geometry : FiniteNullFaceMobileGeometricDatum NullFace}
    {input : FiniteNullFacePhysicalHilbert NullFace} {face : NullFace}
    (incidence : ProgramPT06LocalC3NullIncidenceDatum
      period hPeriod geometry input face)
    (throatCurrent : ThroatCoverCoordinates → ThroatCoverCoordinates)
    (normalDensity : ThroatCoverCoordinates → Real)
    (normalSlope : Real) :
    ProgramPT06NullFaceFiniteCollar → ProgramPT06AmbientCoordinate4 :=
  programPT06LocalC3NullCurrent period hPeriod incidence
    (programPT06AffineAmbientCollarCurrent
      throatCurrent normalDensity normalSlope)

/-- Gate 1033's coordinate-divergence identity evaluated on the actual zero
face supplied by Gate 1034. -/
theorem programPT06RegularAmbientCollarCurrent_divergence_at_localC3_face
    {NullFace : Type*} [Fintype NullFace]
    {geometry : FiniteNullFaceMobileGeometricDatum NullFace}
    {input : FiniteNullFacePhysicalHilbert NullFace} {face : NullFace}
    (incidence : ProgramPT06LocalC3NullIncidenceDatum
      period hPeriod geometry input face)
    {throatCurrent : ThroatCoverCoordinates → ThroatCoverCoordinates}
    {normalDensity : ThroatCoverCoordinates → Real}
    (source : ProgramPT06NullFaceSource3)
    (hSource : source ∈ incidence.sourceDomain)
    (hThroat : DifferentiableAt Real throatCurrent
      (programPT06AmbientThroatProjection
        (geometry.embedding input face source)))
    (hNormal : DifferentiableAt Real normalDensity
      (programPT06AmbientThroatProjection
        (geometry.embedding input face source))) :
    programPT06AmbientCoordinateDivergence
        (programPT06RegularAmbientCollarCurrent
          throatCurrent normalDensity)
        (programPT06LocalC3NullChartCoordinate period hPeriod incidence
          (source, (⊥ : CutCollarInterval))) =
      programPT06ThroatCoordinateDivergence throatCurrent
        (programPT06AmbientThroatProjection
          (geometry.embedding input face source)) := by
  rw [programPT06LocalC3NullChartCoordinate_face
    period hPeriod incidence source hSource]
  exact programPT06RegularAmbientCollarCurrent_divergence hThroat hNormal

/-- The affine normal slope contributes additively to coordinate divergence
on the same actual zero face. -/
theorem programPT06AffineAmbientCollarCurrent_divergence_at_localC3_face
    {NullFace : Type*} [Fintype NullFace]
    {geometry : FiniteNullFaceMobileGeometricDatum NullFace}
    {input : FiniteNullFacePhysicalHilbert NullFace} {face : NullFace}
    (incidence : ProgramPT06LocalC3NullIncidenceDatum
      period hPeriod geometry input face)
    {throatCurrent : ThroatCoverCoordinates → ThroatCoverCoordinates}
    {normalDensity : ThroatCoverCoordinates → Real}
    {normalSlope : Real}
    (source : ProgramPT06NullFaceSource3)
    (hSource : source ∈ incidence.sourceDomain)
    (hThroat : DifferentiableAt Real throatCurrent
      (programPT06AmbientThroatProjection
        (geometry.embedding input face source)))
    (hNormal : DifferentiableAt Real normalDensity
      (programPT06AmbientThroatProjection
        (geometry.embedding input face source))) :
    programPT06AmbientCoordinateDivergence
        (programPT06AffineAmbientCollarCurrent
          throatCurrent normalDensity normalSlope)
        (programPT06LocalC3NullChartCoordinate period hPeriod incidence
          (source, (⊥ : CutCollarInterval))) =
      programPT06ThroatCoordinateDivergence throatCurrent
          (programPT06AmbientThroatProjection
            (geometry.embedding input face source)) + normalSlope := by
  rw [programPT06LocalC3NullChartCoordinate_face
    period hPeriod incidence source hSource]
  exact programPT06AffineAmbientCollarCurrent_divergence hThroat hNormal

/-- The normal-constant Gate-1033 current has zero first derivative along the
actual unit collar normal whenever the coordinate normal is aligned. -/
theorem programPT06LocalC3RegularRadialCurrent_normal_mfderiv_zero
    {NullFace : Type*} [Fintype NullFace]
    {geometry : FiniteNullFaceMobileGeometricDatum NullFace}
    {input : FiniteNullFacePhysicalHilbert NullFace} {face : NullFace}
    {incidence : ProgramPT06LocalC3NullIncidenceDatum
      period hPeriod geometry input face}
    (alignment : ProgramPT06TrueCutCollarNormalAlignmentDatum
      period hPeriod incidence)
    {throatCurrent : ThroatCoverCoordinates → ThroatCoverCoordinates}
    {normalDensity : ThroatCoverCoordinates → Real}
    (parameter : ProgramPT06NullFaceFiniteCollar)
    (hParameter : parameter ∈
      programPT06LocalC3NullCollarDomain period hPeriod incidence)
    (hThroat : DifferentiableAt Real throatCurrent
      (programPT06AmbientThroatProjection
        (programPT06LocalC3NullChartCoordinate
          period hPeriod incidence parameter)))
    (hNormal : DifferentiableAt Real normalDensity
      (programPT06AmbientThroatProjection
        (programPT06LocalC3NullChartCoordinate
          period hPeriod incidence parameter))) :
    mfderiv programPT06NullFaceCollarModelWithCorners
        (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
        (programPT06LocalC3RegularRadialCurrent
          period hPeriod incidence throatCurrent normalDensity)
        parameter (programPT06LocalC3NullCollarUnitNormal parameter) = 0 := by
  have hCoordinate :=
    programPT06LocalC3NullChartCoordinate_mdifferentiableAt
      period hPeriod incidence parameter hParameter
  have hCurrent :=
    (programPT06RegularAmbientCollarCurrent_hasFDerivAt
      hThroat hNormal).differentiableAt.mdifferentiableAt
  change mfderiv programPT06NullFaceCollarModelWithCorners
      (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
      (programPT06RegularAmbientCollarCurrent throatCurrent normalDensity ∘
        programPT06LocalC3NullChartCoordinate period hPeriod incidence)
      parameter (programPT06LocalC3NullCollarUnitNormal parameter) = 0
  calc
    _ = mfderiv (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
          (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
          (programPT06RegularAmbientCollarCurrent
            throatCurrent normalDensity)
          (programPT06LocalC3NullChartCoordinate
            period hPeriod incidence parameter)
          (mfderiv programPT06NullFaceCollarModelWithCorners
            (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
            (programPT06LocalC3NullChartCoordinate
              period hPeriod incidence)
            parameter
            (programPT06LocalC3NullCollarUnitNormal parameter)) :=
      mfderiv_comp_apply parameter hCurrent hCoordinate
        (programPT06LocalC3NullCollarUnitNormal parameter)
    _ = fderiv Real
          (programPT06RegularAmbientCollarCurrent
            throatCurrent normalDensity)
          (programPT06LocalC3NullChartCoordinate
            period hPeriod incidence parameter)
          (programPT06PureTransverseEmbedding 1) := by
      rw [ProgramPT06TrueCutCollarNormalAlignmentDatum.coordinate_normal
          period hPeriod alignment parameter hParameter,
        mfderiv_eq_fderiv]
      rfl
    _ = 0 :=
      programPT06RegularAmbientCollarCurrent_transverse_fderiv_zero
        hThroat hNormal

/-- The affine Gate-1033 current realizes its exact prescribed slope along
the actual unit collar normal. -/
theorem programPT06LocalC3AffineRadialCurrent_normal_mfderiv
    {NullFace : Type*} [Fintype NullFace]
    {geometry : FiniteNullFaceMobileGeometricDatum NullFace}
    {input : FiniteNullFacePhysicalHilbert NullFace} {face : NullFace}
    {incidence : ProgramPT06LocalC3NullIncidenceDatum
      period hPeriod geometry input face}
    (alignment : ProgramPT06TrueCutCollarNormalAlignmentDatum
      period hPeriod incidence)
    {throatCurrent : ThroatCoverCoordinates → ThroatCoverCoordinates}
    {normalDensity : ThroatCoverCoordinates → Real}
    {normalSlope : Real}
    (parameter : ProgramPT06NullFaceFiniteCollar)
    (hParameter : parameter ∈
      programPT06LocalC3NullCollarDomain period hPeriod incidence)
    (hThroat : DifferentiableAt Real throatCurrent
      (programPT06AmbientThroatProjection
        (programPT06LocalC3NullChartCoordinate
          period hPeriod incidence parameter)))
    (hNormal : DifferentiableAt Real normalDensity
      (programPT06AmbientThroatProjection
        (programPT06LocalC3NullChartCoordinate
          period hPeriod incidence parameter))) :
    mfderiv programPT06NullFaceCollarModelWithCorners
        (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
        (programPT06LocalC3AffineRadialCurrent period hPeriod incidence
          throatCurrent normalDensity normalSlope)
        parameter (programPT06LocalC3NullCollarUnitNormal parameter) =
      programPT06PureTransverseEmbedding normalSlope := by
  have hCoordinate :=
    programPT06LocalC3NullChartCoordinate_mdifferentiableAt
      period hPeriod incidence parameter hParameter
  have hCurrent :=
    (programPT06AffineAmbientCollarCurrent_hasFDerivAt
      (normalSlope := normalSlope) hThroat hNormal).differentiableAt.mdifferentiableAt
  change mfderiv programPT06NullFaceCollarModelWithCorners
      (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
      (programPT06AffineAmbientCollarCurrent throatCurrent normalDensity
          normalSlope ∘
        programPT06LocalC3NullChartCoordinate period hPeriod incidence)
      parameter (programPT06LocalC3NullCollarUnitNormal parameter) = _
  calc
    _ = mfderiv (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
          (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
          (programPT06AffineAmbientCollarCurrent
            throatCurrent normalDensity normalSlope)
          (programPT06LocalC3NullChartCoordinate
            period hPeriod incidence parameter)
          (mfderiv programPT06NullFaceCollarModelWithCorners
            (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
            (programPT06LocalC3NullChartCoordinate
              period hPeriod incidence)
            parameter
            (programPT06LocalC3NullCollarUnitNormal parameter)) :=
      mfderiv_comp_apply parameter hCurrent hCoordinate
        (programPT06LocalC3NullCollarUnitNormal parameter)
    _ = fderiv Real
          (programPT06AffineAmbientCollarCurrent
            throatCurrent normalDensity normalSlope)
          (programPT06LocalC3NullChartCoordinate
            period hPeriod incidence parameter)
          (programPT06PureTransverseEmbedding 1) := by
      rw [ProgramPT06TrueCutCollarNormalAlignmentDatum.coordinate_normal
          period hPeriod alignment parameter hParameter,
        mfderiv_eq_fderiv]
      rfl
    _ = programPT06PureTransverseEmbedding normalSlope :=
      programPT06AffineAmbientCollarCurrent_transverse_fderiv
        hThroat hNormal

end
end P0EFTJanusProgramPT06TrueCutCollarNormalAlignment4D
end JanusFormal
