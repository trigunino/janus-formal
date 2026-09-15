import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06TrueCutCollarNormalAlignment4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06WarpedNullMappingTorusFaceIncidence4D

/-!
# Warped-null collar chart-transition germ

Gate 1047 identifies the zero face in one mapping-torus chart.  This gate
packages the next missing datum as a local ambient coordinate transition near
one point of that face.  Its composition with the explicit warped half-collar
agrees as a one-sided germ with the chart of the genuine cut collar.

The transition has an invertible Jacobian.  The true positive collar normal is
that Jacobian applied to the warped radial vector `e₃`.  The transition fixes
the face point, but its normal action remains general.  No global collar,
metric, measure, or Piola-divergence compatibility is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06WarpedNullCollarChartTransition4D

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000

noncomputable section

open scoped Manifold ContDiff
open Topology
open P0EFTJanusMappingTorusCutThroatSmoothFiniteCollar4D
open P0EFTJanusMappingTorusCutCollarNormalDerivativeIsomorphism4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalProductEuler4D
open P0EFTJanusFiniteNullFaceMobileGeometricRealization4D
open P0EFTJanusProgramPT06AmbientNullFluxPullback4D
open P0EFTJanusProgramPT06ExplicitWarpedNullHyperplaneGeometry4D
open P0EFTJanusProgramPT06ExplicitWarpedNullLinearCollar4D
open P0EFTJanusProgramPT06LocalC3NullFaceCutCollarIncidence4D
open P0EFTJanusProgramPT06TrueCutCollarNormalAlignment4D
open P0EFTJanusProgramPT06WarpedNullClosedHalfCollar4D
open P0EFTJanusProgramPT06WarpedNullMappingTorusFaceIncidence4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- The proof-forgetting product coordinate on the closed half-collar is
smooth. -/
theorem contMDiff_programPT06WarpedNullClosedHalfCollarCoordinate :
    ContMDiff programPT06NullFaceCollarModelWithCorners
      (modelWithCornersSelf Real ProgramPT06WarpedNullCollarCoordinate4) ∞
      programPT06WarpedNullClosedHalfCollarCoordinate := by
  exact contMDiff_fst.prodMk_space
    (contMDiff_subtype_coe_Icc.comp contMDiff_snd)

/-- The explicit closed-half-collar embedding is smooth. -/
theorem contMDiff_programPT06WarpedNullClosedHalfCollarEmbedding :
    ContMDiff programPT06NullFaceCollarModelWithCorners
      (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4) ∞
      programPT06WarpedNullClosedHalfCollarEmbedding := by
  exact programPT06WarpedNullCollarEquiv.contDiff.contMDiff.comp
    contMDiff_programPT06WarpedNullClosedHalfCollarCoordinate

set_option backward.isDefEq.respectTransparency false in
/-- The proof-forgetting coordinate sends the canonical positive interval
tangent to `(0,1)`. -/
theorem programPT06WarpedNullClosedHalfCollarCoordinate_unitNormal_mfderiv
    (parameter : ProgramPT06WarpedNullClosedHalfCollar) :
    mfderiv programPT06NullFaceCollarModelWithCorners
        (modelWithCornersSelf Real ProgramPT06WarpedNullCollarCoordinate4)
        programPT06WarpedNullClosedHalfCollarCoordinate parameter
        (programPT06LocalC3NullCollarUnitNormal parameter) = (0, 1) := by
  change mfderiv programPT06NullFaceCollarModelWithCorners
      (modelWithCornersSelf Real ProgramPT06WarpedNullCollarCoordinate4)
      (Prod.map id (Subtype.val : CutCollarInterval → Real)) parameter
      (0, (cutCollarNormalDerivativeEquiv parameter.2).symm 1) = (0, 1)
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  rw [mfderiv_prodMap mdifferentiableAt_id
    ((contMDiff_subtype_coe_Icc (n := ∞)).mdifferentiableAt (by simp)),
    mfderiv_id]
  rw [← cutCollarNormalDerivativeEquiv_coe]
  change (0, (cutCollarNormalDerivativeEquiv parameter.2)
    ((cutCollarNormalDerivativeEquiv parameter.2).symm 1)) = (0, 1)
  simp

/-- The canonical positive tangent of the explicit half-collar maps to `e₃`. -/
theorem programPT06WarpedNullClosedHalfCollarEmbedding_unitNormal_mfderiv
    (parameter : ProgramPT06WarpedNullClosedHalfCollar) :
    mfderiv programPT06NullFaceCollarModelWithCorners
        (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
        programPT06WarpedNullClosedHalfCollarEmbedding parameter
        (programPT06LocalC3NullCollarUnitNormal parameter) =
      programPT06AmbientCoordinateBasis 3 := by
  have hCoordinate : MDifferentiableAt
      programPT06NullFaceCollarModelWithCorners
      (modelWithCornersSelf Real ProgramPT06WarpedNullCollarCoordinate4)
      programPT06WarpedNullClosedHalfCollarCoordinate parameter :=
    contMDiff_programPT06WarpedNullClosedHalfCollarCoordinate.mdifferentiableAt
      (by simp)
  have hCollar : MDifferentiableAt
      (modelWithCornersSelf Real ProgramPT06WarpedNullCollarCoordinate4)
      (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
      programPT06WarpedNullCollarEquiv
      (programPT06WarpedNullClosedHalfCollarCoordinate parameter) :=
    programPT06WarpedNullCollarEquiv.differentiableAt.mdifferentiableAt
  change mfderiv programPT06NullFaceCollarModelWithCorners
      (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
      (programPT06WarpedNullCollarEquiv ∘
        programPT06WarpedNullClosedHalfCollarCoordinate) parameter
      (programPT06LocalC3NullCollarUnitNormal parameter) = _
  rw [mfderiv_comp_apply parameter hCollar hCoordinate,
    programPT06WarpedNullClosedHalfCollarCoordinate_unitNormal_mfderiv]
  rw [mfderiv_eq_fderiv]
  exact programPT06WarpedNullCollar_radialDerivative
    (programPT06WarpedNullClosedHalfCollarCoordinate parameter)

/-- A local ambient transition whose pullback to the half-collar is the true
collar chart germ at one zero-face point. -/
structure ProgramPT06WarpedNullCollarChartTransitionGermDatum
    {input : FiniteNullFacePhysicalHilbert Unit}
    (incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input)
    (source : ProgramPT06NullFaceSource3)
    (hSource : source ∈ incidence.sourceDomain) where
  transition : ProgramPT06AmbientCoordinate4 → ProgramPT06AmbientCoordinate4
  transition_isLocalDiffeomorphAt :
    IsLocalDiffeomorphAt
      (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
      (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4) 3 transition
      (programPT06WarpedNullHyperplaneEmbedding source)
  collar_eventuallyEq :
    transition ∘ programPT06WarpedNullClosedHalfCollarEmbedding =ᶠ[
        𝓝 (programPT06WarpedNullZeroFace source)]
      programPT06LocalC3NullChartCoordinate period hPeriod incidence

/-- The transition fixes the already identified point of the zero face. -/
theorem ProgramPT06WarpedNullCollarChartTransitionGermDatum.transition_face
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    (datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource) :
    datum.transition (programPT06WarpedNullHyperplaneEmbedding source) =
      programPT06WarpedNullHyperplaneEmbedding source := by
  calc
    datum.transition (programPT06WarpedNullHyperplaneEmbedding source) =
        (datum.transition ∘ programPT06WarpedNullClosedHalfCollarEmbedding)
          (programPT06WarpedNullZeroFace source) := by simp
    _ = programPT06LocalC3NullChartCoordinate period hPeriod incidence
          (programPT06WarpedNullZeroFace source) :=
      datum.collar_eventuallyEq.eq_of_nhds
    _ = programPT06WarpedNullHyperplaneEmbedding source :=
      programPT06LocalC3NullChartCoordinate_face
        period hPeriod incidence source hSource

/-- Invertible Jacobian of the ambient transition at the face point. -/
def programPT06WarpedNullCollarTransitionJacobian
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    (datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource) :
    ProgramPT06AmbientCoordinate4 ≃L[Real] ProgramPT06AmbientCoordinate4 :=
  datum.transition_isLocalDiffeomorphAt.mfderivToContinuousLinearEquiv
    (by norm_num)

theorem programPT06WarpedNullCollarTransitionJacobian_coe
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    (datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource) :
    (programPT06WarpedNullCollarTransitionJacobian
        period hPeriod datum :
      ProgramPT06AmbientCoordinate4 →L[Real]
        ProgramPT06AmbientCoordinate4) =
      mfderiv (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
        (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
        datum.transition (programPT06WarpedNullHyperplaneEmbedding source) :=
  datum.transition_isLocalDiffeomorphAt.mfderivToContinuousLinearEquiv_coe
    (by norm_num)

/-- Absolute Jacobian density of the collar transition at the face. -/
def programPT06WarpedNullCollarTransitionJacobianDensity
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    (datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource) : Real :=
  |LinearMap.det
    (programPT06WarpedNullCollarTransitionJacobian
      period hPeriod datum).toLinearEquiv.toLinearMap|

/-- A chart transition has strictly positive absolute Jacobian density. -/
theorem programPT06WarpedNullCollarTransitionJacobianDensity_pos
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    (datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource) :
    0 < programPT06WarpedNullCollarTransitionJacobianDensity
      period hPeriod datum := by
  rw [programPT06WarpedNullCollarTransitionJacobianDensity, abs_pos]
  exact (LinearEquiv.isUnit_det'
    (programPT06WarpedNullCollarTransitionJacobian
      period hPeriod datum).toLinearEquiv).ne_zero

/-- Differential form of the commutative collar germ. -/
theorem ProgramPT06WarpedNullCollarChartTransitionGermDatum.mfderiv_eq_transition_comp
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    (datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource) :
    mfderiv programPT06NullFaceCollarModelWithCorners
        (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
        (programPT06LocalC3NullChartCoordinate period hPeriod incidence)
        (programPT06WarpedNullZeroFace source) =
      (mfderiv (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
          (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
          datum.transition
          (programPT06WarpedNullClosedHalfCollarEmbedding
            (programPT06WarpedNullZeroFace source))).comp
        (mfderiv programPT06NullFaceCollarModelWithCorners
          (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
          programPT06WarpedNullClosedHalfCollarEmbedding
          (programPT06WarpedNullZeroFace source)) := by
  have hWarped : MDifferentiableAt
      programPT06NullFaceCollarModelWithCorners
      (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
      programPT06WarpedNullClosedHalfCollarEmbedding
      (programPT06WarpedNullZeroFace source) :=
    contMDiff_programPT06WarpedNullClosedHalfCollarEmbedding.mdifferentiableAt
      (by simp)
  have hTransition : MDifferentiableAt
      (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
      (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
      datum.transition
      (programPT06WarpedNullClosedHalfCollarEmbedding
        (programPT06WarpedNullZeroFace source)) := by
    rw [programPT06WarpedNullClosedHalfCollarEmbedding_zeroFace]
    exact datum.transition_isLocalDiffeomorphAt.mdifferentiableAt (by norm_num)
  calc
    _ = mfderiv programPT06NullFaceCollarModelWithCorners
          (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
          (datum.transition ∘
            programPT06WarpedNullClosedHalfCollarEmbedding)
          (programPT06WarpedNullZeroFace source) :=
      datum.collar_eventuallyEq.mfderiv_eq.symm
    _ = (mfderiv (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
          (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
          datum.transition
          (programPT06WarpedNullClosedHalfCollarEmbedding
            (programPT06WarpedNullZeroFace source))).comp
        (mfderiv programPT06NullFaceCollarModelWithCorners
          (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
          programPT06WarpedNullClosedHalfCollarEmbedding
          (programPT06WarpedNullZeroFace source)) := by
      exact mfderiv_comp (programPT06WarpedNullZeroFace source)
        hTransition hWarped

/-- The true collar chart sends its positive interval tangent to the transition
Jacobian applied to the explicit radial vector. -/
theorem ProgramPT06WarpedNullCollarChartTransitionGermDatum.unitNormal_mfderiv
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    (datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource) :
    mfderiv programPT06NullFaceCollarModelWithCorners
        (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
        (programPT06LocalC3NullChartCoordinate period hPeriod incidence)
        (programPT06WarpedNullZeroFace source)
        (programPT06LocalC3NullCollarUnitNormal
          (programPT06WarpedNullZeroFace source)) =
      programPT06WarpedNullCollarTransitionJacobian period hPeriod datum
        (programPT06AmbientCoordinateBasis 3) := by
  have hDerivative := congrArg
    (fun derivative => derivative
      (programPT06LocalC3NullCollarUnitNormal
        (programPT06WarpedNullZeroFace source)))
    (datum.mfderiv_eq_transition_comp period hPeriod)
  calc
    _ = ((mfderiv (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
            (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
            datum.transition
            (programPT06WarpedNullClosedHalfCollarEmbedding
              (programPT06WarpedNullZeroFace source))).comp
          (mfderiv programPT06NullFaceCollarModelWithCorners
            (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
            programPT06WarpedNullClosedHalfCollarEmbedding
            (programPT06WarpedNullZeroFace source)))
          (programPT06LocalC3NullCollarUnitNormal
            (programPT06WarpedNullZeroFace source)) := hDerivative
    _ = mfderiv (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
          (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
          datum.transition
          (programPT06WarpedNullClosedHalfCollarEmbedding
            (programPT06WarpedNullZeroFace source))
          (mfderiv programPT06NullFaceCollarModelWithCorners
            (modelWithCornersSelf Real ProgramPT06AmbientCoordinate4)
            programPT06WarpedNullClosedHalfCollarEmbedding
            (programPT06WarpedNullZeroFace source)
            (programPT06LocalC3NullCollarUnitNormal
              (programPT06WarpedNullZeroFace source))) := rfl
    _ = _ := by
      rw [programPT06WarpedNullClosedHalfCollarEmbedding_unitNormal_mfderiv]
      rw [programPT06WarpedNullClosedHalfCollarEmbedding_zeroFace]
      rw [← programPT06WarpedNullCollarTransitionJacobian_coe]
      rfl

/-- The actual cut-bulk chart normal is the same transported radial vector. -/
theorem ProgramPT06WarpedNullCollarChartTransitionGermDatum.trueCutBulkChartUnitNormal
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    (datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource) :
    programPT06TrueCutBulkChartUnitNormal period hPeriod incidence
        (programPT06LocalC3NullCollarMap period hPeriod incidence
          (programPT06WarpedNullZeroFace source)) =
      programPT06WarpedNullCollarTransitionJacobian period hPeriod datum
        (programPT06AmbientCoordinateBasis 3) := by
  rw [← programPT06LocalC3NullChartCoordinate_unitNormal_mfderiv_eq_trueCutBulkChartUnitNormal
    period hPeriod incidence (programPT06WarpedNullZeroFace source)
    ⟨hSource, Set.mem_univ _⟩]
  exact datum.unitNormal_mfderiv period hPeriod

/-- The transported true collar normal cannot vanish. -/
theorem ProgramPT06WarpedNullCollarChartTransitionGermDatum.trueCutBulkChartUnitNormal_ne_zero
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    (datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource) :
    programPT06TrueCutBulkChartUnitNormal period hPeriod incidence
        (programPT06LocalC3NullCollarMap period hPeriod incidence
          (programPT06WarpedNullZeroFace source)) ≠ 0 := by
  rw [datum.trueCutBulkChartUnitNormal period hPeriod]
  intro hImage
  have hBasis : programPT06AmbientCoordinateBasis 3 ≠ 0 := by
    intro hZero
    have hCoordinate := congrArg
      (fun vector : ProgramPT06AmbientCoordinate4 => vector 3) hZero
    simp [programPT06AmbientCoordinateBasis] at hCoordinate
  apply hBasis
  apply (programPT06WarpedNullCollarTransitionJacobian
    period hPeriod datum).injective
  simpa using hImage

/-- Gate bundle: the transition fixes the face point, has positive absolute
Jacobian, and transports `e₃` to the genuine cut-bulk chart normal. -/
theorem programPT06WarpedNullCollarChartTransition_bundle
    {input : FiniteNullFacePhysicalHilbert Unit}
    {incidence : ProgramPT06WarpedNullLocalC3IncidenceDatum
      period hPeriod input}
    {source : ProgramPT06NullFaceSource3}
    {hSource : source ∈ incidence.sourceDomain}
    (datum : ProgramPT06WarpedNullCollarChartTransitionGermDatum
      period hPeriod incidence source hSource) :
    datum.transition (programPT06WarpedNullHyperplaneEmbedding source) =
        programPT06WarpedNullHyperplaneEmbedding source ∧
      0 < programPT06WarpedNullCollarTransitionJacobianDensity
        period hPeriod datum ∧
      programPT06TrueCutBulkChartUnitNormal period hPeriod incidence
          (programPT06LocalC3NullCollarMap period hPeriod incidence
            (programPT06WarpedNullZeroFace source)) =
        programPT06WarpedNullCollarTransitionJacobian period hPeriod datum
          (programPT06AmbientCoordinateBasis 3) :=
  ⟨datum.transition_face period hPeriod,
    programPT06WarpedNullCollarTransitionJacobianDensity_pos
      period hPeriod datum,
    datum.trueCutBulkChartUnitNormal period hPeriod⟩

end
end P0EFTJanusProgramPT06WarpedNullCollarChartTransition4D
end JanusFormal
