import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiagonalExtendedFourSectorBoundaryNoGo4D

/-!
# Four canonical projectors commute with the diagonal Candidate-A Riesz operator

The four completed coordinate factors split the diagonal BRST--matter--LL
Hessian exactly. This statement concerns the diagonal operator. The augmented
physical Hessian has seven further blocks, whose commutators need not vanish.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT12DiagonalFourSectorRieszCommutation4D

set_option autoImplicit false
set_option maxHeartbeats 3600000
set_option synthInstance.maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
noncomputable section

open scoped InnerProductSpace
open P0EFTJanusProgramPT12DiagonalExtendedBulkHilbertProjectors4D
open P0EFTJanusProgramPT12DiagonalExtendedBulkMetricAbelianHilbertProjectors4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateAAbelianExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalPairedAbelianBRSTGaugeFermion4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPGlobalFullLLGraphRiesz4D

variable {D A M L : Type*}
  [NormedAddCommGroup D] [InnerProductSpace Real D]
  [NormedAddCommGroup A] [InnerProductSpace Real A]
  [NormedAddCommGroup M] [InnerProductSpace Real M]
  [NormedAddCommGroup L] [InnerProductSpace Real L]

private abbrev FourGraph := WithLp 2
  (D × WithLp 2 (A × WithLp 2 (M × L)))

private theorem d_apply (x : FourGraph (D := D) (A := A) (M := M) (L := L)) :
    diffeomorphismProjector x = WithLp.toLp 2 (x.fst,
      (0 : WithLp 2 (A × WithLp 2 (M × L)))) := by
  apply graphCoordinates.injective
  rfl

private theorem a_apply (x : FourGraph (D := D) (A := A) (M := M) (L := L)) :
    abelianProjector x = WithLp.toLp 2 (0,
      WithLp.toLp 2 (x.snd.fst, (0 : WithLp 2 (M × L)))) := by
  apply graphCoordinates.injective
  rfl

private theorem m_apply (x : FourGraph (D := D) (A := A) (M := M) (L := L)) :
    matterProjector x = WithLp.toLp 2 (0,
      WithLp.toLp 2 (0, WithLp.toLp 2 (x.snd.snd.fst, (0 : L)))) := by
  apply graphCoordinates.injective
  rfl

private theorem l_apply (x : FourGraph (D := D) (A := A) (M := M) (L := L)) :
    llProjector x = WithLp.toLp 2 (0,
      WithLp.toLp 2 (0, WithLp.toLp 2 (0, x.snd.snd.snd))) := by
  apply graphCoordinates.injective
  rfl

private theorem commute_of_form
    (B : FourGraph (D := D) (A := A) (M := M) (L := L) →L[Real]
      FourGraph (D := D) (A := A) (M := M) (L := L) →L[Real] Real)
    (R P : FourGraph (D := D) (A := A) (M := M) (L := L) →L[Real]
      FourGraph (D := D) (A := A) (M := M) (L := L))
    (hR : ∀ x y, inner Real (R x) y = B x y)
    (hP : ∀ x y, inner Real (P x) y = inner Real x (P y))
    (hB : ∀ x y, B (P x) y = B x (P y))
    (x : FourGraph (D := D) (A := A) (M := M) (L := L)) :
    R (P x) = P (R x) := by
  apply ext_inner_right Real
  intro y
  rw [hR, hB, ← hR, hP]

/-- A bilinear form separated across four genuine `WithLp 2` factors has a
Riesz representative commuting with each coordinate projector. -/
theorem four_projectors_commute_of_block_form
    (B : FourGraph (D := D) (A := A) (M := M) (L := L) →L[Real]
      FourGraph (D := D) (A := A) (M := M) (L := L) →L[Real] Real)
    (R : FourGraph (D := D) (A := A) (M := M) (L := L) →L[Real]
      FourGraph (D := D) (A := A) (M := M) (L := L))
    (bD : D →L[Real] D →L[Real] Real)
    (bA : A →L[Real] A →L[Real] Real)
    (bM : M →L[Real] M →L[Real] Real)
    (bL : L →L[Real] L →L[Real] Real)
    (hB : ∀ x y,
      B x y = bD x.fst y.fst + bA x.snd.fst y.snd.fst +
        bM x.snd.snd.fst y.snd.snd.fst +
        bL x.snd.snd.snd y.snd.snd.snd)
    (hR : ∀ x y, inner Real (R x) y = B x y)
    (x : FourGraph (D := D) (A := A) (M := M) (L := L)) :
    R (diffeomorphismProjector x) = diffeomorphismProjector (R x) ∧
    R (abelianProjector x) = abelianProjector (R x) ∧
    R (matterProjector x) = matterProjector (R x) ∧
    R (llProjector x) = llProjector (R x) := by
  have hSelfD (u v : FourGraph (D := D) (A := A) (M := M) (L := L)) :
      inner Real (diffeomorphismProjector u) v =
        inner Real u (diffeomorphismProjector v) := by
    rw [d_apply u, d_apply v]
    simp [WithLp.prod_inner_apply]
  have hSelfA (u v : FourGraph (D := D) (A := A) (M := M) (L := L)) :
      inner Real (abelianProjector u) v =
        inner Real u (abelianProjector v) := by
    rw [a_apply u, a_apply v]
    simp [WithLp.prod_inner_apply]
  have hSelfM (u v : FourGraph (D := D) (A := A) (M := M) (L := L)) :
      inner Real (matterProjector u) v =
        inner Real u (matterProjector v) := by
    rw [m_apply u, m_apply v]
    simp [WithLp.prod_inner_apply]
  have hSelfL (u v : FourGraph (D := D) (A := A) (M := M) (L := L)) :
      inner Real (llProjector u) v =
        inner Real u (llProjector v) := by
    rw [l_apply u, l_apply v]
    simp [WithLp.prod_inner_apply]
  have hBD (u v : FourGraph (D := D) (A := A) (M := M) (L := L)) :
      B (diffeomorphismProjector u) v = B u (diffeomorphismProjector v) := by
    rw [hB, hB, d_apply u, d_apply v]
    simp
  have hBA (u v : FourGraph (D := D) (A := A) (M := M) (L := L)) :
      B (abelianProjector u) v = B u (abelianProjector v) := by
    rw [hB, hB, a_apply u, a_apply v]
    simp
  have hBM (u v : FourGraph (D := D) (A := A) (M := M) (L := L)) :
      B (matterProjector u) v = B u (matterProjector v) := by
    rw [hB, hB, m_apply u, m_apply v]
    simp
  have hBL (u v : FourGraph (D := D) (A := A) (M := M) (L := L)) :
      B (llProjector u) v = B u (llProjector v) := by
    rw [hB, hB, l_apply u, l_apply v]
    simp
  exact ⟨commute_of_form B R diffeomorphismProjector hR hSelfD hBD x,
    commute_of_form B R abelianProjector hR hSelfA hBA x,
    commute_of_form B R matterProjector hR hSelfM hBM x,
    commute_of_form B R llProjector hR hSelfL hBL x⟩

private def pullbackRealBilinear
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E]
    [NormedAddCommGroup F] [NormedSpace Real F]
    (form : F →L[Real] F →L[Real] Real)
    (projection : E →L[Real] F) : E →L[Real] E →L[Real] Real :=
  form.bilinearComp (𝕜₁' := Real) (𝕜₂' := Real)
    (E' := E) (F' := E) projection projection

section CandidateA

attribute [local instance]
  diagonalL2DiffeomorphismNormedAddCommGroup
  diagonalL2DiffeomorphismInnerProductSpace
  diagonalL2AbelianInnerProductSpace
  diagonalL2MatterInnerProductSpace
  diagonalL2LLInnerProductSpace
  diagonalL2ExtendedBulkNormedAddCommGroup
  diagonalL2ExtendedBulkInnerProductSpace
  diagonalL2ExtendedBulkCompleteSpace

variable (period : Real) (hPeriod : period ≠ 0)

/-- The four genuine completed factor projectors commute with the Riesz
representative of the diagonal Candidate-A action Hessian. -/
theorem diagonalExtendedBulkL2RieszOperator_four_projectors_commute
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (x : GlobalCandidateADiagonalExtendedBulkL2Hilbert period hPeriod metric
      massSquared data analysis) :
    diagonalExtendedBulkL2RieszOperator period hPeriod metric massSquared data
        analysis (diffeomorphismProjector x) =
      diffeomorphismProjector
        (diagonalExtendedBulkL2RieszOperator period hPeriod metric massSquared
          data analysis x) ∧
    diagonalExtendedBulkL2RieszOperator period hPeriod metric massSquared data
        analysis (abelianProjector x) =
      abelianProjector
        (diagonalExtendedBulkL2RieszOperator period hPeriod metric massSquared
          data analysis x) ∧
    diagonalExtendedBulkL2RieszOperator period hPeriod metric massSquared data
        analysis (matterProjector x) =
      matterProjector
        (diagonalExtendedBulkL2RieszOperator period hPeriod metric massSquared
          data analysis x) ∧
    diagonalExtendedBulkL2RieszOperator period hPeriod metric massSquared data
        analysis (llProjector x) =
      llProjector
        (diagonalExtendedBulkL2RieszOperator period hPeriod metric massSquared
          data analysis x) := by
  let matterEquiv := programPPrimitiveSpinCMatterL2GraphEquiv period hPeriod massSquared
  let matterForm := pullbackRealBilinear
    (programPPrimitiveSpinCMatterGraphForm period hPeriod massSquared)
    matterEquiv.toContinuousLinearMap
  have hSplit (first second : GlobalCandidateADiagonalExtendedBulkL2Hilbert
      period hPeriod metric massSquared data analysis) :
      diagonalExtendedBulkL2Hessian period hPeriod metric massSquared data
          analysis first second =
        globalCandidateADiagonalDiffeomorphismOffShellHessian
            period hPeriod couplings metric first.fst second.fst +
          globalPairedAbelianOffShellHessian period hPeriod metric
            first.snd.fst second.snd.fst +
          matterForm first.snd.snd.fst second.snd.snd.fst +
          globalCandidateAFullLLGraphForm period hPeriod data analysis
            first.snd.snd.snd second.snd.snd.snd := by
    rw [diagonalExtendedBulkL2Hessian_apply,
      diagonalExtendedBulkHessian_apply]
    rfl
  exact four_projectors_commute_of_block_form
    (diagonalExtendedBulkL2Hessian period hPeriod metric massSquared data analysis)
    (diagonalExtendedBulkL2RieszOperator period hPeriod metric massSquared data analysis)
    (globalCandidateADiagonalDiffeomorphismOffShellHessian period hPeriod couplings metric)
    (globalPairedAbelianOffShellHessian period hPeriod metric)
    matterForm
    (globalCandidateAFullLLGraphForm period hPeriod data analysis)
    hSplit
    (diagonalExtendedBulkL2RieszOperator_pairing period hPeriod metric
      massSquared data analysis) x

end CandidateA
end

end P0EFTJanusProgramPT12DiagonalFourSectorRieszCommutation4D
end JanusFormal
