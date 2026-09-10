import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT05HorizontalGeometricIncidenceSupport4D

/-!
# Canonical integrated GHY-to-joint trace

For a nonempty finite null-face carrier, the completed first-sheet GHY
integral can be distributed uniformly over the final endpoint of every face.
This gives an actual linear inhabitant of Gate 854's reduced trace operator
and proves its integrated trace law for every completed boundary density.

The construction is an integrated finite-carrier trace.  It does not supply
the still-missing local codimension-two restriction map on the orientation
boundary.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06CanonicalIntegratedGHYJointTrace4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusFiniteNullFaceAction
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
open P0EFTJanusProgramPT05CutBulkLocalDensityStokesBridge4D
open P0EFTJanusProgramPT05GHYLocalDensityRelativeBridge4D
open P0EFTJanusProgramPT05GeometricStratifiedDensityCochain4D
open P0EFTJanusProgramPT05AvailableStratifiedHorizontalComplex4D
open P0EFTJanusProgramPT05MissingHorizontalGeometricContracts4D
open P0EFTJanusProgramPT05HorizontalGeometricIncidenceSupport4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Uniform coefficient assigned to each face of a nonempty finite carrier. -/
def programPT06FiniteJointAveragingWeight
    (NullFace : Type*) [Fintype NullFace] : Real :=
  (Fintype.card NullFace : Real)⁻¹

/-- The completed GHY integral, distributed uniformly over the final joint
of every face.  This is a genuine linear map on the existing boundary scalar
field carrier. -/
def programPT06CanonicalIntegratedGHYToJointTrace
    {NullFace : Type*} [Fintype NullFace] [Nonempty NullFace] :
    ProgramPT05GHYToJointTraceOperator period hPeriod NullFace where
  toLinearMap :=
    { toFun := fun density _face endpoint =>
        match endpoint with
        | .initial => 0
        | .final =>
            programPT06FiniteJointAveragingWeight NullFace *
              programPT05GeometricGHYDensityIntegral period hPeriod density
      map_add' := by
        intro x y
        funext face endpoint
        cases endpoint with
        | initial => simp
        | final =>
            change
              programPT06FiniteJointAveragingWeight NullFace *
                  candidateANormalBoundaryFirstSheetIntegralCLM period hPeriod
                    (x + y) =
                programPT06FiniteJointAveragingWeight NullFace *
                    candidateANormalBoundaryFirstSheetIntegralCLM period hPeriod x +
                  programPT06FiniteJointAveragingWeight NullFace *
                    candidateANormalBoundaryFirstSheetIntegralCLM period hPeriod y
            rw [map_add]
            ring
      map_smul' := by
        intro scalar x
        funext face endpoint
        cases endpoint with
        | initial => simp
        | final =>
            change
              programPT06FiniteJointAveragingWeight NullFace *
                  candidateANormalBoundaryFirstSheetIntegralCLM period hPeriod
                    (scalar • x) =
                scalar *
                  (programPT06FiniteJointAveragingWeight NullFace *
                    candidateANormalBoundaryFirstSheetIntegralCLM period hPeriod x)
            rw [map_smul]
            ring }

@[simp]
theorem programPT06CanonicalIntegratedGHYToJointTrace_initial
    {NullFace : Type*} [Fintype NullFace] [Nonempty NullFace]
    (density : CandidateANormalBoundaryScalarField period hPeriod)
    (face : NullFace) :
    (programPT06CanonicalIntegratedGHYToJointTrace period hPeriod).toLinearMap
        density face .initial = 0 := by
  rfl

@[simp]
theorem programPT06CanonicalIntegratedGHYToJointTrace_final
    {NullFace : Type*} [Fintype NullFace] [Nonempty NullFace]
    (density : CandidateANormalBoundaryScalarField period hPeriod)
    (face : NullFace) :
    (programPT06CanonicalIntegratedGHYToJointTrace period hPeriod).toLinearMap
        density face .final =
      programPT06FiniteJointAveragingWeight NullFace *
        programPT05GeometricGHYDensityIntegral period hPeriod density := by
  rfl

/-- The reduced trace commutes with integration for every completed boundary
density, not only for the canonical GHY integrand. -/
theorem programPT06CanonicalIntegratedGHYToJointTrace_integration
    {NullFace : Type*} [Fintype NullFace] [Nonempty NullFace]
    (density : CandidateANormalBoundaryScalarField period hPeriod) :
    programPT05GeometricJointDensityIntegral
        (programPT05GHYToJointTracedDensity period hPeriod
          (programPT06CanonicalIntegratedGHYToJointTrace
            (NullFace := NullFace) period hPeriod)
          density) =
      programPT05GeometricGHYDensityIntegral period hPeriod density := by
  have hCard : (Fintype.card NullFace : Real) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card NullFace ≠ 0)
  unfold programPT05GeometricJointDensityIntegral
    programPT05GHYToJointTracedDensity
  simp only [programPT06CanonicalIntegratedGHYToJointTrace_initial,
    programPT06CanonicalIntegratedGHYToJointTrace_final, zero_add,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  unfold programPT06FiniteJointAveragingWeight
  rw [← mul_assoc, mul_inv_cancel₀ hCard, one_mul]

/-- The canonical completed GHY density therefore has concrete Gate 854
trace support. -/
theorem programPT06CanonicalIntegratedGHYToJointTrace_support
    {NullFace : Type*} [Fintype NullFace] [Nonempty NullFace]
    (einsteinScale : Real)
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (current : CandidateANormalBoundaryFunctionalCore period hPeriod metric ×
      Real) :
    ProgramPT05CanonicalGHYToJointTraceSupport period hPeriod einsteinScale
      metric current
      (programPT06CanonicalIntegratedGHYToJointTrace
        (NullFace := NullFace) period hPeriod) := by
  constructor
  exact programPT06CanonicalIntegratedGHYToJointTrace_integration
    (NullFace := NullFace) period hPeriod
    (programPT05CanonicalGHYLocalDensityCochain period hPeriod
      einsteinScale metric current).nonNullBoundaryDensity

/-- Once the independent bulk-to-null Stokes support is supplied, the new
trace removes the GHY-to-joint support hypothesis from the completed
horizontal incidence square. -/
theorem programPT06CanonicalIntegratedGHYJointIncidence_commutes
    {NullFace : Type*} [Fintype NullFace] [Nonempty NullFace]
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real)
    (faces : NullFace → FiniteNullFaceActionDatum)
    (einsteinScale : Real)
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (current : CandidateANormalBoundaryFunctionalCore period hPeriod metric ×
      Real)
    (restriction : ProgramPT05BulkToNullRestrictionOperator NullFace)
    (hBulk : ProgramPT05CanonicalBulkToNullStokesSupport period hPeriod
      field test faces restriction)
    (contracts : ∀ face, NullFaceIntervalIntegrability (faces face)) :
    programPT05AvailableStratifiedIntegratedDH
        (programPT05ContractCompletedHorizontalSource period hPeriod field test
          faces
          (programPT05CanonicalGHYLocalDensityCochain period hPeriod
            einsteinScale metric current).nonNullBoundaryDensity) =
      programPT05ContractCompletedHorizontalTarget period hPeriod field test
        faces
        (programPT05CanonicalHorizontalDensityDataOfIncidence period hPeriod
          field test einsteinScale metric current restriction
          (programPT06CanonicalIntegratedGHYToJointTrace
            (NullFace := NullFace) period hPeriod)) := by
  exact programPT05CanonicalHorizontalIncidence_integration_commutes
    period hPeriod massSquared field test faces einsteinScale metric current
    restriction (programPT06CanonicalIntegratedGHYToJointTrace
      (NullFace := NullFace) period hPeriod)
    hBulk
    (programPT06CanonicalIntegratedGHYToJointTrace_support
      (NullFace := NullFace) period hPeriod einsteinScale metric current)
    contracts

end
end P0EFTJanusProgramPT06CanonicalIntegratedGHYJointTrace4D
end JanusFormal
