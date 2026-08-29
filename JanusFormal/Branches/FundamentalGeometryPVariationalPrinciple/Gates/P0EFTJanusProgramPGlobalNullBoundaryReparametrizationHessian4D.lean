import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCovariantAction4D

/-!
# Global null-boundary reparametrization Hessian

This gate scales the already supplied null-generator normalization function
by a real parameter.  The existing finite face-plus-joint transgression theorem
then makes the exact Candidate-A null-boundary action constant on that genuine
reparametrization curve.  Its first and second real derivatives vanish.

Only generator reparametrizations are covered.  No normal displacement or
general variation of the null-face geometry is claimed.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalNullBoundaryReparametrizationHessian4D

set_option autoImplicit false

noncomputable section

open scoped BigOperators ContDiff
open P0EFTJanusNullJointReparametrizationCancellation
open P0EFTJanusFiniteNullFaceAction
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Real scaling of one supplied null-generator normalization. -/
def scaledNullGeneratorReparametrizationData
    (parameter : Real)
    (data : NullGeneratorReparametrizationData) :
    NullGeneratorReparametrizationData where
  area := data.area
  expansion := data.expansion
  inaffinity := data.inaffinity
  sigma := fun point => parameter * data.sigma point
  sigmaDerivative := fun point => parameter * data.sigmaDerivative point
  area_hasDerivAt := data.area_hasDerivAt
  sigma_hasDerivAt := fun point =>
    (data.sigma_hasDerivAt point).const_mul parameter

theorem scaledNullGenerator_localFaceShift
    (parameter point : Real)
    (data : NullGeneratorReparametrizationData) :
    localFaceShift
        (scaledNullGeneratorReparametrizationData parameter data) point =
      parameter * localFaceShift data point := by
  simp [scaledNullGeneratorReparametrizationData, localFaceShift,
    inaffinityDensityShift, shiftedInaffinity, expansionDensityShift]
  ring

/-- The same finite face with only its normalization function scaled. -/
def scaledFiniteNullFaceActionDatum
    (parameter : Real) (face : FiniteNullFaceActionDatum) :
    FiniteNullFaceActionDatum where
  generator :=
    scaledNullGeneratorReparametrizationData parameter face.generator
  interval := face.interval
  einsteinScale := face.einsteinScale
  orientationSign := face.orientationSign
  orientationSignAdmissible := face.orientationSignAdmissible
  renormalizationLengthScale := face.renormalizationLengthScale
  renormalizationLengthScalePositive :=
    face.renormalizationLengthScalePositive
  initialJointAction := face.initialJointAction
  finalJointAction := face.finalJointAction

/-- The untransformed face action is unchanged because scaling touches only
the reparametrization data. -/
theorem finiteNullFaceAction_scaled_eq
    (parameter : Real) (face : FiniteNullFaceActionDatum) :
    finiteNullFaceAction
        (scaledFiniteNullFaceActionDatum parameter face) =
      finiteNullFaceAction face :=
  rfl

/-- The existing interval contract is stable under real scaling of the
normalization function. -/
def scaledFiniteNullFaceIntervalIntegrability
    (parameter : Real) (face : FiniteNullFaceActionDatum)
    (contract : NullFaceIntervalIntegrability face) :
    NullFaceIntervalIntegrability
      (scaledFiniteNullFaceActionDatum parameter face) where
  inaffinity := by
    change IntervalIntegrable
      (inaffinityFaceDensity face) MeasureTheory.volume
        face.interval.initialParameter face.interval.finalParameter
    exact contract.inaffinity
  expansionCounterterm := by
    change IntervalIntegrable
      (expansionCountertermFaceDensity face) MeasureTheory.volume
        face.interval.initialParameter face.interval.finalParameter
    exact contract.expansionCounterterm
  reparametrizationShift := by
    have hScaled := contract.reparametrizationShift.const_mul parameter
    change IntervalIntegrable
      (localFaceShift
        (scaledNullGeneratorReparametrizationData
          parameter face.generator))
      MeasureTheory.volume face.interval.initialParameter
        face.interval.finalParameter
    convert hScaled using 1
    funext point
    exact scaledNullGenerator_localFaceShift parameter point face.generator

/-- Exact finite face-plus-joint action along the normalization scaling. -/
def finiteNullFaceReparametrizationActionCurve
    (face : FiniteNullFaceActionDatum) (parameter : Real) : Real :=
  reparametrizedFiniteNullFaceAction
    (scaledFiniteNullFaceActionDatum parameter face)

theorem finiteNullFaceReparametrizationActionCurve_eq
    (face : FiniteNullFaceActionDatum)
    (contract : NullFaceIntervalIntegrability face)
    (parameter : Real) :
    finiteNullFaceReparametrizationActionCurve face parameter =
      finiteNullFaceAction face := by
  rw [finiteNullFaceReparametrizationActionCurve,
    reparametrizedFiniteNullFaceAction_eq
      (scaledFiniteNullFaceActionDatum parameter face)
      (scaledFiniteNullFaceIntervalIntegrability
        parameter face contract),
    finiteNullFaceAction_scaled_eq]

/-- The exact global finite-null-boundary block along simultaneous scaling of
every supplied face normalization. -/
def globalCandidateANullBoundaryReparametrizationActionCurve
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (parameter : Real) : Real :=
  ∑ face : NullFace,
    finiteNullFaceReparametrizationActionCurve
      (data.nullActionFaces face) parameter

theorem globalCandidateANullBoundaryReparametrizationActionCurve_eq
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (contract :
      GlobalCandidateANullBoundaryReparametrizationIntegrability
        period hPeriod data)
    (parameter : Real) :
    globalCandidateANullBoundaryReparametrizationActionCurve
        period hPeriod data parameter =
      globalCandidateANullBoundaryAction period hPeriod data := by
  classical
  unfold globalCandidateANullBoundaryReparametrizationActionCurve
    globalCandidateANullBoundaryAction
  apply Finset.sum_congr rfl
  intro face _
  exact finiteNullFaceReparametrizationActionCurve_eq
    (data.nullActionFaces face)
    (contract.toInterval period hPeriod face) parameter

theorem globalCandidateANullBoundaryReparametrizationActionCurve_contDiff
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (contract :
      GlobalCandidateANullBoundaryReparametrizationIntegrability
        period hPeriod data) :
    ContDiff Real ∞
      (globalCandidateANullBoundaryReparametrizationActionCurve
        period hPeriod data) := by
  rw [show
    globalCandidateANullBoundaryReparametrizationActionCurve
        period hPeriod data =
      fun _parameter =>
        globalCandidateANullBoundaryAction period hPeriod data by
    funext parameter
    exact globalCandidateANullBoundaryReparametrizationActionCurve_eq
      period hPeriod data contract parameter]
  exact contDiff_const

theorem globalCandidateANullBoundaryReparametrizationActionCurve_hasDerivAt
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (contract :
      GlobalCandidateANullBoundaryReparametrizationIntegrability
        period hPeriod data)
    (parameter : Real) :
    HasDerivAt
      (globalCandidateANullBoundaryReparametrizationActionCurve
        period hPeriod data)
      0 parameter := by
  rw [show
    globalCandidateANullBoundaryReparametrizationActionCurve
        period hPeriod data =
      fun _varied =>
        globalCandidateANullBoundaryAction period hPeriod data by
    funext varied
    exact globalCandidateANullBoundaryReparametrizationActionCurve_eq
      period hPeriod data contract varied]
  exact hasDerivAt_const parameter _

theorem globalCandidateANullBoundaryReparametrizationActionCurve_deriv
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (contract :
      GlobalCandidateANullBoundaryReparametrizationIntegrability
        period hPeriod data)
    (parameter : Real) :
    deriv
        (globalCandidateANullBoundaryReparametrizationActionCurve
          period hPeriod data)
        parameter =
      0 :=
  (globalCandidateANullBoundaryReparametrizationActionCurve_hasDerivAt
    period hPeriod data contract parameter).deriv

/-- The same-action second derivative on every supplied generator
reparametrization direction is exactly zero. -/
theorem globalCandidateANullBoundaryReparametrizationActionCurve_secondDeriv
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (contract :
      GlobalCandidateANullBoundaryReparametrizationIntegrability
        period hPeriod data)
    (parameter : Real) :
    deriv
        (fun varied =>
          deriv
            (globalCandidateANullBoundaryReparametrizationActionCurve
              period hPeriod data)
            varied)
        parameter =
      0 := by
  have hConstant :
      (fun varied =>
        deriv
          (globalCandidateANullBoundaryReparametrizationActionCurve
            period hPeriod data)
          varied) =
        fun _varied => 0 := by
    funext varied
    exact globalCandidateANullBoundaryReparametrizationActionCurve_deriv
      period hPeriod data contract varied
  rw [hConstant]
  simp

end
end P0EFTJanusProgramPGlobalNullBoundaryReparametrizationHessian4D
end JanusFormal
