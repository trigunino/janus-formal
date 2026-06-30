import JanusFormal.P0EFTGrowthMasterBranchExport

namespace JanusFormal
namespace P0EFTObservationalFSigma8Data

set_option autoImplicit false

structure ObservationalFSigma8Data where
  sdssDR16LikelihoodFilesFetched : Prop
  fsigma8PointsExtracted : Prop
  covarianceDiagonalErrorsExtracted : Prop
  desiFSigma8TableLoaded : Prop
  planckAmplitudePriorLoaded : Prop
  likelihoodReady : Prop

def sdssFSigma8Ready (d : ObservationalFSigma8Data) : Prop :=
  d.sdssDR16LikelihoodFilesFetched /\
  d.fsigma8PointsExtracted /\
  d.covarianceDiagonalErrorsExtracted

def surveyLikelihoodReady (d : ObservationalFSigma8Data) : Prop :=
  sdssFSigma8Ready d /\
  d.desiFSigma8TableLoaded /\
  d.planckAmplitudePriorLoaded /\
  d.likelihoodReady

theorem sdss_files_give_local_fsigma8_points
    (d : ObservationalFSigma8Data)
    (hFiles : d.sdssDR16LikelihoodFilesFetched)
    (hPoints : d.fsigma8PointsExtracted)
    (hErrors : d.covarianceDiagonalErrorsExtracted) :
    sdssFSigma8Ready d := by
  exact And.intro hFiles (And.intro hPoints hErrors)

theorem missing_desi_blocks_full_survey_likelihood
    (d : ObservationalFSigma8Data)
    (hMissing : Not d.desiFSigma8TableLoaded) :
    Not (surveyLikelihoodReady d) := by
  intro h
  exact hMissing h.right.left

end P0EFTObservationalFSigma8Data
end JanusFormal
