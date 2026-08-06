import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D

/-!
# Public namespace facade for the terminal Candidate-A boundary chain

The H10 gates live primarily in the Candidate-A fiber-substitution namespace,
while their geometric input types are defined in the pre-existing quotient,
metric, displacement and graph modules.  This file exports only transparent
API aliases into the H10 namespace so imported downstream gates resolve the
same vocabulary without repeating file-scoped `open` commands.  It introduces
no definition, instance, hypothesis, geometric datum or axiom.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D

export P0EFTJanusMappingTorusCutThroatBoundaryDoubleCover4D
  (CutThroatBoundary)
export P0EFTJanusProgramPGlobalFieldSpace4D
  (GlobalFieldConfiguration)
export P0EFTJanusMappingTorusGeneralLorentzTensor4D
  (SmoothSymmetricCovariantTwoTensor)
export P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
  (SmoothGeneralLorentzMetric)
export P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
  (RegularGeneralLorentzMetric)
export P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
  (HasNoTangentialRadical)
export P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
  (SmoothHolonomicFrameChart4)
export P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
  (finiteSmoothThroatGeneratingFrame)
export P0EFTJanusD8NormalBundleD9DisplacementBridge4D
  (SmoothNormalDisplacement)
export P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
  (NormalGraphNonNullAt)

end P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
end JanusFormal
