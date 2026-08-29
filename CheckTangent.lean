import ScratchHessianGauss

#check IsLocalDiffeomorph.mfderiv_injective
#check IsLocalDiffeomorph.mfderiv_bijective
#check IsLocalDiffeomorph.mfderivToContinuousLinearEquiv
#check IsLocalDiffeomorph.mfderivToContinuousLinearEquiv_coe
#check tangentModelSpaceEquiv

example (x v : Real) : TangentSpace (modelWithCornersSelf Real Real) x := v

example
    (x v : JanusFormal.P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D.Vector4) :
    TangentSpace
      (modelWithCornersSelf Real
        JanusFormal.P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D.Vector4)
      x := v

example
    (x : JanusFormal.P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D.Vector4)
    (v : JanusFormal.P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4) :
    TangentSpace
      (modelWithCornersSelf Real
        JanusFormal.P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D.Vector4)
      x := v
