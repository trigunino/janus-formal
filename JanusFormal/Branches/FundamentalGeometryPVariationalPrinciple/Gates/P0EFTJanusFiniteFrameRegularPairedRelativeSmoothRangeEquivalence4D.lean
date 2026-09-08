import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameRegularPairedRelativeSmoothGraph4D

/-! # Equivalence of the finite-frame and regular paired-relative smooth ranges -/

namespace JanusFormal
namespace P0EFTJanusFiniteFrameRegularPairedRelativeSmoothRangeEquivalence4D

set_option autoImplicit false
noncomputable section
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootLift4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalMetricCoreProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalRelativeMetricCoreProjection4D
open P0EFTJanusFiniteFrameRegularPairedRelativeSmoothCoreBridge4D
open P0EFTJanusFiniteFrameRegularPairedRelativeSmoothGraph4D

variable (period : Real) (hPeriod : period ≠ 0)
variable (frame : SmoothD8Frame period hPeriod)
  (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)

private abbrev FinitePair :=
  GeneralMetricRelativeC2Core period hPeriod frame plusBase.metric ×
    GeneralMetricRelativeC2Core period hPeriod frame plusBase.metric
private abbrev RegularRelative :=
  RegularGeneralMetricC2PairedRelativeCore period hPeriod plusBase minusBase
private abbrev SmoothGraph :=
  finiteFrameRegularPairedRelativeSmoothGraph period hPeriod frame plusBase minusBase

/-- Finite-frame projection of the common smooth graph. -/
def finiteFrameRegularPairedRelativeSmoothGraphToFinite :
    SmoothGraph period hPeriod frame plusBase minusBase →ₗ[Real]
      FinitePair period hPeriod frame plusBase where
  toFun pair := pair.1.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Regular paired-relative projection of the common smooth graph. -/
def finiteFrameRegularPairedRelativeSmoothGraphToRegular :
    SmoothGraph period hPeriod frame plusBase minusBase →ₗ[Real]
      RegularRelative period hPeriod plusBase minusBase where
  toFun pair := pair.1.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Smooth finite-frame directions which have a regular representative. -/
def finiteFrameRegularPairedRelativeFiniteSmoothRange :
    Submodule Real (FinitePair period hPeriod frame plusBase) :=
  LinearMap.range
    (finiteFrameRegularPairedRelativeSmoothGraphToFinite period hPeriod frame plusBase minusBase)

/-- Smooth regular directions which have a finite-frame representative. -/
def finiteFrameRegularPairedRelativeRegularSmoothRange :
    Submodule Real (RegularRelative period hPeriod plusBase minusBase) :=
  LinearMap.range
    (finiteFrameRegularPairedRelativeSmoothGraphToRegular period hPeriod frame plusBase minusBase)

/-- The common graph identifies with its finite-frame smooth range. -/
def finiteFrameRegularPairedRelativeSmoothGraphFiniteEquiv :
    SmoothGraph period hPeriod frame plusBase minusBase ≃ₗ[Real]
      finiteFrameRegularPairedRelativeFiniteSmoothRange period hPeriod frame plusBase minusBase :=
  LinearEquiv.ofInjective
    (finiteFrameRegularPairedRelativeSmoothGraphToFinite period hPeriod frame plusBase minusBase)
    (finiteFrameRegularPairedRelativeSmoothGraph_finite_injective period hPeriod frame plusBase
      minusBase)

/-- The common graph identifies with its regular paired-relative smooth range. -/
def finiteFrameRegularPairedRelativeSmoothGraphRegularEquiv :
    SmoothGraph period hPeriod frame plusBase minusBase ≃ₗ[Real]
      finiteFrameRegularPairedRelativeRegularSmoothRange period hPeriod frame plusBase minusBase :=
  LinearEquiv.ofInjective
    (finiteFrameRegularPairedRelativeSmoothGraphToRegular period hPeriod frame plusBase minusBase)
    (finiteFrameRegularPairedRelativeSmoothGraph_regular_injective period hPeriod frame plusBase
      minusBase)

@[simp]
theorem finiteFrameRegularPairedRelativeSmoothGraphFiniteEquiv_coe
    (pair : SmoothGraph period hPeriod frame plusBase minusBase) :
    ↑(finiteFrameRegularPairedRelativeSmoothGraphFiniteEquiv period hPeriod frame plusBase minusBase
      pair) = pair.1.1 :=
  rfl

@[simp]
theorem finiteFrameRegularPairedRelativeSmoothGraphRegularEquiv_coe
    (pair : SmoothGraph period hPeriod frame plusBase minusBase) :
    ↑(finiteFrameRegularPairedRelativeSmoothGraphRegularEquiv period hPeriod frame plusBase minusBase
      pair) = pair.1.2 :=
  rfl

/-- Canonical linear identification of the two smooth ranges. -/
def finiteFrameRegularPairedRelativeSmoothRangeEquiv :
    finiteFrameRegularPairedRelativeFiniteSmoothRange period hPeriod frame plusBase minusBase ≃ₗ[Real]
      finiteFrameRegularPairedRelativeRegularSmoothRange period hPeriod frame plusBase minusBase :=
  (finiteFrameRegularPairedRelativeSmoothGraphFiniteEquiv period hPeriod frame plusBase minusBase).symm.trans
    (finiteFrameRegularPairedRelativeSmoothGraphRegularEquiv period hPeriod frame plusBase minusBase)

/-- The range equivalence sends both projections of a graph element to each other. -/
theorem finiteFrameRegularPairedRelativeSmoothRangeEquiv_apply_graph
    (pair : SmoothGraph period hPeriod frame plusBase minusBase) :
    finiteFrameRegularPairedRelativeSmoothRangeEquiv period hPeriod frame plusBase minusBase
        (finiteFrameRegularPairedRelativeSmoothGraphFiniteEquiv period hPeriod frame plusBase minusBase
          pair) =
      finiteFrameRegularPairedRelativeSmoothGraphRegularEquiv period hPeriod frame plusBase minusBase
        pair := by
  simp [finiteFrameRegularPairedRelativeSmoothRangeEquiv]

/-- The inverse range equivalence recovers the finite-frame projection. -/
theorem finiteFrameRegularPairedRelativeSmoothRangeEquiv_symm_apply_graph
    (pair : SmoothGraph period hPeriod frame plusBase minusBase) :
    (finiteFrameRegularPairedRelativeSmoothRangeEquiv period hPeriod frame plusBase minusBase).symm
        (finiteFrameRegularPairedRelativeSmoothGraphRegularEquiv period hPeriod frame plusBase minusBase
          pair) =
      finiteFrameRegularPairedRelativeSmoothGraphFiniteEquiv period hPeriod frame plusBase minusBase
        pair := by
  simp [finiteFrameRegularPairedRelativeSmoothRangeEquiv]

end
end P0EFTJanusFiniteFrameRegularPairedRelativeSmoothRangeEquivalence4D
end JanusFormal
