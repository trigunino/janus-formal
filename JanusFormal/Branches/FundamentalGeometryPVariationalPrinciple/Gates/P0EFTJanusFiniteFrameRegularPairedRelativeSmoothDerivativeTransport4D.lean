import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameRegularPairedRelativeSmoothRangeEquivalence4D

/-! # Transport of derivatives across the finite-frame/regular smooth bridge -/

namespace JanusFormal
namespace P0EFTJanusFiniteFrameRegularPairedRelativeSmoothDerivativeTransport4D

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1200000
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
open P0EFTJanusFiniteFrameRegularPairedRelativeSmoothRangeEquivalence4D

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
private abbrev FiniteRange :=
  finiteFrameRegularPairedRelativeFiniteSmoothRange period hPeriod frame plusBase minusBase
private abbrev RegularRange :=
  finiteFrameRegularPairedRelativeRegularSmoothRange period hPeriod frame plusBase minusBase

/-- Restriction of a finite-frame derivative to the common smooth range. -/
def finiteFrameRegularPairedRelativeFiniteDerivativeRestriction
    (derivative : FinitePair period hPeriod frame plusBase →ₗ[Real] Real) :
    FiniteRange period hPeriod frame plusBase minusBase →ₗ[Real] Real :=
  derivative.comp (Submodule.subtype _)

/-- Restriction of a regular paired-relative derivative to the common smooth range. -/
def finiteFrameRegularPairedRelativeRegularDerivativeRestriction
    (derivative : RegularRelative period hPeriod plusBase minusBase →ₗ[Real] Real) :
    RegularRange period hPeriod frame plusBase minusBase →ₗ[Real] Real :=
  derivative.comp (Submodule.subtype _)

/-- Two derivatives are compatible when they agree on every common smooth representative. -/
def finiteFrameRegularPairedRelativeSmoothDerivativeCompatible
    (finiteDerivative : FinitePair period hPeriod frame plusBase →ₗ[Real] Real)
    (regularDerivative : RegularRelative period hPeriod plusBase minusBase →ₗ[Real] Real) : Prop :=
  ∀ pair : SmoothGraph period hPeriod frame plusBase minusBase,
    finiteDerivative pair.1.1 = regularDerivative pair.1.2

/-- Compatibility is exactly equality after transport between the two smooth ranges. -/
theorem finiteFrameRegularPairedRelativeSmoothDerivativeCompatible_iff_restrictions
    (finiteDerivative : FinitePair period hPeriod frame plusBase →ₗ[Real] Real)
    (regularDerivative : RegularRelative period hPeriod plusBase minusBase →ₗ[Real] Real) :
    finiteFrameRegularPairedRelativeSmoothDerivativeCompatible period hPeriod frame plusBase minusBase
        finiteDerivative regularDerivative ↔
      finiteFrameRegularPairedRelativeFiniteDerivativeRestriction period hPeriod frame plusBase
          minusBase finiteDerivative =
        (finiteFrameRegularPairedRelativeRegularDerivativeRestriction period hPeriod frame plusBase
          minusBase regularDerivative).comp
          (finiteFrameRegularPairedRelativeSmoothRangeEquiv period hPeriod frame plusBase minusBase).toLinearMap := by
  constructor
  · intro hCompatible
    apply LinearMap.ext
    intro finitePoint
    obtain ⟨pair, rfl⟩ :=
      (finiteFrameRegularPairedRelativeSmoothGraphFiniteEquiv period hPeriod frame plusBase minusBase).surjective
        finitePoint
    change finiteDerivative
        ↑(finiteFrameRegularPairedRelativeSmoothGraphFiniteEquiv period hPeriod frame plusBase minusBase
          pair) =
      regularDerivative
        ↑(finiteFrameRegularPairedRelativeSmoothRangeEquiv period hPeriod frame plusBase minusBase
          (finiteFrameRegularPairedRelativeSmoothGraphFiniteEquiv period hPeriod frame plusBase minusBase
            pair))
    rw [finiteFrameRegularPairedRelativeSmoothRangeEquiv_apply_graph]
    simpa using hCompatible pair
  · intro hRestrictions pair
    have hAt := LinearMap.congr_fun hRestrictions
      (finiteFrameRegularPairedRelativeSmoothGraphFiniteEquiv period hPeriod frame plusBase minusBase
        pair)
    change finiteDerivative
        ↑(finiteFrameRegularPairedRelativeSmoothGraphFiniteEquiv period hPeriod frame plusBase minusBase
          pair) =
      regularDerivative
        ↑(finiteFrameRegularPairedRelativeSmoothRangeEquiv period hPeriod frame plusBase minusBase
          (finiteFrameRegularPairedRelativeSmoothGraphFiniteEquiv period hPeriod frame plusBase minusBase
            pair)) at hAt
    rw [finiteFrameRegularPairedRelativeSmoothRangeEquiv_apply_graph] at hAt
    simpa using hAt

/-- Compatible derivatives vanish on one smooth range exactly when they vanish on the other. -/
theorem finiteFrameRegularPairedRelativeSmoothDerivative_zero_iff
    (finiteDerivative : FinitePair period hPeriod frame plusBase →ₗ[Real] Real)
    (regularDerivative : RegularRelative period hPeriod plusBase minusBase →ₗ[Real] Real)
    (hCompatible : finiteFrameRegularPairedRelativeSmoothDerivativeCompatible period hPeriod frame
      plusBase minusBase finiteDerivative regularDerivative) :
    finiteFrameRegularPairedRelativeFiniteDerivativeRestriction period hPeriod frame plusBase minusBase
        finiteDerivative = 0 ↔
      finiteFrameRegularPairedRelativeRegularDerivativeRestriction period hPeriod frame plusBase
        minusBase regularDerivative = 0 := by
  have hRestrictions :=
    (finiteFrameRegularPairedRelativeSmoothDerivativeCompatible_iff_restrictions period hPeriod frame
      plusBase minusBase finiteDerivative regularDerivative).mp hCompatible
  constructor
  · intro hFinite
    apply LinearMap.ext
    intro regularPoint
    obtain ⟨finitePoint, rfl⟩ :=
      (finiteFrameRegularPairedRelativeSmoothRangeEquiv period hPeriod frame plusBase minusBase).surjective
        regularPoint
    have hAt := LinearMap.congr_fun hRestrictions finitePoint
    rw [hFinite] at hAt
    simpa using hAt.symm
  · intro hRegular
    apply LinearMap.ext
    intro finitePoint
    have hAt := LinearMap.congr_fun hRestrictions finitePoint
    rw [hRegular] at hAt
    simpa using hAt

end
end P0EFTJanusFiniteFrameRegularPairedRelativeSmoothDerivativeTransport4D
end JanusFormal
