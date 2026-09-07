import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGaugeC2AbelianOffShellGraphBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGaugeCoefficientRecenterRootTransport4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedGaugeCoefficientMaxwellAction4D

/-! # The mobile physical potential in fixed-frame L² coordinates

The initial coefficients plus the physical direction are transported from
each moving Lorentz frame to its fixed base frame.  Bounded reconstruction
then gives the very same intrinsic potentials as the paired action datum.
This is a joint C² potential map.  It does not identify fixed-metric Lorenz
gauge fixing with gauge fixing at the mobile physical metric.
-/

namespace JanusFormal
namespace P0EFTJanusPairedMobileGaugeSamePotentialL2Input4D

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option synthInstance.maxHeartbeats 600000

noncomputable section

open Set
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2IdentityRootBranch4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalAbelianLorenzGraphRiesz4D
open P0EFTJanusProgramPGlobalGaugeTangentIntrinsicEmbedding4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootLift4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartRegularMetric4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalMetricGaugeCoreProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily4D
open P0EFTJanusProgramPRegularGeneralMetricC2GaugeCoefficientFrameTransport4D
open P0EFTJanusProgramPRegularGeneralMetricC2GaugeCoefficientMaxwellAction4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedGaugeCoefficientMaxwellAction4D
open P0EFTJanusProgramPRegularFrameGaugePotentialReconstruction4D
open P0EFTJanusGaugeCoefficientRecenterRootTransport4D
open P0EFTJanusGaugeC2AbelianOffShellGraphBridge4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
private abbrev C2Scalar := CanonicalPhysicalScalarC2JetCore period hPeriod

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod
local instance : NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (C2Scalar period hPeriod) := inferInstance
local instance : NormedSpace Real (GlobalPairedAbelianPotentialL2 period hPeriod) :=
  (inferInstance : InnerProductSpace Real
    (GlobalPairedAbelianPotentialL2 period hPeriod)).toNormedSpace
local instance : Module Real (GlobalPairedAbelianPotentialL2 period hPeriod) :=
  (inferInstance : InnerProductSpace Real
    (GlobalPairedAbelianPotentialL2 period hPeriod)).toNormedSpace.toModule

private theorem mobileTransport_reconstructed
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (variation : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hVariation : regularGeneralMetricSmoothC2Variation period hPeriod metric variation ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric)
    (coefficients : SmoothQuotientField period hPeriod GaugeFiber) :
    regularGeneralMetricC2MobileGaugeCoefficientTransport period hPeriod metric
        (regularGeneralMetricSmoothC2Variation period hPeriod metric variation)
        (smoothGaugeCoefficientC2CoreLinearMap period hPeriod coefficients) =
      smoothGaugeCoefficientC2CoreLinearMap period hPeriod
        (gaugePotentialFrameCoefficients period hPeriod metric
          (regularFrameGaugePotentialFromCoefficients period hPeriod
            (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod
              metric variation hVariation) coefficients)) := by
  change gaugeCoefficientC2CoreFrameTransport period hPeriod
    (c2IdentityRootBranch period hPeriod
      (regularGeneralMetricC2VariationMatrix period hPeriod metric variation))
    (smoothGaugeCoefficientC2CoreLinearMap period hPeriod coefficients) = _
  exact gaugeCoefficientC2CoreFrameTransport_reconstructed period hPeriod
    metric variation hVariation coefficients

variable (configuration : GlobalFieldConfiguration period hPeriod)
  (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)

/-- Total moving-frame coefficients, re-expressed in the fixed base frames. -/
def pairedMobileGaugeC2Input
    (core : RegularGeneralMetricC2PairedMetricGaugeCore period hPeriod plusBase minusBase) :
    RegularGeneralMetricC2PairedGaugeCoefficientCore period hPeriod :=
  (let input := regularGeneralMetricC2PairedPlusGaugeCoefficientInput
      period hPeriod configuration plusBase minusBase core
   regularGeneralMetricC2MobileGaugeCoefficientTransport
     period hPeriod plusBase input.1 input.2,
   let input := regularGeneralMetricC2PairedMinusGaugeCoefficientInput
      period hPeriod configuration plusBase minusBase core
   regularGeneralMetricC2MobileGaugeCoefficientTransport
     period hPeriod minusBase input.1 input.2)

theorem pairedMobileGaugeC2Input_contDiffOn_two :
    ContDiffOn Real 2
      (pairedMobileGaugeC2Input period hPeriod configuration plusBase minusBase)
      (regularGeneralMetricC2PairedMetricGaugeMaxwellDomain period hPeriod
        plusBase minusBase) := by
  have hPlus :=
    (regularGeneralMetricC2MobileGaugeCoefficientTransport_contDiffOn_two
      period hPeriod plusBase).comp
      (regularGeneralMetricC2PairedPlusGaugeCoefficientInput_contDiffOn_two
        period hPeriod configuration plusBase minusBase)
      (fun _ hCore => regularGeneralMetricC2PairedPlusGaugeCoefficientInput_mem
        period hPeriod configuration plusBase minusBase hCore)
  have hMinus :=
    (regularGeneralMetricC2MobileGaugeCoefficientTransport_contDiffOn_two
      period hPeriod minusBase).comp
      (regularGeneralMetricC2PairedMinusGaugeCoefficientInput_contDiffOn_two
        period hPeriod configuration plusBase minusBase)
      (fun _ hCore => regularGeneralMetricC2PairedMinusGaugeCoefficientInput_mem
        period hPeriod configuration plusBase minusBase hCore)
  exact hPlus.prodMk hMinus

/-- The physical potential in fixed-frame L² coordinates, including its base value. -/
def pairedMobileGaugePotentialL2Input
    (core : RegularGeneralMetricC2PairedMetricGaugeCore period hPeriod plusBase minusBase) :
    GlobalPairedAbelianPotentialL2 period hPeriod :=
  pairedGaugeC2PotentialL2 period hPeriod
    (fun | .plus => plusBase | .minus => minusBase)
    (pairedMobileGaugeC2Input period hPeriod configuration plusBase minusBase core)

theorem pairedMobileGaugePotentialL2Input_contDiffOn_two :
    ContDiffOn Real 2
      (pairedMobileGaugePotentialL2Input period hPeriod configuration plusBase minusBase)
      (regularGeneralMetricC2PairedMetricGaugeMaxwellDomain period hPeriod
        plusBase minusBase) := by
  have hProjection : ContDiff Real 2
      (pairedGaugeC2PotentialL2 period hPeriod
        (fun | .plus => plusBase | .minus => minusBase)) :=
    (pairedGaugeC2PotentialL2 period hPeriod
      (fun | .plus => plusBase | .minus => minusBase)).contDiff
  exact hProjection.contDiffOn.comp
    (pairedMobileGaugeC2Input_contDiffOn_two period hPeriod
      configuration plusBase minusBase) (fun _ _ => Set.mem_univ _)

/-- The smooth total potential reconstructed in the actual mobile frames. -/
def pairedMobileGaugePotentialAt
    (direction : GlobalMinimalPhysicalFieldTangent period hPeriod configuration)
    (hDirection : direction ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration plusBase minusBase) :
    Sector → SmoothAbelianGaugePotential period hPeriod
  | .plus => regularFrameGaugePotentialFromCoefficients period hPeriod
      (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod plusBase
        (direction.1.completeVariation.fullMetricPerturbation .plus) hDirection.plus_mem)
      (configuration.coefficientFields.gauge.1 +
        direction.1.completeVariation.independent.gauge.1)
  | .minus => regularFrameGaugePotentialFromCoefficients period hPeriod
      (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod minusBase
        (direction.1.completeVariation.fullMetricPerturbation .minus) hDirection.minus_mem)
      (configuration.coefficientFields.gauge.2 +
        direction.1.completeVariation.independent.gauge.2)

/-- The completed packet is the actual mobile potential read in the fixed base frames. -/
theorem pairedMobileGaugeC2Input_projected
    (direction : GlobalMinimalPhysicalFieldTangent period hPeriod configuration)
    (hDirection : direction ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration plusBase minusBase) :
    pairedMobileGaugeC2Input period hPeriod configuration plusBase minusBase
        (globalMinimalPhysicalPairedMetricGaugeCoreLinearMap period hPeriod
          configuration plusBase minusBase direction) =
      (smoothGaugeCoefficientC2CoreLinearMap period hPeriod
        (gaugePotentialFrameCoefficients period hPeriod plusBase
          (pairedMobileGaugePotentialAt period hPeriod configuration plusBase minusBase
            direction hDirection .plus)),
       smoothGaugeCoefficientC2CoreLinearMap period hPeriod
        (gaugePotentialFrameCoefficients period hPeriod minusBase
          (pairedMobileGaugePotentialAt period hPeriod configuration plusBase minusBase
            direction hDirection .minus))) := by
  unfold pairedMobileGaugeC2Input
  rw [regularGeneralMetricC2PairedPlusGaugeCoefficientInput_projected,
    regularGeneralMetricC2PairedMinusGaugeCoefficientInput_projected]
  dsimp only
  apply Prod.ext
  · exact mobileTransport_reconstructed period hPeriod plusBase
      (direction.1.completeVariation.fullMetricPerturbation .plus) hDirection.plus_mem _
  · exact mobileTransport_reconstructed period hPeriod minusBase
      (direction.1.completeVariation.fullMetricPerturbation .minus) hDirection.minus_mem _

/-- Transport changes the coefficient frame while preserving the intrinsic potential. -/
theorem pairedMobileGaugePotentialL2Input_projected
    (direction : GlobalMinimalPhysicalFieldTangent period hPeriod configuration)
    (hDirection : direction ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration plusBase minusBase) :
    pairedMobileGaugePotentialL2Input period hPeriod configuration plusBase minusBase
        (globalMinimalPhysicalPairedMetricGaugeCoreLinearMap period hPeriod
          configuration plusBase minusBase direction) =
      globalPairedAbelianPotentialL2LinearMap period hPeriod
        (pairedMobileGaugePotentialAt period hPeriod configuration plusBase minusBase
          direction hDirection) := by
  unfold pairedMobileGaugePotentialL2Input
  rw [pairedMobileGaugeC2Input_projected period hPeriod configuration
      plusBase minusBase direction hDirection,
    pairedGaugeC2PotentialL2_smooth]
  apply congrArg (globalPairedAbelianPotentialL2LinearMap period hPeriod)
  funext sector
  cases sector <;>
    exact regularFrameGaugePotentialFromCoefficients_frameCoefficients period hPeriod _ _

/-- The L² input is exactly the Maxwell potential carried by the action datum. -/
theorem pairedMobileGaugePotentialL2Input_eq_datumAt
    (couplings : GlobalCandidateAActionCouplings)
    {NonNullFace NullFace : Type*} [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (direction : GlobalMinimalPhysicalFieldTangent period hPeriod configuration)
    (hDirection : direction ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration plusBase minusBase) :
    pairedMobileGaugePotentialL2Input period hPeriod configuration plusBase minusBase
        (globalMinimalPhysicalPairedMetricGaugeCoreLinearMap period hPeriod
          configuration plusBase minusBase direction) =
      globalPairedAbelianPotentialL2LinearMap period hPeriod
        (globalCandidateAPotentialBySector period hPeriod
          ((regularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily
            period hPeriod configuration couplings data plusBase minusBase).datumAt
              direction hDirection).2) := by
  rw [pairedMobileGaugePotentialL2Input_projected period hPeriod
    configuration plusBase minusBase direction hDirection]
  apply congrArg (globalPairedAbelianPotentialL2LinearMap period hPeriod)
  funext sector
  cases sector <;> rfl

/-- Gate 631: a joint C² input reconstructs the same mobile total potential. -/
theorem paired_mobile_gauge_same_potential_l2_input_gate
    (direction : GlobalMinimalPhysicalFieldTangent period hPeriod configuration)
    (hDirection : direction ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration plusBase minusBase) :
    ContDiffOn Real 2
        (pairedMobileGaugePotentialL2Input period hPeriod configuration plusBase minusBase)
        (regularGeneralMetricC2PairedMetricGaugeMaxwellDomain period hPeriod
          plusBase minusBase) ∧
      pairedMobileGaugePotentialL2Input period hPeriod configuration plusBase minusBase
          (globalMinimalPhysicalPairedMetricGaugeCoreLinearMap period hPeriod
            configuration plusBase minusBase direction) =
        globalPairedAbelianPotentialL2LinearMap period hPeriod
          (pairedMobileGaugePotentialAt period hPeriod configuration plusBase minusBase
            direction hDirection) :=
  ⟨pairedMobileGaugePotentialL2Input_contDiffOn_two period hPeriod
      configuration plusBase minusBase,
    pairedMobileGaugePotentialL2Input_projected period hPeriod
      configuration plusBase minusBase direction hDirection⟩

end
end P0EFTJanusPairedMobileGaugeSamePotentialL2Input4D
end JanusFormal
