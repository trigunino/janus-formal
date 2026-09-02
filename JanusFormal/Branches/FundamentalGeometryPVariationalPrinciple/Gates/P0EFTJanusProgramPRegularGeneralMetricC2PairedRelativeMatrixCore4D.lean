import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalRelativeMetricCoreProjection4D

/-!
# C² paired relative-metric matrix core

The plus-sector identity root transports the fixed-plus representation of the
relative metric by the exact algebraic sandwich `S * C * S`.  This file proves
that the resulting completed C² matrix is C²-smooth on an open domain.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2PairedRelativeMatrixCore4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 4000000

noncomputable section

open Set
open scoped Manifold ContDiff Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootLift4D
open P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootInverseCore4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalRelativeMetricCoreProjection4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev C2Scalar :=
  CanonicalPhysicalScalarC2JetCore period hPeriod

private abbrev C2Matrix :=
  C2FiniteMatrix period hPeriod 4

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance c2ScalarNormedAddCommGroup :
    NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule
    period hPeriod).normedAddCommGroup

local instance c2ScalarNormedSpace :
    NormedSpace Real (C2Scalar period hPeriod) :=
  inferInstance

local instance c2ScalarCompleteSpace :
    CompleteSpace (C2Scalar period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod

/-- Core parameters for which the plus-sector identity root is available and
invertible in the completed C² matrix algebra. -/
def regularGeneralMetricC2PairedRelativeMatrixDomain
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod) :
    Set (RegularGeneralMetricC2PairedRelativeCore
      period hPeriod plusBase minusBase) :=
  (fun core => core.2.1) ⁻¹'
    c2IdentityRootInvertiblePerturbationDomain period hPeriod

theorem regularGeneralMetricC2PairedRelativeMatrixDomain_isOpen
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod) :
    IsOpen (regularGeneralMetricC2PairedRelativeMatrixDomain
      period hPeriod plusBase minusBase) := by
  exact (c2IdentityRootInvertiblePerturbationDomain_isOpen
    period hPeriod).preimage (continuous_fst.comp continuous_snd)

theorem zero_mem_regularGeneralMetricC2PairedRelativeMatrixDomain
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod) :
    (0 : RegularGeneralMetricC2PairedRelativeCore
      period hPeriod plusBase minusBase) ∈
      regularGeneralMetricC2PairedRelativeMatrixDomain
        period hPeriod plusBase minusBase := by
  exact zero_mem_c2IdentityRootInvertiblePerturbationDomain
    period hPeriod

/-- Completed C² relative matrix in the varied plus frame. -/
def regularGeneralMetricC2PairedRelativeMatrix
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (core : RegularGeneralMetricC2PairedRelativeCore
      period hPeriod plusBase minusBase) :
    C2Matrix period hPeriod :=
  let inverseRoot :=
    regularGeneralMetricC2IdentityRootInverseC2Matrix
      period hPeriod core.2.1
  let relativeMatrix :=
    regularGeneralMetricC2VariationMatrix period hPeriod plusBase
        (minusBase.metric.tensor - plusBase.metric.tensor) +
      core.2.2
  c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) 4
    inverseRoot
    (c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) 4
      relativeMatrix inverseRoot)

/-- The exact relative-matrix sandwich is C² on its open root domain. -/
theorem regularGeneralMetricC2PairedRelativeMatrix_contDiffOn
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod) :
    ContDiffOn Real 2
      (regularGeneralMetricC2PairedRelativeMatrix
        period hPeriod plusBase minusBase)
      (regularGeneralMetricC2PairedRelativeMatrixDomain
        period hPeriod plusBase minusBase) := by
  let domain := regularGeneralMetricC2PairedRelativeMatrixDomain
    period hPeriod plusBase minusBase
  let inverseRoot := fun core : RegularGeneralMetricC2PairedRelativeCore
      period hPeriod plusBase minusBase =>
    regularGeneralMetricC2IdentityRootInverseC2Matrix
      period hPeriod core.2.1
  let relativeMatrix := fun core : RegularGeneralMetricC2PairedRelativeCore
      period hPeriod plusBase minusBase =>
    regularGeneralMetricC2VariationMatrix period hPeriod plusBase
        (minusBase.metric.tensor - plusBase.metric.tensor) +
      core.2.2
  let multiply := fun pair : C2Matrix period hPeriod × C2Matrix period hPeriod =>
    c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) 4
      pair.1 pair.2
  have hPlus : ContDiffOn Real 2
      (fun core : RegularGeneralMetricC2PairedRelativeCore
        period hPeriod plusBase minusBase => core.2.1) domain :=
    (contDiff_fst.comp contDiff_snd).contDiffOn
  have hInverseRoot : ContDiffOn Real 2 inverseRoot domain :=
    (regularGeneralMetricC2IdentityRootInverseC2Matrix_contDiffOn
      period hPeriod).comp hPlus (fun _ hCore => hCore)
  have hRelativeMatrix : ContDiffOn Real 2 relativeMatrix domain :=
    (contDiff_const.add
      (contDiff_snd.comp contDiff_snd)).contDiffOn
  have hMultiplySmooth : ContDiff Real ∞ multiply :=
    ((c2FiniteMatrixProduct
      (period := period) (hPeriod := hPeriod) 4).contDiff.comp
        contDiff_fst).clm_apply contDiff_snd
  have hMultiply : ContDiff Real 2 multiply :=
    hMultiplySmooth.of_le
      (show (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω) by
        exact WithTop.coe_le_coe.mpr le_top)
  have hRight : ContDiffOn Real 2
      (fun core => multiply (relativeMatrix core, inverseRoot core)) domain :=
    hMultiply.contDiffOn.comp
      (hRelativeMatrix.prodMk hInverseRoot) (fun _ _ => mem_univ _)
  have hSandwich : ContDiffOn Real 2
      (fun core => multiply
        (inverseRoot core, multiply (relativeMatrix core, inverseRoot core)))
      domain :=
    hMultiply.contDiffOn.comp
      (hInverseRoot.prodMk hRight) (fun _ _ => mem_univ _)
  change ContDiffOn Real 2
    (fun core : RegularGeneralMetricC2PairedRelativeCore
        period hPeriod plusBase minusBase =>
      c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) 4
        (regularGeneralMetricC2IdentityRootInverseC2Matrix
          period hPeriod core.2.1)
        (c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) 4
          (regularGeneralMetricC2VariationMatrix period hPeriod plusBase
              (minusBase.metric.tensor - plusBase.metric.tensor) +
            core.2.2)
          (regularGeneralMetricC2IdentityRootInverseC2Matrix
            period hPeriod core.2.1)))
    (regularGeneralMetricC2PairedRelativeMatrixDomain
      period hPeriod plusBase minusBase)
  simpa only [inverseRoot, relativeMatrix, multiply, domain] using hSandwich

/-- Gate marker: the full paired relative matrix has an open C² core. -/
theorem regular_general_metric_c2_paired_relative_matrix_core_gate
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod) :
    IsOpen (regularGeneralMetricC2PairedRelativeMatrixDomain
        period hPeriod plusBase minusBase) ∧
      (0 : RegularGeneralMetricC2PairedRelativeCore
        period hPeriod plusBase minusBase) ∈
          regularGeneralMetricC2PairedRelativeMatrixDomain
            period hPeriod plusBase minusBase ∧
      ContDiffOn Real 2
        (regularGeneralMetricC2PairedRelativeMatrix
          period hPeriod plusBase minusBase)
        (regularGeneralMetricC2PairedRelativeMatrixDomain
          period hPeriod plusBase minusBase) := by
  exact ⟨
    regularGeneralMetricC2PairedRelativeMatrixDomain_isOpen
      period hPeriod plusBase minusBase,
    zero_mem_regularGeneralMetricC2PairedRelativeMatrixDomain
      period hPeriod plusBase minusBase,
    regularGeneralMetricC2PairedRelativeMatrix_contDiffOn
      period hPeriod plusBase minusBase⟩

end

end P0EFTJanusProgramPRegularGeneralMetricC2PairedRelativeMatrixCore4D
end JanusFormal
