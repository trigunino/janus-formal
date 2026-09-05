import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixInverseDerivative4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedRelativeMatrixCore4D

/-! # Exact derivative of the paired C² relative-matrix sandwich -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2PairedRelativeMatrixDerivative4D

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 600000

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
open P0EFTJanusMappingTorusCanonicalPhysicalC2IdentityRootBranch4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2IdentityRootDerivative4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixInverseDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootLift4D
open P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootInverseCore4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalMetricCoreProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalRelativeMetricCoreProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedRelativeMatrixCore4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace
  UniformSpace.toTopologicalSpace

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev C2Scalar :=
  CanonicalPhysicalScalarC2JetCore period hPeriod

private abbrev C2Matrix :=
  C2FiniteMatrix period hPeriod 4

private abbrev RelativeCore
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod) :=
  RegularGeneralMetricC2PairedRelativeCore
    period hPeriod plusBase minusBase

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

@[reducible] private local instance c2MatrixNormedAddCommGroup :
    NormedAddCommGroup (C2Matrix period hPeriod) :=
  inferInstance

@[reducible] private local instance c2MatrixAddCommGroup :
    AddCommGroup (C2Matrix period hPeriod) :=
  c2MatrixNormedAddCommGroup period hPeriod |>.toAddCommGroup

@[reducible] private local instance c2MatrixPseudoMetricSpace :
    PseudoMetricSpace (C2Matrix period hPeriod) :=
  c2MatrixNormedAddCommGroup period hPeriod |>.toPseudoMetricSpace

@[reducible] private local instance c2MatrixUniformSpace :
    UniformSpace (C2Matrix period hPeriod) :=
  c2MatrixPseudoMetricSpace period hPeriod |>.toUniformSpace

@[reducible] private local instance c2MatrixTopologicalSpace :
    TopologicalSpace (C2Matrix period hPeriod) :=
  c2MatrixUniformSpace period hPeriod |>.toTopologicalSpace

@[reducible] private local instance c2MatrixNormedSpace :
    NormedSpace Real (C2Matrix period hPeriod) :=
  inferInstance

@[reducible] private local instance c2MatrixModule :
    Module Real (C2Matrix period hPeriod) :=
  c2MatrixNormedSpace period hPeriod |>.toModule

@[reducible] private local instance relativeCoreNormedAddCommGroup
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod) :
    NormedAddCommGroup
      (RelativeCore period hPeriod plusBase minusBase) :=
  inferInstance

@[reducible] private local instance relativeCoreAddCommGroup
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod) :
    AddCommGroup (RelativeCore period hPeriod plusBase minusBase) :=
  relativeCoreNormedAddCommGroup period hPeriod plusBase minusBase
    |>.toAddCommGroup

@[reducible] private local instance relativeCorePseudoMetricSpace
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod) :
    PseudoMetricSpace (RelativeCore period hPeriod plusBase minusBase) :=
  relativeCoreNormedAddCommGroup period hPeriod plusBase minusBase
    |>.toPseudoMetricSpace

@[reducible] private local instance relativeCoreUniformSpace
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod) :
    UniformSpace (RelativeCore period hPeriod plusBase minusBase) :=
  relativeCorePseudoMetricSpace period hPeriod plusBase minusBase
    |>.toUniformSpace

@[reducible] private local instance relativeCoreTopologicalSpace
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod) :
    TopologicalSpace (RelativeCore period hPeriod plusBase minusBase) :=
  relativeCoreUniformSpace period hPeriod plusBase minusBase
    |>.toTopologicalSpace

@[reducible] private local instance relativeCoreNormedSpace
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod) :
    NormedSpace Real (RelativeCore period hPeriod plusBase minusBase) :=
  inferInstance

@[reducible] private local instance relativeCoreModule
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod) :
    Module Real (RelativeCore period hPeriod plusBase minusBase) :=
  relativeCoreNormedSpace period hPeriod plusBase minusBase |>.toModule

/-- Chain-rule derivative of the inverse selected identity root. -/
def regularGeneralMetricC2IdentityRootInverseDerivative
    (variation : C2Matrix period hPeriod)
    (hVariation : variation ∈
      c2IdentityRootInvertiblePerturbationDomain period hPeriod) :
    C2Matrix period hPeriod →L[Real] C2Matrix period hPeriod :=
  (c2FiniteMatrixInverseDerivative period hPeriod 4
      (c2IdentityRootBranch period hPeriod variation)).comp
    (c2IdentityRootDerivative period hPeriod variation hVariation.1)

theorem regularGeneralMetricC2IdentityRootInverse_hasFDerivAt
    (variation : C2Matrix period hPeriod)
    (hVariation : variation ∈
      c2IdentityRootInvertiblePerturbationDomain period hPeriod) :
    HasFDerivAt
      (regularGeneralMetricC2IdentityRootInverseC2Matrix period hPeriod)
      (regularGeneralMetricC2IdentityRootInverseDerivative
        period hPeriod variation hVariation) variation := by
  exact (c2FiniteMatrixInverse_hasFDerivAt period hPeriod 4
    (c2IdentityRootBranch period hPeriod variation)
    (c2IdentityRootBranch_mem_unitSet period hPeriod hVariation)).comp
      variation
      (c2IdentityRootBranch_hasFDerivAt
        period hPeriod variation hVariation.1)

@[simp]
theorem regularGeneralMetricC2IdentityRootInverseDerivative_apply
    (variation : C2Matrix period hPeriod)
    (hVariation : variation ∈
      c2IdentityRootInvertiblePerturbationDomain period hPeriod)
    (direction : C2Matrix period hPeriod) :
    regularGeneralMetricC2IdentityRootInverseDerivative
        period hPeriod variation hVariation direction =
      -c2FiniteMatrixProduct
        (period := period) (hPeriod := hPeriod) 4
        (regularGeneralMetricC2IdentityRootInverseC2Matrix
          period hPeriod variation)
        (c2FiniteMatrixProduct
          (period := period) (hPeriod := hPeriod) 4
          (c2IdentityRootDerivative period hPeriod variation hVariation.1
            direction)
          (regularGeneralMetricC2IdentityRootInverseC2Matrix
            period hPeriod variation)) :=
  rfl

/-- Projection to the plus-root perturbation. -/
def regularGeneralMetricC2PairedRelativePlusProjection
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod) :
    RelativeCore period hPeriod plusBase minusBase →L[Real]
      C2Matrix period hPeriod :=
  (ContinuousLinearMap.fst Real
      (C2Matrix period hPeriod) (C2Matrix period hPeriod)).comp
    (ContinuousLinearMap.snd Real
      (RegularGeneralMetricC2PairedCore
        period hPeriod plusBase minusBase)
      (C2Matrix period hPeriod × C2Matrix period hPeriod))

@[simp]
theorem regularGeneralMetricC2PairedRelativePlusProjection_apply
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (core : RelativeCore period hPeriod plusBase minusBase) :
    regularGeneralMetricC2PairedRelativePlusProjection
        period hPeriod plusBase minusBase core = core.2.1 :=
  rfl

/-- Projection to the affine relative-matrix perturbation. -/
def regularGeneralMetricC2PairedRelativeCrossProjection
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod) :
    RelativeCore period hPeriod plusBase minusBase →L[Real]
      C2Matrix period hPeriod :=
  (ContinuousLinearMap.snd Real
      (C2Matrix period hPeriod) (C2Matrix period hPeriod)).comp
    (ContinuousLinearMap.snd Real
      (RegularGeneralMetricC2PairedCore
        period hPeriod plusBase minusBase)
      (C2Matrix period hPeriod × C2Matrix period hPeriod))

@[simp]
theorem regularGeneralMetricC2PairedRelativeCrossProjection_apply
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (core : RelativeCore period hPeriod plusBase minusBase) :
    regularGeneralMetricC2PairedRelativeCrossProjection
        period hPeriod plusBase minusBase core = core.2.2 :=
  rfl

/-- Inverse root viewed as a function of the paired relative core. -/
def regularGeneralMetricC2PairedInverseRootOnCore
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (core : RelativeCore period hPeriod plusBase minusBase) :
    C2Matrix period hPeriod :=
  regularGeneralMetricC2IdentityRootInverseC2Matrix
    period hPeriod core.2.1

/-- Derivative of the inverse-root core projection. -/
def regularGeneralMetricC2PairedInverseRootOnCoreDerivative
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (core : RelativeCore period hPeriod plusBase minusBase)
    (hCore : core ∈ regularGeneralMetricC2PairedRelativeMatrixDomain
      period hPeriod plusBase minusBase) :
    RelativeCore period hPeriod plusBase minusBase →L[Real]
      C2Matrix period hPeriod :=
  (regularGeneralMetricC2IdentityRootInverseDerivative
    period hPeriod core.2.1 hCore).comp
    (regularGeneralMetricC2PairedRelativePlusProjection
      period hPeriod plusBase minusBase)

theorem regularGeneralMetricC2PairedInverseRootOnCore_hasFDerivAt
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (core : RelativeCore period hPeriod plusBase minusBase)
    (hCore : core ∈ regularGeneralMetricC2PairedRelativeMatrixDomain
      period hPeriod plusBase minusBase) :
    HasFDerivAt
      (regularGeneralMetricC2PairedInverseRootOnCore
        period hPeriod plusBase minusBase)
      (regularGeneralMetricC2PairedInverseRootOnCoreDerivative
        period hPeriod plusBase minusBase core hCore) core := by
  let projection := regularGeneralMetricC2PairedRelativePlusProjection
    period hPeriod plusBase minusBase
  have hProjection : projection core = core.2.1 := rfl
  have hOuter : HasFDerivAt
      (regularGeneralMetricC2IdentityRootInverseC2Matrix period hPeriod)
      (regularGeneralMetricC2IdentityRootInverseDerivative
        period hPeriod core.2.1 hCore) (projection core) := by
    rw [hProjection]
    exact regularGeneralMetricC2IdentityRootInverse_hasFDerivAt
      period hPeriod core.2.1 hCore
  have hComposite := HasFDerivAt.comp
    (f := fun current => projection current)
    (g := regularGeneralMetricC2IdentityRootInverseC2Matrix period hPeriod)
    core hOuter projection.hasFDerivAt
  apply hComposite.congr_of_eventuallyEq
  filter_upwards [] with current
  rfl

/-- Affine relative matrix before conjugation by the inverse root. -/
def regularGeneralMetricC2PairedAffineRelativeMatrix
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (core : RelativeCore period hPeriod plusBase minusBase) :
    C2Matrix period hPeriod :=
  regularGeneralMetricC2VariationMatrix period hPeriod plusBase
      (minusBase.metric.tensor - plusBase.metric.tensor) + core.2.2

/-- Derivative of the affine relative matrix. -/
def regularGeneralMetricC2PairedAffineRelativeMatrixDerivative
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod) :
    RelativeCore period hPeriod plusBase minusBase →L[Real]
      C2Matrix period hPeriod :=
  (0 : RelativeCore period hPeriod plusBase minusBase →L[Real]
      C2Matrix period hPeriod) +
    regularGeneralMetricC2PairedRelativeCrossProjection
      period hPeriod plusBase minusBase

theorem regularGeneralMetricC2PairedAffineRelativeMatrix_hasFDerivAt
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (core : RelativeCore period hPeriod plusBase minusBase) :
    HasFDerivAt
      (regularGeneralMetricC2PairedAffineRelativeMatrix
        period hPeriod plusBase minusBase)
      (regularGeneralMetricC2PairedAffineRelativeMatrixDerivative
        period hPeriod plusBase minusBase) core := by
  let projection := regularGeneralMetricC2PairedRelativeCrossProjection
    period hPeriod plusBase minusBase
  have hAffine :=
    (hasFDerivAt_const (x := core)
      (c := regularGeneralMetricC2VariationMatrix period hPeriod plusBase
        (minusBase.metric.tensor - plusBase.metric.tensor))).add
      projection.hasFDerivAt
  apply hAffine.congr_of_eventuallyEq
  filter_upwards [] with current
  rfl

/-- Right factor `C * S` and its exact Leibniz derivative. -/
def regularGeneralMetricC2PairedRelativeRightProduct
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (core : RelativeCore period hPeriod plusBase minusBase) :
    C2Matrix period hPeriod :=
  c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) 4
    (regularGeneralMetricC2PairedAffineRelativeMatrix
      period hPeriod plusBase minusBase core)
    (regularGeneralMetricC2PairedInverseRootOnCore
      period hPeriod plusBase minusBase core)

def regularGeneralMetricC2PairedRelativeRightProductDerivative
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (core : RelativeCore period hPeriod plusBase minusBase)
    (hCore : core ∈ regularGeneralMetricC2PairedRelativeMatrixDomain
      period hPeriod plusBase minusBase) :
    RelativeCore period hPeriod plusBase minusBase →L[Real]
      C2Matrix period hPeriod :=
  let product := c2FiniteMatrixProduct
    (period := period) (hPeriod := hPeriod) 4
  let C := regularGeneralMetricC2PairedAffineRelativeMatrix
    period hPeriod plusBase minusBase core
  let S := regularGeneralMetricC2PairedInverseRootOnCore
    period hPeriod plusBase minusBase core
  let dC := regularGeneralMetricC2PairedAffineRelativeMatrixDerivative
    period hPeriod plusBase minusBase
  let dS := regularGeneralMetricC2PairedInverseRootOnCoreDerivative
    period hPeriod plusBase minusBase core hCore
  (product C).comp dS + (product.comp dC).flip S

theorem regularGeneralMetricC2PairedRelativeRightProduct_hasFDerivAt
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (core : RelativeCore period hPeriod plusBase minusBase)
    (hCore : core ∈ regularGeneralMetricC2PairedRelativeMatrixDomain
      period hPeriod plusBase minusBase) :
    HasFDerivAt
      (regularGeneralMetricC2PairedRelativeRightProduct
        period hPeriod plusBase minusBase)
      (regularGeneralMetricC2PairedRelativeRightProductDerivative
        period hPeriod plusBase minusBase core hCore) core := by
  let product := c2FiniteMatrixProduct
    (period := period) (hPeriod := hPeriod) 4
  let C := regularGeneralMetricC2PairedAffineRelativeMatrix
    period hPeriod plusBase minusBase
  let S := regularGeneralMetricC2PairedInverseRootOnCore
    period hPeriod plusBase minusBase
  have hC := regularGeneralMetricC2PairedAffineRelativeMatrix_hasFDerivAt
    period hPeriod plusBase minusBase core
  have hS := regularGeneralMetricC2PairedInverseRootOnCore_hasFDerivAt
    period hPeriod plusBase minusBase core hCore
  have hOperator := HasFDerivAt.comp
    (f := C) (g := fun matrix => product matrix)
    core product.hasFDerivAt hC
  have hRight := hOperator.clm_apply hS
  apply hRight.congr_of_eventuallyEq
  filter_upwards [] with current
  rfl

/-- Exact Leibniz derivative of `S * (C * S)`. -/
def regularGeneralMetricC2PairedRelativeMatrixDerivative
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (core : RelativeCore period hPeriod plusBase minusBase)
    (hCore : core ∈ regularGeneralMetricC2PairedRelativeMatrixDomain
      period hPeriod plusBase minusBase) :
    RelativeCore period hPeriod plusBase minusBase →L[Real]
      C2Matrix period hPeriod :=
  let product := c2FiniteMatrixProduct
    (period := period) (hPeriod := hPeriod) 4
  let S := regularGeneralMetricC2PairedInverseRootOnCore
    period hPeriod plusBase minusBase core
  let dS := regularGeneralMetricC2PairedInverseRootOnCoreDerivative
    period hPeriod plusBase minusBase core hCore
  let right := regularGeneralMetricC2PairedRelativeRightProduct
    period hPeriod plusBase minusBase core
  let dRight := regularGeneralMetricC2PairedRelativeRightProductDerivative
    period hPeriod plusBase minusBase core hCore
  (product S).comp dRight + (product.comp dS).flip right

theorem regularGeneralMetricC2PairedRelativeMatrix_hasFDerivAt
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (core : RelativeCore period hPeriod plusBase minusBase)
    (hCore : core ∈ regularGeneralMetricC2PairedRelativeMatrixDomain
      period hPeriod plusBase minusBase) :
    HasFDerivAt
      (regularGeneralMetricC2PairedRelativeMatrix
        period hPeriod plusBase minusBase)
      (regularGeneralMetricC2PairedRelativeMatrixDerivative
        period hPeriod plusBase minusBase core hCore) core := by
  let product := c2FiniteMatrixProduct
    (period := period) (hPeriod := hPeriod) 4
  let S := regularGeneralMetricC2PairedInverseRootOnCore
    period hPeriod plusBase minusBase
  let right := regularGeneralMetricC2PairedRelativeRightProduct
    period hPeriod plusBase minusBase
  have hS := regularGeneralMetricC2PairedInverseRootOnCore_hasFDerivAt
    period hPeriod plusBase minusBase core hCore
  have hRight := regularGeneralMetricC2PairedRelativeRightProduct_hasFDerivAt
    period hPeriod plusBase minusBase core hCore
  have hProductS := HasFDerivAt.comp
    (f := S) (g := fun matrix => product matrix)
    core product.hasFDerivAt hS
  have hSandwich := hProductS.clm_apply hRight
  apply hSandwich.congr_of_eventuallyEq
  filter_upwards [] with current
  rfl

/-- Gate marker: the inverse root and full relative sandwich now carry their
exact Fréchet derivatives on the authentic open domain. -/
theorem regular_general_metric_c2_paired_relative_matrix_derivative_gate
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (core : RelativeCore period hPeriod plusBase minusBase)
    (hCore : core ∈ regularGeneralMetricC2PairedRelativeMatrixDomain
      period hPeriod plusBase minusBase) :
    HasFDerivAt
        (regularGeneralMetricC2IdentityRootInverseC2Matrix period hPeriod)
        (regularGeneralMetricC2IdentityRootInverseDerivative
          period hPeriod core.2.1 hCore) core.2.1 ∧
      HasFDerivAt
        (regularGeneralMetricC2PairedRelativeMatrix
          period hPeriod plusBase minusBase)
        (regularGeneralMetricC2PairedRelativeMatrixDerivative
          period hPeriod plusBase minusBase core hCore) core :=
  ⟨regularGeneralMetricC2IdentityRootInverse_hasFDerivAt
      period hPeriod core.2.1 hCore,
    regularGeneralMetricC2PairedRelativeMatrix_hasFDerivAt
      period hPeriod plusBase minusBase core hCore⟩

end
end P0EFTJanusProgramPRegularGeneralMetricC2PairedRelativeMatrixDerivative4D
end JanusFormal
