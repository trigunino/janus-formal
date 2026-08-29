import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGeneralMetricC2RelativeEndomorphism4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixInverse4D

/-!
# Genuine open C² domain for general metric variations

The closed true-smooth range of relative endomorphisms is a complete metric
tangent space.  It remains inside the intrinsic redundant-frame corner.
Adding the ambient identity and pulling back the finite C² unit group gives a
genuine open neighborhood of zero with a smooth inverse-metric matrix.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGeneralMetricC2OpenDomain4D

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open scoped Manifold ContDiff Topology BigOperators
open Set Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixInverse4D
open P0EFTJanusProgramPGlobalCandidateAC2FiniteFrameCorner4D
open P0EFTJanusProgramPGeneralMetricC2RelativeEndomorphism4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev C2Scalar :=
  CanonicalPhysicalScalarC2JetCore period hPeriod

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

/-- Closed true-smooth range of relative metric endomorphisms. -/
def generalMetricRelativeC2CoreSubmodule
    (frame : SmoothD8Frame period hPeriod)
    (baseMetric : SmoothGeneralLorentzMetric period hPeriod) :
    Submodule Real (C2FiniteMatrix period hPeriod frame.count) :=
  (LinearMap.range
    (smoothGeneralMetricRelativeEndomorphismToC2
      period hPeriod frame baseMetric)).topologicalClosure

/-- Complete C² tangent space based at an arbitrary smooth Lorentz metric. -/
abbrev GeneralMetricRelativeC2Core
    (frame : SmoothD8Frame period hPeriod)
    (baseMetric : SmoothGeneralLorentzMetric period hPeriod) :=
  generalMetricRelativeC2CoreSubmodule
    period hPeriod frame baseMetric

theorem generalMetricRelativeC2Core_isClosed
    (frame : SmoothD8Frame period hPeriod)
    (baseMetric : SmoothGeneralLorentzMetric period hPeriod) :
    IsClosed
      (GeneralMetricRelativeC2Core period hPeriod frame baseMetric :
        Set (C2FiniteMatrix period hPeriod frame.count)) :=
  Submodule.isClosed_topologicalClosure _

@[implicit_reducible]
def generalMetricRelativeC2CoreCompleteSpace
    (frame : SmoothD8Frame period hPeriod)
    (baseMetric : SmoothGeneralLorentzMetric period hPeriod) :
    CompleteSpace
      (GeneralMetricRelativeC2Core period hPeriod frame baseMetric) :=
  Submodule.topologicalClosure.completeSpace
    (LinearMap.range
      (smoothGeneralMetricRelativeEndomorphismToC2
        period hPeriod frame baseMetric))

/-- Dense faithful lift of genuine smooth metric variations. -/
def smoothToGeneralMetricRelativeC2Core
    (frame : SmoothD8Frame period hPeriod)
    (baseMetric : SmoothGeneralLorentzMetric period hPeriod) :
    SmoothSymmetricCovariantTwoTensor period hPeriod →ₗ[Real]
      GeneralMetricRelativeC2Core period hPeriod frame baseMetric where
  toFun tensor :=
    ⟨smoothGeneralMetricRelativeEndomorphismToC2
        period hPeriod frame baseMetric tensor,
      (LinearMap.range
        (smoothGeneralMetricRelativeEndomorphismToC2
          period hPeriod frame baseMetric)).le_topologicalClosure
        (LinearMap.mem_range_self
          (smoothGeneralMetricRelativeEndomorphismToC2
            period hPeriod frame baseMetric) tensor)⟩
  map_add' first second := Subtype.ext
    ((smoothGeneralMetricRelativeEndomorphismToC2
      period hPeriod frame baseMetric).map_add first second)
  map_smul' scalar tensor := Subtype.ext
    ((smoothGeneralMetricRelativeEndomorphismToC2
      period hPeriod frame baseMetric).map_smul scalar tensor)

theorem smoothToGeneralMetricRelativeC2Core_injective
    (frame : SmoothD8Frame period hPeriod)
    (baseMetric : SmoothGeneralLorentzMetric period hPeriod) :
    Function.Injective
      (smoothToGeneralMetricRelativeC2Core
        period hPeriod frame baseMetric) := by
  intro first second hEqual
  apply smoothGeneralMetricRelativeEndomorphismToC2_injective
    period hPeriod frame baseMetric
  exact congrArg Subtype.val hEqual

theorem smoothToGeneralMetricRelativeC2Core_denseRange
    (frame : SmoothD8Frame period hPeriod)
    (baseMetric : SmoothGeneralLorentzMetric period hPeriod) :
    DenseRange
      (smoothToGeneralMetricRelativeC2Core
        period hPeriod frame baseMetric) := by
  simp only [DenseRange]
  rw [Subtype.dense_iff]
  let inclusion := smoothGeneralMetricRelativeEndomorphismToC2
    period hPeriod frame baseMetric
  have hRange :
      Subtype.val '' Set.range
          (smoothToGeneralMetricRelativeC2Core
            period hPeriod frame baseMetric) =
        (LinearMap.range inclusion :
          Set (C2FiniteMatrix period hPeriod frame.count)) := by
    ext value
    constructor
    · rintro ⟨lifted, ⟨tensor, rfl⟩, rfl⟩
      exact ⟨tensor, rfl⟩
    · rintro ⟨tensor, rfl⟩
      exact ⟨smoothToGeneralMetricRelativeC2Core
          period hPeriod frame baseMetric tensor,
        ⟨tensor, rfl⟩, rfl⟩
  change closure (LinearMap.range inclusion :
      Set (C2FiniteMatrix period hPeriod frame.count)) ⊆
    closure (Subtype.val '' Set.range
      (smoothToGeneralMetricRelativeC2Core
        period hPeriod frame baseMetric))
  rw [hRange]

def generalMetricRelativeC2CoreToMatrix
    (frame : SmoothD8Frame period hPeriod)
    (baseMetric : SmoothGeneralLorentzMetric period hPeriod) :
    GeneralMetricRelativeC2Core period hPeriod frame baseMetric →L[Real]
      C2FiniteMatrix period hPeriod frame.count :=
  (generalMetricRelativeC2CoreSubmodule
    period hPeriod frame baseMetric).subtypeL

theorem smoothGeneralMetricRelativeEndomorphism_mem_corner
    (frame : SmoothD8Frame period hPeriod)
    (baseMetric : SmoothGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    smoothGeneralMetricRelativeEndomorphismToC2
        period hPeriod frame baseMetric tensor ∈
      c2FiniteFrameCornerSubmodule period hPeriod frame baseMetric := by
  rw [c2FiniteFrameCorner_mem_iff]
  have hCorner := smoothGeneralMetricRelativeEndomorphismToC2_corner
    period hPeriod frame baseMetric tensor
  rw [c2FiniteFrameCornerProjection_apply, hCorner.2, hCorner.1]

/-- Every completed variation remains an intrinsic corner endomorphism. -/
theorem generalMetricRelativeC2Core_mem_corner
    (frame : SmoothD8Frame period hPeriod)
    (baseMetric : SmoothGeneralLorentzMetric period hPeriod)
    (variation : GeneralMetricRelativeC2Core
      period hPeriod frame baseMetric) :
    variation.1 ∈
      c2FiniteFrameCornerSubmodule period hPeriod frame baseMetric := by
  apply (closure_minimal ?_
    (c2FiniteFrameCornerSubmodule_isClosed
      period hPeriod frame baseMetric)) variation.2
  rintro matrix ⟨tensor, rfl⟩
  exact smoothGeneralMetricRelativeEndomorphism_mem_corner
    period hPeriod frame baseMetric tensor

theorem generalMetricRelativeC2Core_left_projector
    (frame : SmoothD8Frame period hPeriod)
    (baseMetric : SmoothGeneralLorentzMetric period hPeriod)
    (variation : GeneralMetricRelativeC2Core
      period hPeriod frame baseMetric) :
    c2FiniteMatrixProduct
        (period := period) (hPeriod := hPeriod) frame.count
        (c2FiniteFrameProjector period hPeriod frame baseMetric) variation.1 =
      variation.1 := by
  have hSandwich := (c2FiniteFrameCorner_mem_iff
    period hPeriod frame baseMetric variation.1).1
      (generalMetricRelativeC2Core_mem_corner
        period hPeriod frame baseMetric variation)
  exact c2FiniteMatrixSandwich_left period hPeriod frame.count
    (c2FiniteFrameProjector period hPeriod frame baseMetric) variation.1
    (c2FiniteFrameProjector_idempotent
      period hPeriod frame baseMetric) hSandwich

theorem generalMetricRelativeC2Core_right_projector
    (frame : SmoothD8Frame period hPeriod)
    (baseMetric : SmoothGeneralLorentzMetric period hPeriod)
    (variation : GeneralMetricRelativeC2Core
      period hPeriod frame baseMetric) :
    c2FiniteMatrixProduct
        (period := period) (hPeriod := hPeriod) frame.count variation.1
        (c2FiniteFrameProjector period hPeriod frame baseMetric) =
      variation.1 := by
  have hSandwich := (c2FiniteFrameCorner_mem_iff
    period hPeriod frame baseMetric variation.1).1
      (generalMetricRelativeC2Core_mem_corner
        period hPeriod frame baseMetric variation)
  exact c2FiniteMatrixSandwich_right period hPeriod frame.count
    (c2FiniteFrameProjector period hPeriod frame baseMetric) variation.1
    (c2FiniteFrameProjector_idempotent
      period hPeriod frame baseMetric) hSandwich

/-- Ambient extension of `P + g⁻¹h`; it is `I + g⁻¹h` on the redundant
matrix space. -/
def generalMetricRelativeC2ExtendedMatrix
    (frame : SmoothD8Frame period hPeriod)
    (baseMetric : SmoothGeneralLorentzMetric period hPeriod)
    (variation : GeneralMetricRelativeC2Core
      period hPeriod frame baseMetric) :
    C2FiniteMatrix period hPeriod frame.count :=
  c2FiniteMatrixIdentity period hPeriod frame.count + variation.1

theorem generalMetricRelativeC2ExtendedMatrix_contDiff
    (frame : SmoothD8Frame period hPeriod)
    (baseMetric : SmoothGeneralLorentzMetric period hPeriod) :
    ContDiff Real ∞
      (generalMetricRelativeC2ExtendedMatrix
        period hPeriod frame baseMetric) := by
  exact contDiff_const.add
    (generalMetricRelativeC2CoreToMatrix
      period hPeriod frame baseMetric).contDiff

/-- Genuine open parameter domain on which the relative metric is
invertible. -/
def generalMetricRelativeC2OpenDomain
    (frame : SmoothD8Frame period hPeriod)
    (baseMetric : SmoothGeneralLorentzMetric period hPeriod) :
    Set (GeneralMetricRelativeC2Core
      period hPeriod frame baseMetric) :=
  generalMetricRelativeC2ExtendedMatrix
      period hPeriod frame baseMetric ⁻¹'
    c2FiniteMatrixUnitSet period hPeriod frame.count

theorem generalMetricRelativeC2OpenDomain_isOpen
    (frame : SmoothD8Frame period hPeriod)
    (baseMetric : SmoothGeneralLorentzMetric period hPeriod) :
    IsOpen
      (generalMetricRelativeC2OpenDomain
        period hPeriod frame baseMetric) :=
  (c2FiniteMatrixUnitSet_isOpen period hPeriod frame.count).preimage
    (generalMetricRelativeC2ExtendedMatrix_contDiff
      period hPeriod frame baseMetric).continuous

theorem zero_mem_generalMetricRelativeC2OpenDomain
    (frame : SmoothD8Frame period hPeriod)
    (baseMetric : SmoothGeneralLorentzMetric period hPeriod) :
    (0 : GeneralMetricRelativeC2Core
      period hPeriod frame baseMetric) ∈
      generalMetricRelativeC2OpenDomain
        period hPeriod frame baseMetric := by
  change c2FiniteMatrixIdentity period hPeriod frame.count + 0 ∈
    c2FiniteMatrixUnitSet period hPeriod frame.count
  simpa using c2FiniteMatrixIdentity_mem_unitSet
    period hPeriod frame.count

/-- Smooth inverse of the extended relative metric matrix. -/
def generalMetricRelativeC2InverseMatrix
    (frame : SmoothD8Frame period hPeriod)
    (baseMetric : SmoothGeneralLorentzMetric period hPeriod)
    (variation : GeneralMetricRelativeC2Core
      period hPeriod frame baseMetric) :
    C2FiniteMatrix period hPeriod frame.count :=
  c2FiniteMatrixInverse period hPeriod frame.count
    (generalMetricRelativeC2ExtendedMatrix
      period hPeriod frame baseMetric variation)

theorem generalMetricRelativeC2InverseMatrix_contDiffOn
    (frame : SmoothD8Frame period hPeriod)
    (baseMetric : SmoothGeneralLorentzMetric period hPeriod) :
    ContDiffOn Real ∞
      (generalMetricRelativeC2InverseMatrix
        period hPeriod frame baseMetric)
      (generalMetricRelativeC2OpenDomain
        period hPeriod frame baseMetric) := by
  change ContDiffOn Real ∞
    (c2FiniteMatrixInverse period hPeriod frame.count ∘
      generalMetricRelativeC2ExtendedMatrix
        period hPeriod frame baseMetric)
    (generalMetricRelativeC2ExtendedMatrix
        period hPeriod frame baseMetric ⁻¹'
      c2FiniteMatrixUnitSet period hPeriod frame.count)
  have hComposition :=
    (c2FiniteMatrixInverse_contDiffOn period hPeriod frame.count).comp
      (generalMetricRelativeC2ExtendedMatrix_contDiff
        period hPeriod frame baseMetric).contDiffOn
      (fun _ hVariation => hVariation)
  exact hComposition

theorem generalMetricRelativeC2Extended_mul_inverse
    (frame : SmoothD8Frame period hPeriod)
    (baseMetric : SmoothGeneralLorentzMetric period hPeriod)
    (variation : GeneralMetricRelativeC2Core
      period hPeriod frame baseMetric)
    (hVariation : variation ∈ generalMetricRelativeC2OpenDomain
      period hPeriod frame baseMetric) :
    c2FiniteMatrixProduct
        (period := period) (hPeriod := hPeriod) frame.count
        (generalMetricRelativeC2ExtendedMatrix
          period hPeriod frame baseMetric variation)
        (generalMetricRelativeC2InverseMatrix
          period hPeriod frame baseMetric variation) =
      c2FiniteMatrixIdentity period hPeriod frame.count :=
  c2FiniteMatrixProduct_inverse_right period hPeriod frame.count
    (generalMetricRelativeC2ExtendedMatrix
      period hPeriod frame baseMetric variation) hVariation

theorem generalMetricRelativeC2Inverse_mul_extended
    (frame : SmoothD8Frame period hPeriod)
    (baseMetric : SmoothGeneralLorentzMetric period hPeriod)
    (variation : GeneralMetricRelativeC2Core
      period hPeriod frame baseMetric)
    (hVariation : variation ∈ generalMetricRelativeC2OpenDomain
      period hPeriod frame baseMetric) :
    c2FiniteMatrixProduct
        (period := period) (hPeriod := hPeriod) frame.count
        (generalMetricRelativeC2InverseMatrix
          period hPeriod frame baseMetric variation)
        (generalMetricRelativeC2ExtendedMatrix
          period hPeriod frame baseMetric variation) =
      c2FiniteMatrixIdentity period hPeriod frame.count :=
  c2FiniteMatrixProduct_inverse_left period hPeriod frame.count
    (generalMetricRelativeC2ExtendedMatrix
      period hPeriod frame baseMetric variation) hVariation

/-- Summary gate for the local general-metric C² chart domain. -/
theorem general_metric_c2_open_domain_gate
    (frame : SmoothD8Frame period hPeriod)
    (baseMetric : SmoothGeneralLorentzMetric period hPeriod) :
    IsOpen
        (generalMetricRelativeC2OpenDomain
          period hPeriod frame baseMetric) ∧
      (0 : GeneralMetricRelativeC2Core
        period hPeriod frame baseMetric) ∈
          generalMetricRelativeC2OpenDomain
            period hPeriod frame baseMetric ∧
      Function.Injective
        (smoothToGeneralMetricRelativeC2Core
          period hPeriod frame baseMetric) ∧
      DenseRange
        (smoothToGeneralMetricRelativeC2Core
          period hPeriod frame baseMetric) ∧
      ContDiffOn Real ∞
        (generalMetricRelativeC2InverseMatrix
          period hPeriod frame baseMetric)
        (generalMetricRelativeC2OpenDomain
          period hPeriod frame baseMetric) := by
  exact ⟨generalMetricRelativeC2OpenDomain_isOpen
      period hPeriod frame baseMetric,
    zero_mem_generalMetricRelativeC2OpenDomain
      period hPeriod frame baseMetric,
    smoothToGeneralMetricRelativeC2Core_injective
      period hPeriod frame baseMetric,
    smoothToGeneralMetricRelativeC2Core_denseRange
      period hPeriod frame baseMetric,
    generalMetricRelativeC2InverseMatrix_contDiffOn
      period hPeriod frame baseMetric⟩

end

end P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
end JanusFormal
