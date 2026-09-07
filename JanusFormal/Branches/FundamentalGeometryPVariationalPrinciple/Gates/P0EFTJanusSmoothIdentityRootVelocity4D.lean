import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootJetRigidity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalC2IdentityRootDerivative4D

/-!
# Smooth identity-root velocity and its exact completed lift

The smooth inverse of the pointwise Sylvester family produces the root
velocity.  Lifting its equation and using the completed Sylvester equivalence
identifies all C² jets with the actual derivative of the selected root branch.
-/

namespace JanusFormal
namespace P0EFTJanusSmoothIdentityRootVelocity4D

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 600000

noncomputable section
open scoped Manifold ContDiff Topology BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0LocalRootBranch4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2LocalRootBranch4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2IdentityRootBranch4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2IdentityRootDerivative4D
open P0EFTJanusPositiveRawSplitCharpolyContDiffLocalRootBranch4D
open P0EFTJanusProgramPGeneralMetricC2RelativeEndomorphism4D
open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootLift4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootSmoothLift4D
open P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootJetRigidity4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
private abbrev Matrix4 := Matrix (Fin 4) (Fin 4) Real
private abbrev C2Scalar := CanonicalPhysicalScalarC2JetCore period hPeriod
private abbrev RegularFrame (metric : RegularGeneralLorentzMetric period hPeriod) :=
  regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod
local instance : NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (C2Scalar period hPeriod) := inferInstance
local instance : CompleteSpace (C2Scalar period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod

@[reducible] local instance canonicalMatrixNormedAddCommGroup : NormedAddCommGroup Matrix4 :=
  P0EFTJanusMappingTorusCanonicalPhysicalC2LocalRootBranch4D.canonicalMatrixNormedAddCommGroup
local instance : AddCommGroup Matrix4 := canonicalMatrixNormedAddCommGroup.toAddCommGroup
local instance canonicalMatrixPseudoMetricSpace : PseudoMetricSpace Matrix4 :=
  canonicalMatrixNormedAddCommGroup.toPseudoMetricSpace
local instance canonicalMatrixUniformSpace : UniformSpace Matrix4 :=
  canonicalMatrixPseudoMetricSpace.toUniformSpace
local instance : TopologicalSpace Matrix4 := canonicalMatrixUniformSpace.toTopologicalSpace
@[reducible] local instance canonicalMatrixNormedSpace : NormedSpace Real Matrix4 :=
  P0EFTJanusMappingTorusCanonicalPhysicalC2LocalRootBranch4D.canonicalMatrixNormedSpace
local instance : Module Real Matrix4 := canonicalMatrixNormedSpace.toModule
local instance : CompleteSpace Matrix4 := FiniteDimensional.complete Real Matrix4

private theorem variationMatrix_value_eq_affine_sub_one
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (direction : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    c2FiniteMatrixValueAt period hPeriod 4
        (regularGeneralMetricC2VariationMatrix period hPeriod metric direction) point =
      regularGeneralMetricAffineRelativeMatrixField period hPeriod metric direction point - 1 := by
  rw [regularGeneralMetricC2VariationMatrix_valueAt,
    ← smoothGeneralMetricRelativeEndomorphismMatrix_apply period hPeriod
      (RegularFrame period hPeriod metric) metric.metric direction point]
  ext row column
  change smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod
      (RegularFrame period hPeriod metric) metric.metric direction row column point =
    ((if row = column then 1 else 0) +
      smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod
        (RegularFrame period hPeriod metric) metric.metric direction row column point) -
      (if row = column then 1 else 0)
  ring

def regularGeneralMetricIdentityRootSylvesterInverse
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (shift : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    EffectiveQuotient period hPeriod → Matrix4 →L[Real] Matrix4 :=
  fun point => (canonicalSylvesterOperator
    (regularGeneralMetricC2IdentityRootMatrixAt period hPeriod metric shift point)).inverse

private theorem rootSylvester_isInvertible
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (shift : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hRoot : RegularGeneralMetricC2IdentityRootAdmissible period hPeriod metric shift)
    (point : EffectiveQuotient period hPeriod) :
    (canonicalSylvesterOperator
      (regularGeneralMetricC2IdentityRootMatrixAt period hPeriod metric shift point)).IsInvertible := by
  let equiv := (LinearEquiv.ofBijective
    (canonicalSylvesterOperator
      (regularGeneralMetricC2IdentityRootMatrixAt period hPeriod metric shift point)).toLinearMap
    (regularGeneralMetricC2IdentityRootMatrixAt_sylvester_bijective period hPeriod
      metric shift hRoot point)).toContinuousLinearEquiv
  refine ⟨equiv, ?_⟩
  ext matrix
  rfl

theorem regularGeneralMetricIdentityRootSylvesterInverse_contMDiff
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (shift : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hRoot : RegularGeneralMetricC2IdentityRootAdmissible period hPeriod metric shift) :
    ContMDiff coverModelWithCorners (modelWithCornersSelf Real (Matrix4 →L[Real] Matrix4)) ∞
      (regularGeneralMetricIdentityRootSylvesterInverse period hPeriod metric shift) := by
  let family : Matrix4 →L[Real] (Matrix4 →L[Real] Matrix4) := canonicalSylvesterFamily
  have hSmooth := family.contMDiff.comp
    (regularGeneralMetricC2IdentityRootMatrixAt_contMDiff period hPeriod metric shift hRoot)
  intro point
  exact ((rootSylvester_isInvertible period hPeriod metric shift hRoot point
    ).contDiffAt_map_inverse (n := ∞)).comp_contMDiffAt
      (f := fun p : EffectiveQuotient period hPeriod =>
        family (regularGeneralMetricC2IdentityRootMatrixAt period hPeriod metric shift p))
      (x := point) hSmooth.contMDiffAt

/-- The true root velocity, constructed as a genuine smooth matrix field by
inverting the smooth pointwise Sylvester family. -/
def regularGeneralMetricSmoothIdentityRootVelocity
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (shift direction : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hShift : regularGeneralMetricSmoothC2Variation period hPeriod metric shift ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric) :
    SmoothQuotientField period hPeriod Matrix4 where
  toFun := fun point => regularGeneralMetricIdentityRootSylvesterInverse period hPeriod metric shift point
    (regularGeneralMetricAffineRelativeMatrixField period hPeriod metric direction point - 1)
  contMDiff_toFun :=
    (regularGeneralMetricIdentityRootSylvesterInverse_contMDiff period hPeriod metric shift
      (regularGeneralMetricC2LorentzChartDomain_matrix_mem_root period hPeriod metric hShift).1
      ).clm_apply
      ((regularGeneralMetricAffineRelativeMatrixField period hPeriod metric direction
        ).contMDiff_toFun.sub contMDiff_const)

theorem regularGeneralMetricSmoothIdentityRootVelocity_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (shift direction : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hShift : regularGeneralMetricSmoothC2Variation period hPeriod metric shift ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric)
    (point : EffectiveQuotient period hPeriod) :
    regularGeneralMetricSmoothIdentityRootVelocity period hPeriod
        metric shift direction hShift point =
      regularGeneralMetricIdentityRootSylvesterInverse period hPeriod metric shift point
        (c2FiniteMatrixValueAt period hPeriod 4
          (regularGeneralMetricC2VariationMatrix period hPeriod metric direction) point) := by
  rw [variationMatrix_value_eq_affine_sub_one]
  rfl

/-- Its pointwise Sylvester equation has the actual relative metric test as right-hand side. -/
theorem regularGeneralMetricSmoothIdentityRootVelocity_sylvester
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (shift direction : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hShift : regularGeneralMetricSmoothC2Variation period hPeriod metric shift ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric)
    (point : EffectiveQuotient period hPeriod) :
    canonicalSylvesterOperator
        (regularGeneralMetricC2IdentityRootMatrixAt period hPeriod metric shift point)
        (regularGeneralMetricSmoothIdentityRootVelocity period hPeriod
          metric shift direction hShift point) =
      c2FiniteMatrixValueAt period hPeriod 4
        (regularGeneralMetricC2VariationMatrix period hPeriod metric direction) point := by
  rw [variationMatrix_value_eq_affine_sub_one]
  have hInvertible := rootSylvester_isInvertible period hPeriod metric shift
    (regularGeneralMetricC2LorentzChartDomain_matrix_mem_root period hPeriod metric hShift).1 point
  exact (hInvertible.inverse_apply_eq.mp (show
    (canonicalSylvesterOperator
      (regularGeneralMetricC2IdentityRootMatrixAt period hPeriod metric shift point)).inverse
      (regularGeneralMetricAffineRelativeMatrixField period hPeriod metric direction point - 1) =
    regularGeneralMetricSmoothIdentityRootVelocity period hPeriod
      metric shift direction hShift point from rfl)).symm

private theorem smoothRootVelocity_lift_sylvester
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (shift direction : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hShift : regularGeneralMetricSmoothC2Variation period hPeriod metric shift ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric) :
    c2FiniteMatrixSylvester period hPeriod 4
        (smoothMatrixFieldToC2 period hPeriod
          (regularGeneralMetricC2IdentityRootMatrixField period hPeriod metric shift
            (regularGeneralMetricC2LorentzChartDomain_matrix_mem_root period hPeriod metric hShift).1))
        (smoothMatrixFieldToC2 period hPeriod
          (regularGeneralMetricSmoothIdentityRootVelocity period hPeriod metric shift direction hShift)) =
      regularGeneralMetricC2VariationMatrix period hPeriod metric direction := by
  let root := regularGeneralMetricC2IdentityRootMatrixField period hPeriod metric shift
    (regularGeneralMetricC2LorentzChartDomain_matrix_mem_root period hPeriod metric hShift).1
  let velocity := regularGeneralMetricSmoothIdentityRootVelocity period hPeriod
    metric shift direction hShift
  change c2FiniteMatrixSylvester period hPeriod 4 (smoothMatrixFieldToC2 period hPeriod root)
    (smoothFiniteMatrixToC2 period hPeriod 4 (smoothMatrixFieldCoefficients period hPeriod velocity)) = _
  rw [c2FiniteMatrixSylvester_smooth]
  funext row column
  change smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
      (smoothMatrixSylvester period hPeriod (smoothMatrixFieldCoefficients period hPeriod root)
        (smoothMatrixFieldCoefficients period hPeriod velocity) row column) =
    smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
      (smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod
        (RegularFrame period hPeriod metric) metric.metric direction row column)
  apply congrArg (smoothToCanonicalPhysicalScalarC2JetCore period hPeriod)
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  have hValue := smoothMatrixSylvester_value period hPeriod root
    (smoothMatrixFieldCoefficients period hPeriod velocity) point
  have hEquation := regularGeneralMetricSmoothIdentityRootVelocity_sylvester period hPeriod
    metric shift direction hShift point
  exact congrFun (congrFun (hValue.trans hEquation) row) column

/-- Exact equality of all C² jets with the authentic root derivative, proved
by uniqueness of the completed Sylvester solution. -/
theorem regularGeneralMetricSmoothIdentityRootVelocity_lift
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (shift direction : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hShift : regularGeneralMetricSmoothC2Variation period hPeriod metric shift ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric) :
    smoothMatrixFieldToC2 period hPeriod
        (regularGeneralMetricSmoothIdentityRootVelocity period hPeriod metric shift direction hShift) =
      c2IdentityRootDerivative period hPeriod
        (regularGeneralMetricC2VariationMatrix period hPeriod metric shift)
        (regularGeneralMetricC2LorentzChartDomain_matrix_mem_root period hPeriod metric hShift).1
        (regularGeneralMetricC2VariationMatrix period hPeriod metric direction) := by
  let hRoot :=
    (regularGeneralMetricC2LorentzChartDomain_matrix_mem_root period hPeriod metric hShift).1
  let root := regularGeneralMetricC2IdentityRootMatrixField period hPeriod metric shift hRoot
  have hRegular : ∀ point, Function.Bijective (canonicalSylvesterOperator (root point)) :=
    regularGeneralMetricC2IdentityRootMatrixAt_sylvester_bijective period hPeriod metric shift hRoot
  apply (c2MatrixSylvesterEquiv period hPeriod root hRegular).injective
  change c2FiniteMatrixSylvester period hPeriod 4 (smoothMatrixFieldToC2 period hPeriod root)
      (smoothMatrixFieldToC2 period hPeriod
        (regularGeneralMetricSmoothIdentityRootVelocity period hPeriod metric shift direction hShift)) =
    c2FiniteMatrixSylvester period hPeriod 4 (smoothMatrixFieldToC2 period hPeriod root)
      (c2IdentityRootDerivative period hPeriod
        (regularGeneralMetricC2VariationMatrix period hPeriod metric shift) hRoot
        (regularGeneralMetricC2VariationMatrix period hPeriod metric direction))
  have hDerivative := c2IdentityRootDerivative_sylvester period hPeriod
    (regularGeneralMetricC2VariationMatrix period hPeriod metric shift) hRoot
    (regularGeneralMetricC2VariationMatrix period hPeriod metric direction)
  rw [regularGeneralMetricC2IdentityRoot_eq_smoothMatrixFieldToC2 period hPeriod
    metric shift hRoot] at hDerivative
  exact (smoothRootVelocity_lift_sylvester period hPeriod metric shift direction hShift
    ).trans hDerivative.symm

end
end P0EFTJanusSmoothIdentityRootVelocity4D
end JanusFormal
