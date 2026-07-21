import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCoverLorentzGramFrechet4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntrinsicLorentzMetricDescent4D

/-!
# Algebraic identity of the descended Lorentz--Gram tensor

The canonical Lorentz--Gram tensor is already constructed from the actual
cover immersion and descended to the true effective D8 quotient.  This gate
defines the zero-order identity operator which extracts the skew part of an
arbitrary smooth covariant two-tensor.  Its kernel is exactly pointwise
symmetry, and the descended Lorentz--Gram output lies in that kernel.

The pullback theorem below keeps the construction tied to the genuine ambient
Gram formula on the cover.  This is a restricted algebraic `B_sym K = 0`; it
is not the differential Bianchi operator, a global compatibility complex, or
a Sobolev statement.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusQuotientLorentzGramAlgebraicIdentity4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open scoped Manifold ContDiff RealInnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusIntrinsicCoverLorentzTensor4D
open P0EFTJanusMappingTorusIntrinsicLorentzMetricDescent4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveCover := MappingTorusCover (sphereData period hPeriod)
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

local instance effectiveCoverChartedSpace :
    ChartedSpace CoverModel (EffectiveCover period hPeriod) :=
  reflectedSphereCoverChartedSpace period hPeriod

local instance effectiveCoverIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveCover period hPeriod) :=
  reflectedSphereCover_isManifold period hPeriod

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

private abbrev CoverTangent
    (point : EffectiveCover period hPeriod) :=
  TangentSpace coverModelWithCorners point

private abbrev QuotientTangent
    (point : EffectiveQuotient period hPeriod) :=
  TangentSpace coverModelWithCorners point

/-- Pointwise identity fields which can record the skew defect of a quotient
covariant two-tensor. -/
abbrev QuotientTensorAlgebraicIdentityField :=
  (point : EffectiveQuotient period hPeriod) →
    QuotientTangent period hPeriod point →
      QuotientTangent period hPeriod point → Real

/-- The zero-order identity operator `B_sym`: extract the skew part of a
genuine smooth covariant two-tensor on D8. -/
def quotientTensorAlgebraicSymmetryIdentityOperator
    (tensor : SmoothCovariantTwoTensor period hPeriod) :
    QuotientTensorAlgebraicIdentityField period hPeriod :=
  fun point first second =>
    tensor point first second - tensor point second first

/-- The identity operator has exactly the symmetric tensors as its kernel. -/
theorem quotientTensorAlgebraicSymmetryIdentityOperator_eq_zero_iff
    (tensor : SmoothCovariantTwoTensor period hPeriod) :
    quotientTensorAlgebraicSymmetryIdentityOperator period hPeriod tensor = 0 ↔
      IsSymmetric period hPeriod tensor := by
  constructor
  · intro hZero point first second
    have hComponent := congrFun (congrFun (congrFun hZero point) first) second
    change tensor point first second - tensor point second first = 0 at hComponent
    exact sub_eq_zero.mp hComponent
  · intro hSymmetric
    funext point first second
    exact sub_eq_zero.mpr (hSymmetric point first second)

/-- The actual Lorentz--Gram output on the quotient: the unique smooth tensor
whose pullback is the ambient-product Gram tensor of the cover immersion. -/
def quotientCanonicalLorentzGramCompatibilityOutput :
    SmoothCovariantTwoTensor period hPeriod :=
  (intrinsicTensorQuotientDescent period hPeriod).tensor

/-- Pullback of the quotient output is the literal Lorentz--Gram expression
of the actual cover immersion derivative. -/
theorem quotientCanonicalLorentzGramCompatibilityOutput_pullback
    (point : EffectiveCover period hPeriod)
    (first second : CoverTangent period hPeriod point) :
    quotientCanonicalLorentzGramCompatibilityOutput period hPeriod
        (mappingTorusMk (sphereData period hPeriod) point)
        (mfderiv coverModelWithCorners coverModelWithCorners
          (mappingTorusMk (sphereData period hPeriod)) point first)
        (mfderiv coverModelWithCorners coverModelWithCorners
          (mappingTorusMk (sphereData period hPeriod)) point second) =
      inner Real (coverAmbientDerivative period hPeriod point first).1
          (coverAmbientDerivative period hPeriod point second).1 -
        (coverAmbientDerivative period hPeriod point first).2 *
          (coverAmbientDerivative period hPeriod point second).2 := by
  rw [quotientCanonicalLorentzGramCompatibilityOutput,
    (intrinsicTensorQuotientDescent period hPeriod).pullback,
    intrinsicCoverLorentzTensor_apply]

/-- Restricted, literal `B_sym K = 0` on the true effective D8 quotient. -/
theorem quotientTensorAlgebraicSymmetryIdentity_comp_lorentzGram_eq_zero :
    quotientTensorAlgebraicSymmetryIdentityOperator period hPeriod
        (quotientCanonicalLorentzGramCompatibilityOutput period hPeriod) = 0 := by
  apply
    (quotientTensorAlgebraicSymmetryIdentityOperator_eq_zero_iff
      period hPeriod
      (quotientCanonicalLorentzGramCompatibilityOutput period hPeriod)).2
  exact
    (intrinsicTensorQuotientDescent period hPeriod).toSymmetricTensor.symmetric

end

end P0EFTJanusMappingTorusQuotientLorentzGramAlgebraicIdentity4D
end JanusFormal
