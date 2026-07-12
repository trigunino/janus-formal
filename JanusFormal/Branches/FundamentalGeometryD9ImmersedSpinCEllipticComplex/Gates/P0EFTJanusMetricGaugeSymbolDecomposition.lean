import Mathlib
import JanusFormal.Branches.FundamentalGeometryD9ImmersedSpinCEllipticComplex.Gates.P0EFTJanusGaugeFixedPrincipalSymbols

namespace JanusFormal
namespace P0EFTJanusMetricGaugeSymbolDecomposition

set_option autoImplicit false

open P0EFTJanusImmersionFiberAlgebra
open P0EFTJanusGaugeFixedPrincipalSymbols

/-- Subtraction of symmetric tensors. -/
def subSymmetric
    (first second : SymmetricTensor3) : SymmetricTensor3 :=
  { xx := first.xx - second.xx
    yy := first.yy - second.yy
    zz := first.zz - second.zz
    xy := first.xy - second.xy
    xz := first.xz - second.xz
    yz := first.yz - second.yz }

/-- de Donder is linear under subtraction. -/
theorem de_donder_sub_symmetric
    (covector : TangentVector3)
    (first second : SymmetricTensor3) :
    deDonderSymbol covector
        (subSymmetric first second) =
      subTangent
        (deDonderSymbol covector first)
        (deDonderSymbol covector second) := by
  ext <;>
    simp [deDonderSymbol, subSymmetric,
      subTangent, symmetricTrace] <;>
    ring

/-- Gauge vector extracted from a metric symbol. -/
noncomputable def gaugeVectorFromTensor
    (covector : TangentVector3)
    (tensor : SymmetricTensor3) : TangentVector3 :=
  scaleTangent
    (1 / normSquared covector)
    (deDonderSymbol covector tensor)

/-- Pure-gauge part of a metric symbol. -/
noncomputable def pureGaugeProjection
    (covector : TangentVector3)
    (tensor : SymmetricTensor3) : SymmetricTensor3 :=
  symGradientSymbol covector
    (gaugeVectorFromTensor covector tensor)

/-- de Donder-transverse remainder. -/
noncomputable def transverseProjection
    (covector : TangentVector3)
    (tensor : SymmetricTensor3) : SymmetricTensor3 :=
  subSymmetric tensor
    (pureGaugeProjection covector tensor)

/-- de Donder of the pure-gauge projection recovers the original gauge functional. -/
theorem de_donder_pure_gauge_projection
    (covector : TangentVector3)
    (hCovector : covector ≠ zeroTangent)
    (tensor : SymmetricTensor3) :
    deDonderSymbol covector
        (pureGaugeProjection covector tensor) =
      deDonderSymbol covector tensor := by
  have hNorm : normSquared covector ≠ 0 :=
    ne_of_gt (norm_squared_positive_of_nonzero
      covector hCovector)
  unfold pureGaugeProjection gaugeVectorFromTensor
  rw [de_donder_sym_gradient]
  apply TangentVector3.ext <;>
    simp [scaleTangent]
  · field_simp [hNorm]
  · field_simp [hNorm]
  · field_simp [hNorm]

/-- The complementary metric symbol is de Donder transverse. -/
theorem transverse_projection_is_de_donder_zero
    (covector : TangentVector3)
    (hCovector : covector ≠ zeroTangent)
    (tensor : SymmetricTensor3) :
    deDonderSymbol covector
        (transverseProjection covector tensor) = zeroTangent := by
  rw [transverseProjection,
    de_donder_sub_symmetric,
    de_donder_pure_gauge_projection covector hCovector tensor]
  ext <;> simp [subTangent, zeroTangent]

/-- Every metric symbol splits into pure gauge plus transverse part. -/
theorem metric_symbol_gauge_transverse_decomposition
    (covector : TangentVector3)
    (tensor : SymmetricTensor3) :
    addSymmetric
        (pureGaugeProjection covector tensor)
        (transverseProjection covector tensor) = tensor := by
  ext <;>
    simp [pureGaugeProjection, transverseProjection,
      addSymmetric, subSymmetric] <;>
    ring

/-- The diffeomorphism symbol is injective at nonzero covector. -/
theorem sym_gradient_symbol_injective
    (covector : TangentVector3)
    (hCovector : covector ≠ zeroTangent)
    (vector : TangentVector3)
    (hKernel :
      symGradientSymbol covector vector = zeroSymmetric) :
    vector = zeroTangent := by
  have hDeDonder := congrArg
    (deDonderSymbol covector) hKernel
  rw [de_donder_sym_gradient] at hDeDonder
  have hZeroRight :
      deDonderSymbol covector zeroSymmetric = zeroTangent := by
    ext <;>
      simp [deDonderSymbol, zeroSymmetric,
        symmetricTrace, zeroTangent]
  rw [hZeroRight] at hDeDonder
  exact scale_tangent_eq_zero
    (normSquared covector)
    (ne_of_gt (norm_squared_positive_of_nonzero
      covector hCovector))
    vector hDeDonder

/-- de Donder is surjective at nonzero covector. -/
theorem de_donder_symbol_surjective
    (covector : TangentVector3)
    (hCovector : covector ≠ zeroTangent)
    (target : TangentVector3) :
    ∃ tensor : SymmetricTensor3,
      deDonderSymbol covector tensor = target := by
  have hNorm : normSquared covector ≠ 0 :=
    ne_of_gt (norm_squared_positive_of_nonzero
      covector hCovector)
  refine ⟨symGradientSymbol covector
    (scaleTangent (1 / normSquared covector) target), ?_⟩
  rw [de_donder_sym_gradient]
  apply TangentVector3.ext <;>
    simp [scaleTangent]
  · field_simp [hNorm]
  · field_simp [hNorm]
  · field_simp [hNorm]

/-- Principal-symbol gauge splitting. -/
theorem metric_gauge_symbol_matrix
    (covector : TangentVector3)
    (hCovector : covector ≠ zeroTangent) :
    (∀ vector : TangentVector3,
      symGradientSymbol covector vector = zeroSymmetric →
        vector = zeroTangent) /\
    (∀ target : TangentVector3,
      ∃ tensor : SymmetricTensor3,
        deDonderSymbol covector tensor = target) /\
    (∀ tensor : SymmetricTensor3,
      deDonderSymbol covector
        (transverseProjection covector tensor) = zeroTangent) := by
  exact ⟨sym_gradient_symbol_injective covector hCovector,
    de_donder_symbol_surjective covector hCovector,
    transverse_projection_is_de_donder_zero covector hCovector⟩

/--
At principal-symbol level, the metric sector splits canonically into a
three-dimensional pure-diffeomorphism image and a three-dimensional de Donder
transverse complement. Lower-order curvature, trace and conformal-factor signs
still decide the physical Hessian and determinant contour.
-/
structure GlobalMetricBRSTStatus where
  diffeomorphismGroupActionLinearized : Prop
  killingOperatorConstructed : Prop
  deDonderGaugeDerived : Prop
  faddeevPopovOperatorDerived : Prop
  transverseBundleConstructed : Prop
  conformalFactorContourFixed : Prop
  lichnerowiczLowerOrderTermsComputed : Prop
  zeroModesAndKillingFieldsSeparated : Prop
  determinantSignsDerived : Prop


def globalMetricBRSTClosed
    (s : GlobalMetricBRSTStatus) : Prop :=
  s.diffeomorphismGroupActionLinearized /\
  s.killingOperatorConstructed /\
  s.deDonderGaugeDerived /\
  s.faddeevPopovOperatorDerived /\
  s.transverseBundleConstructed /\
  s.conformalFactorContourFixed /\
  s.lichnerowiczLowerOrderTermsComputed /\
  s.zeroModesAndKillingFieldsSeparated /\
  s.determinantSignsDerived

end P0EFTJanusMetricGaugeSymbolDecomposition
end JanusFormal
