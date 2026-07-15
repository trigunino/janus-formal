import Mathlib
import JanusFormal.Branches.FundamentalGeometryD9ImmersedSpinCEllipticComplex.Gates.P0EFTJanusGaugeFixedPrincipalSymbols

namespace JanusFormal
namespace P0EFTJanusDeRhamSymbolExactness

set_option autoImplicit false

open P0EFTJanusImmersionFiberAlgebra
open P0EFTJanusGaugeFixedPrincipalSymbols

local notation "janusCross" =>
  P0EFTJanusGaugeFixedPrincipalSymbols.crossProduct

/-- Cross product is linear in its second argument. -/
theorem cross_scale_right
    (covector field : TangentVector3)
    (scalar : ℝ) :
    janusCross covector (scaleTangent scalar field) =
      scaleTangent scalar (janusCross covector field) := by
  ext <;>
    simp [P0EFTJanusGaugeFixedPrincipalSymbols.crossProduct,
      scaleTangent] <;>
    ring

/-- The gradient symbol is injective for nonzero covector. -/
theorem gradient_symbol_injective
    (covector : TangentVector3)
    (hCovector : covector ≠ zeroTangent)
    (scalar : ℝ)
    (hKernel : gradientSymbol covector scalar = zeroTangent) :
    scalar = 0 := by
  have hDivergence := congrArg
    (divergenceSymbol covector) hKernel
  rw [divergence_gradient_symbol] at hDivergence
  have hRight : divergenceSymbol covector zeroTangent = 0 := by
    simp [divergenceSymbol, tangentDot, zeroTangent]
  rw [hRight] at hDivergence
  exact (mul_eq_zero.mp hDivergence).resolve_left
    (ne_of_gt (norm_squared_positive_of_nonzero
      covector hCovector))

/-- Kernel of the cross symbol is exactly the image of the gradient symbol. -/
theorem cross_kernel_is_gradient_image
    (covector : TangentVector3)
    (hCovector : covector ≠ zeroTangent)
    (field : TangentVector3)
    (hKernel : janusCross covector field = zeroTangent) :
    ∃ scalar : ℝ,
      gradientSymbol covector scalar = field := by
  have hNorm : normSquared covector ≠ 0 :=
    ne_of_gt (norm_squared_positive_of_nonzero
      covector hCovector)
  have hDouble :
      janusCross covector (janusCross covector field) =
        zeroTangent := by
    rw [hKernel]
    ext <;> simp [P0EFTJanusGaugeFixedPrincipalSymbols.crossProduct,
      zeroTangent]
  have hTriple := cross_cross_identity covector field
  rw [hDouble] at hTriple
  have hx := congrArg TangentVector3.x hTriple
  have hy := congrArg TangentVector3.y hTriple
  have hz := congrArg TangentVector3.z hTriple
  simp [zeroTangent, subTangent, scaleTangent] at hx hy hz
  refine ⟨tangentDot covector field / normSquared covector, ?_⟩
  apply TangentVector3.ext
  · simp [gradientSymbol, scaleTangent]
    field_simp [hNorm]
    nlinarith [hx]
  · simp [gradientSymbol, scaleTangent]
    field_simp [hNorm]
    nlinarith [hy]
  · simp [gradientSymbol, scaleTangent]
    field_simp [hNorm]
    nlinarith [hz]

/-- Kernel of divergence is exactly the image of the cross symbol. -/
theorem divergence_kernel_is_cross_image
    (covector : TangentVector3)
    (hCovector : covector ≠ zeroTangent)
    (field : TangentVector3)
    (hKernel : divergenceSymbol covector field = 0) :
    ∃ potential : TangentVector3,
      janusCross covector potential = field := by
  have hNorm : normSquared covector ≠ 0 :=
    ne_of_gt (norm_squared_positive_of_nonzero
      covector hCovector)
  have hDot : tangentDot covector field = 0 := by
    exact hKernel
  refine ⟨scaleTangent
    (-1 / normSquared covector)
    (janusCross covector field), ?_⟩
  rw [cross_scale_right, cross_cross_identity]
  apply TangentVector3.ext <;>
    simp [scaleTangent, subTangent, hDot] <;>
    field_simp [hNorm]

/-- Divergence is surjective for nonzero covector. -/
theorem divergence_symbol_surjective
    (covector : TangentVector3)
    (hCovector : covector ≠ zeroTangent)
    (target : ℝ) :
    ∃ field : TangentVector3,
      divergenceSymbol covector field = target := by
  have hNorm : normSquared covector ≠ 0 :=
    ne_of_gt (norm_squared_positive_of_nonzero
      covector hCovector)
  refine ⟨gradientSymbol covector
    (target / normSquared covector), ?_⟩
  rw [divergence_gradient_symbol]
  field_simp [hNorm]

/-- Full exactness matrix of the de Rham symbol complex in three dimensions. -/
theorem de_rham_symbol_complex_exact
    (covector : TangentVector3)
    (hCovector : covector ≠ zeroTangent) :
    (∀ scalar : ℝ,
      gradientSymbol covector scalar = zeroTangent → scalar = 0) /\
    (∀ field : TangentVector3,
      janusCross covector field = zeroTangent →
        ∃ scalar : ℝ,
          gradientSymbol covector scalar = field) /\
    (∀ field : TangentVector3,
      divergenceSymbol covector field = 0 →
        ∃ potential : TangentVector3,
          janusCross covector potential = field) /\
    (∀ target : ℝ,
      ∃ field : TangentVector3,
        divergenceSymbol covector field = target) := by
  exact ⟨gradient_symbol_injective covector hCovector,
    cross_kernel_is_gradient_image covector hCovector,
    divergence_kernel_is_cross_image covector hCovector,
    divergence_symbol_surjective covector hCovector⟩

/-- Fiber ranks of the three-dimensional de Rham complex. -/
def deRhamRanks : List ℤ := [1, 3, 3, 1]

/-- Its alternating fiber-rank Euler characteristic vanishes. -/
theorem de_rham_fiber_rank_euler_zero :
    (1 : ℤ) - 3 + 3 - 1 = 0 := by
  norm_num

/--
The `U(1)` gauge/ghost sector is therefore not merely Laplace-type after gauge
fixing: its underlying principal-symbol sequence is an exact elliptic complex.
Global cohomology and zero modes remain dependent on the throat topology and
chosen flat/monopole twists.
-/
structure GlobalDeRhamComplexStatus where
  differentialFormsConstructed : Prop
  twistedExteriorDerivativeConstructed : Prop
  dSquaredZeroProved : Prop
  adjointConstructed : Prop
  absoluteOrPeriodicBoundaryConditionsDerived : Prop
  principalSymbolIdentified : Prop
  ellipticityProved : Prop
  twistedCohomologyComputed : Prop
  zeroModesSeparated : Prop
  determinantPrimeDefined : Prop


def globalDeRhamComplexClosed
    (s : GlobalDeRhamComplexStatus) : Prop :=
  s.differentialFormsConstructed /\
  s.twistedExteriorDerivativeConstructed /\
  s.dSquaredZeroProved /\
  s.adjointConstructed /\
  s.absoluteOrPeriodicBoundaryConditionsDerived /\
  s.principalSymbolIdentified /\
  s.ellipticityProved /\
  s.twistedCohomologyComputed /\
  s.zeroModesSeparated /\
  s.determinantPrimeDefined

end P0EFTJanusDeRhamSymbolExactness
end JanusFormal
