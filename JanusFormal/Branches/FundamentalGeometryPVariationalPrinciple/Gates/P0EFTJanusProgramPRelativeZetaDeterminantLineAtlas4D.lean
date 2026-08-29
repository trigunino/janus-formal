import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeZetaDeterminantCocycle4D

/-!
# Determinant-line atlas from local relative zeta functions

The local nonzero zeta determinants provide canonical local frames.  Their
ratios are the transition functions of the determinant line; the local zeta
connection coefficients obey the exact gauge law on overlaps.

This file packages the resulting line-atlas certificate without choosing a
global trivialization.  It is suitable for parameter spaces requiring several
local zeta branches or several spectral cuts.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRelativeZetaDeterminantLineAtlas4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPRelativeZetaDeterminantCocycle4D

variable {Index : Type*}

/-- Local covariant derivative of one scalar first jet. -/
def relativeZetaLocalConnectionAt
    (atlas : RelativeZetaLocalFamilyAtlasData Index)
    (index : Index) (parameter : Real)
    (value derivative : Complex) : Complex :=
  derivative +
    relativeZetaLocalConnectionCoefficient atlas index parameter * value

/-- Each local determinant coordinate is parallel in its own frame. -/
theorem relativeZetaLocalDeterminant_parallel
    (atlas : RelativeZetaLocalFamilyAtlasData Index)
    (index : Index) (parameter : Real) :
    relativeZetaLocalConnectionAt atlas index parameter
        (relativeZetaLocalDeterminant atlas index parameter)
        (relativeZetaLocalDeterminantDerivative atlas index parameter) = 0 := by
  unfold relativeZetaLocalConnectionAt
    relativeZetaLocalConnectionCoefficient
    relativeZetaLocalDeterminantDerivative
  ring

/-- The local determinant sections glue through the transition cocycle. -/
theorem relativeZetaLocalDeterminant_transition
    (atlas : RelativeZetaLocalFamilyAtlasData Index)
    (first second : Index) (parameter : Real) :
    relativeZetaTransition atlas first second parameter *
        relativeZetaLocalDeterminant atlas first parameter =
      relativeZetaLocalDeterminant atlas second parameter := by
  unfold relativeZetaTransition
  field_simp [relativeZetaLocalDeterminant_ne_zero]

/-- Gauge covariance of an arbitrary local first jet.  If the second-frame
coordinate is `g_ij s_i`, its covariant derivative is `g_ij ∇_i s_i`. -/
theorem relativeZetaLocalConnection_gauge_covariant
    (atlas : RelativeZetaLocalFamilyAtlasData Index)
    (first second : Index) (parameter : Real)
    (value derivative : Complex) :
    relativeZetaLocalConnectionAt atlas second parameter
        (relativeZetaTransition atlas first second parameter * value)
        (relativeZetaTransitionDerivative atlas first second parameter * value +
          relativeZetaTransition atlas first second parameter * derivative) =
      relativeZetaTransition atlas first second parameter *
        relativeZetaLocalConnectionAt atlas first parameter value derivative := by
  unfold relativeZetaLocalConnectionAt
  have h :=
    relativeZetaTransition_connection_gauge atlas first second parameter
  calc
    relativeZetaTransitionDerivative atlas first second parameter * value +
          relativeZetaTransition atlas first second parameter * derivative +
        relativeZetaLocalConnectionCoefficient atlas second parameter *
          (relativeZetaTransition atlas first second parameter * value) =
      (relativeZetaTransitionDerivative atlas first second parameter +
          relativeZetaLocalConnectionCoefficient atlas second parameter *
            relativeZetaTransition atlas first second parameter) * value +
        relativeZetaTransition atlas first second parameter * derivative := by ring
    _ = (relativeZetaTransition atlas first second parameter *
          relativeZetaLocalConnectionCoefficient atlas first parameter) * value +
        relativeZetaTransition atlas first second parameter * derivative := by rw [h]
    _ = relativeZetaTransition atlas first second parameter *
        (derivative + relativeZetaLocalConnectionCoefficient atlas first parameter * value) := by ring

/-- Complete local determinant-line atlas certificate. -/
structure RelativeZetaDeterminantLineAtlasCertificate
    (atlas : RelativeZetaLocalFamilyAtlasData Index) : Prop where
  local_nonzero : ∀ index parameter,
    relativeZetaLocalDeterminant atlas index parameter ≠ 0
  local_parallel : ∀ index parameter,
    relativeZetaLocalConnectionAt atlas index parameter
        (relativeZetaLocalDeterminant atlas index parameter)
        (relativeZetaLocalDeterminantDerivative atlas index parameter) = 0
  transition_nonzero : ∀ first second parameter,
    relativeZetaTransition atlas first second parameter ≠ 0
  transition_self : ∀ index parameter,
    relativeZetaTransition atlas index index parameter = 1
  transition_cocycle : ∀ first second third parameter,
    relativeZetaTransition atlas second third parameter *
        relativeZetaTransition atlas first second parameter =
      relativeZetaTransition atlas first third parameter
  section_gluing : ∀ first second parameter,
    relativeZetaTransition atlas first second parameter *
        relativeZetaLocalDeterminant atlas first parameter =
      relativeZetaLocalDeterminant atlas second parameter
  connection_gauge : ∀ first second parameter value derivative,
    relativeZetaLocalConnectionAt atlas second parameter
        (relativeZetaTransition atlas first second parameter * value)
        (relativeZetaTransitionDerivative atlas first second parameter * value +
          relativeZetaTransition atlas first second parameter * derivative) =
      relativeZetaTransition atlas first second parameter *
        relativeZetaLocalConnectionAt atlas first parameter value derivative

/-- The local zeta family canonically produces its determinant-line atlas. -/
def relativeZetaDeterminantLineAtlasCertificate
    (atlas : RelativeZetaLocalFamilyAtlasData Index) :
    RelativeZetaDeterminantLineAtlasCertificate atlas where
  local_nonzero := relativeZetaLocalDeterminant_ne_zero atlas
  local_parallel := relativeZetaLocalDeterminant_parallel atlas
  transition_nonzero := relativeZetaTransition_ne_zero atlas
  transition_self := relativeZetaTransition_self atlas
  transition_cocycle := relativeZetaTransition_cocycle atlas
  section_gluing := relativeZetaLocalDeterminant_transition atlas
  connection_gauge := relativeZetaLocalConnection_gauge_covariant atlas

/-- Public determinant-line atlas gate. -/
theorem relative_zeta_determinant_line_atlas_gate
    (atlas : RelativeZetaLocalFamilyAtlasData Index) :
    RelativeZetaDeterminantLineAtlasCertificate atlas :=
  relativeZetaDeterminantLineAtlasCertificate atlas

end
end P0EFTJanusProgramPRelativeZetaDeterminantLineAtlas4D
end JanusFormal
