import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPThroatFiniteFrameReconstruction4D

/-!
# Inverse-lift trace algebra for a redundant finite frame

This file supplies the purely finite-dimensional cancellation needed by the
H10 historical-trace bridge.  It is independent of the Janus geometry: an
identity extension of an intrinsic endomorphism acts on an encoded intrinsic
endomorphism exactly by composition.  Consequently any left inverse of that
lift cancels a factored encoding before taking the faithful trace.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPThroatFiniteFrameReconstruction4D

set_option autoImplicit false
noncomputable section

section RedundantFiniteFrameInverseTraceAlgebra

variable {E : Type*} [AddCommGroup E] [Module Real E]
  [FiniteDimensional Real E]
variable {dimension : Nat}

/-- Multiplying an encoded intrinsic operator by the identity extension of a
first operator gives the encoding of their intrinsic composition. -/
theorem redundantFiniteFrameLift_mul_encoding
    (analysis : E →ₗ[Real] (Fin dimension → Real))
    (synthesis : (Fin dimension → Real) →ₗ[Real] E)
    (hReconstruct : synthesis.comp analysis = LinearMap.id)
    (first second : E →ₗ[Real] E) :
    redundantFiniteFrameLift analysis synthesis first *
        redundantFiniteFrameEncoding analysis synthesis second =
      redundantFiniteFrameEncoding analysis synthesis (first.comp second) := by
  let projector :=
    redundantFiniteFrameEncoding analysis synthesis LinearMap.id
  let firstMatrix :=
    redundantFiniteFrameEncoding analysis synthesis first
  let secondMatrix :=
    redundantFiniteFrameEncoding analysis synthesis second
  let compositeMatrix :=
    redundantFiniteFrameEncoding analysis synthesis (first.comp second)
  have hProjectorSecond : projector * secondMatrix = secondMatrix := by
    simpa [projector, secondMatrix] using
      (redundantFiniteFrameEncoding_comp analysis synthesis hReconstruct
        LinearMap.id second).symm
  have hComposite : firstMatrix * secondMatrix = compositeMatrix := by
    simpa [firstMatrix, secondMatrix, compositeMatrix] using
      (redundantFiniteFrameEncoding_comp analysis synthesis hReconstruct
        first second).symm
  change (1 - projector + firstMatrix) * secondMatrix = compositeMatrix
  calc
    (1 - projector + firstMatrix) * secondMatrix =
        secondMatrix - projector * secondMatrix +
          firstMatrix * secondMatrix := by
      noncomm_ring
    _ = compositeMatrix := by
      rw [hProjectorSecond, hComposite]
      abel

/-- A left inverse of the faithful lift cancels an encoding whose intrinsic
operator factors through the lifted operator. -/
theorem redundantFiniteFrame_leftInverse_mul_encoding_of_factorization
    (analysis : E →ₗ[Real] (Fin dimension → Real))
    (synthesis : (Fin dimension → Real) →ₗ[Real] E)
    (hReconstruct : synthesis.comp analysis = LinearMap.id)
    (first source target : E →ₗ[Real] E)
    (inverseMatrix : Matrix (Fin dimension) (Fin dimension) Real)
    (hInverse : inverseMatrix *
        redundantFiniteFrameLift analysis synthesis first = 1)
    (hFactor : source = first.comp target) :
    inverseMatrix *
        redundantFiniteFrameEncoding analysis synthesis source =
      redundantFiniteFrameEncoding analysis synthesis target := by
  rw [hFactor, ← redundantFiniteFrameLift_mul_encoding
    analysis synthesis hReconstruct first target]
  rw [← Matrix.mul_assoc, hInverse, Matrix.one_mul]

/-- Trace form of the same cancellation.  The result is the intrinsic trace,
not the trace of an auxiliary coefficient-space extension. -/
theorem redundantFiniteFrame_leftInverse_trace_encoding_of_factorization
    (analysis : E →ₗ[Real] (Fin dimension → Real))
    (synthesis : (Fin dimension → Real) →ₗ[Real] E)
    (hReconstruct : synthesis.comp analysis = LinearMap.id)
    (first source target : E →ₗ[Real] E)
    (inverseMatrix : Matrix (Fin dimension) (Fin dimension) Real)
    (hInverse : inverseMatrix *
        redundantFiniteFrameLift analysis synthesis first = 1)
    (hFactor : source = first.comp target) :
    Matrix.trace
        (inverseMatrix *
          redundantFiniteFrameEncoding analysis synthesis source) =
      LinearMap.trace Real E target := by
  rw [redundantFiniteFrame_leftInverse_mul_encoding_of_factorization
    analysis synthesis hReconstruct first source target inverseMatrix hInverse
      hFactor]
  exact redundantFiniteFrameEncoding_trace analysis synthesis hReconstruct target

end RedundantFiniteFrameInverseTraceAlgebra

end
end P0EFTJanusProgramPThroatFiniteFrameReconstruction4D
end JanusFormal
