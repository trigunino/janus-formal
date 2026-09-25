import Mathlib.LinearAlgebra.Trace
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Trace contraction through a finite, possibly redundant, family. The
coefficient operation is used only after synthesis; no Gram inverse or basis
assumption on the family is introduced. -/
namespace JanusFormal.P0EFTJanusProgramPT12FiniteCovectorTrace4D
set_option autoImplicit false
noncomputable section
open scoped BigOperators

variable {I E : Type*} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup E] [NormedSpace Real E] [FiniteDimensional Real E]

def finiteCovectorTraceSynthesis (vectors : I → E) : (I → Real) →ₗ[Real] E where
  toFun coefficients := ∑ i, coefficients i • vectors i
  map_add' := by intro first second; simp [add_smul, Finset.sum_add_distrib]
  map_smul' := by intro scalar coefficients; simp [Finset.smul_sum, smul_smul]

def finiteCovectorTraceReadings (vectors : I → E) :
    (E →L[Real] Real) →ₗ[Real] (I → Real) where
  toFun covector i := covector (vectors i)
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

omit [FiniteDimensional Real E] in @[simp] theorem finiteCovectorTraceSynthesis_basis (vectors : I → E) (i : I) :
    finiteCovectorTraceSynthesis vectors (Pi.basisFun Real I i) = vectors i := by
  simp [finiteCovectorTraceSynthesis, Pi.basisFun_apply]

/-- Rectangular cyclicity converts the coefficient trace to the synthesized
endomorphism, even when the finite family has linear dependencies. -/
theorem finiteCovectorTrace_eq_trace (vectors : I → E) (weights : Matrix I I Real)
    (form : E →L[Real] E →L[Real] Real) :
    Matrix.trace (weights * Matrix.of (fun row column => form (vectors column) (vectors row))) =
      LinearMap.trace Real E
        ((finiteCovectorTraceSynthesis vectors).comp
          (weights.mulVecLin.comp ((finiteCovectorTraceReadings vectors).comp form.toLinearMap))) := by
  let coefficients := weights.mulVecLin.comp
    ((finiteCovectorTraceReadings vectors).comp form.toLinearMap)
  have hMatrix :
      LinearMap.toMatrix (Pi.basisFun Real I) (Pi.basisFun Real I)
        (coefficients.comp (finiteCovectorTraceSynthesis vectors)) =
      weights * Matrix.of (fun row column => form (vectors column) (vectors row)) := by
    ext row column
    simp [coefficients, finiteCovectorTraceReadings, finiteCovectorTraceSynthesis,
      Matrix.mul_apply, Matrix.mulVec, dotProduct]
  rw [← hMatrix, ← LinearMap.trace_eq_matrix_trace Real (Pi.basisFun Real I)]
  exact (LinearMap.trace_comp_comm' coefficients (finiteCovectorTraceSynthesis vectors)).symm

/-- A coefficient solver which synthesizes to the actual sharp contracts any
bilinear form with that sharp. This is pure finite-dimensional algebra. -/
theorem finiteCovectorTrace_eq_sharp_trace (vectors : I → E) (weights : Matrix I I Real)
    (sharp : (E →L[Real] Real) →L[Real] E)
    (hSharp : ∀ covector,
      finiteCovectorTraceSynthesis vectors
        (weights.mulVec (fun i => covector (vectors i))) = sharp covector)
    (form : E →L[Real] E →L[Real] Real) :
    Matrix.trace (weights * Matrix.of (fun row column => form (vectors column) (vectors row))) =
      LinearMap.trace Real E (sharp.toLinearMap.comp form.toLinearMap) := by
  rw [finiteCovectorTrace_eq_trace]
  congr 1
  ext vector
  exact hSharp (form vector)

end
end JanusFormal.P0EFTJanusProgramPT12FiniteCovectorTrace4D
