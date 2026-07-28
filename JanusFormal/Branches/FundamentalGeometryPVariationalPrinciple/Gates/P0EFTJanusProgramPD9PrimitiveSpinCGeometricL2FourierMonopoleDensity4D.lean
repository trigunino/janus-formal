import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2SignedJointIsometry4D

/-!
# Fourier--monopole density bridge for the geometric SpinC completion

The independent geometric Hilbert space is the completion of all genuine
smooth SpinC sections.  Consequently it is enough to approximate every
embedded smooth section by the closed span of the explicit signed
Fourier--monopole blocks.  This file proves that reduction and promotes any
such core theorem to the ambient geometric Dirac unitary.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2FourierMonopoleDensity4D

set_option autoImplicit false
noncomputable section

open Set
open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2Pairing4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2SignedJointIsometry4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionCore4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev SmoothSection :=
  D9PrimitiveSpinCSmoothSection period hPeriod .positiveQuarter

private abbrev GeometricL2 :=
  D9PrimitiveSpinCGeometricL2Completion
    period hPeriod .positiveQuarter

/-- Concrete core form of Fourier--monopole completeness: every genuine
smooth section belongs to the closed signed spectral range. -/
def PrimitiveSpinCFourierMonopoleCoreComplete : Prop :=
  ∀ state : SmoothSection period hPeriod,
    d9PrimitiveSpinCGeometricL2Embedding
        period hPeriod .positiveQuarter state ∈
      closure
        (Set.range
          (primitiveSpinCGeometricL2SignedGlobalJointSynthesis
            period hPeriod))

/-- Density of the smooth geometric core promotes core completeness to
density of the signed synthesis in the whole independent completion. -/
theorem primitiveSpinCGeometricL2SignedGlobalDensity_of_coreComplete
    (hCore :
      PrimitiveSpinCFourierMonopoleCoreComplete period hPeriod) :
    PrimitiveSpinCGeometricL2SignedGlobalDensity period hPeriod := by
  change
    Dense
      (Set.range
        (primitiveSpinCGeometricL2SignedGlobalJointSynthesis
          period hPeriod))
  rw [dense_iff_closure_eq]
  apply Set.eq_univ_of_univ_subset
  intro state _
  have hEmbeddingDense :
      DenseRange
        (d9PrimitiveSpinCGeometricL2Embedding
          period hPeriod .positiveQuarter) :=
    d9PrimitiveSpinCGeometricL2Embedding_denseRange
      period hPeriod .positiveQuarter
  have hEmbeddingClosure :
      closure
          (Set.range
            (d9PrimitiveSpinCGeometricL2Embedding
              period hPeriod .positiveQuarter)) =
        Set.univ :=
    dense_iff_closure_eq.mp hEmbeddingDense
  have hRangeSubset :
      Set.range
          (d9PrimitiveSpinCGeometricL2Embedding
            period hPeriod .positiveQuarter) ⊆
        closure
          (Set.range
            (primitiveSpinCGeometricL2SignedGlobalJointSynthesis
              period hPeriod)) := by
    rintro _ ⟨smooth, rfl⟩
    exact hCore smooth
  have hClosureSubset :
      closure
          (Set.range
            (d9PrimitiveSpinCGeometricL2Embedding
              period hPeriod .positiveQuarter)) ⊆
        closure
          (Set.range
            (primitiveSpinCGeometricL2SignedGlobalJointSynthesis
              period hPeriod)) :=
    closure_minimal hRangeSubset isClosed_closure
  exact hClosureSubset (hEmbeddingClosure.symm ▸ Set.mem_univ state)

/-- Fourier--monopole completeness yields the unconditional-looking
geometric unitary only after its concrete core theorem has been supplied. -/
def primitiveSpinCGeometricL2SignedFourierMonopoleUnitary
    (hCore :
      PrimitiveSpinCFourierMonopoleCoreComplete period hPeriod) :
    PrimitiveSpinCGeometricL2SignedGlobalJointCoefficients
        period hPeriod ≃ₗᵢ[Complex]
      GeometricL2 period hPeriod :=
  primitiveSpinCGeometricL2SignedGlobalUnitary
    period hPeriod
    (primitiveSpinCGeometricL2SignedGlobalDensity_of_coreComplete
      period hPeriod hCore)

/-- The exact reduction certificate contains no analytic premise: it records
that proving Fourier--monopole approximation on genuine smooth sections is
sufficient for both ambient density and the geometric unitary. -/
structure ProgramPD9PrimitiveSpinCGeometricL2FourierMonopoleDensityCertificate4D
    where
  densityPromotion :
    PrimitiveSpinCFourierMonopoleCoreComplete period hPeriod →
      PrimitiveSpinCGeometricL2SignedGlobalDensity period hPeriod
  unitaryPromotion :
    PrimitiveSpinCFourierMonopoleCoreComplete period hPeriod →
      Nonempty
        (PrimitiveSpinCGeometricL2SignedGlobalJointCoefficients
            period hPeriod ≃ₗᵢ[Complex]
          GeometricL2 period hPeriod)

def programPD9PrimitiveSpinCGeometricL2FourierMonopoleDensityCertificate4D :
    ProgramPD9PrimitiveSpinCGeometricL2FourierMonopoleDensityCertificate4D
      period hPeriod where
  densityPromotion :=
    primitiveSpinCGeometricL2SignedGlobalDensity_of_coreComplete
      period hPeriod
  unitaryPromotion := fun hCore =>
    ⟨primitiveSpinCGeometricL2SignedFourierMonopoleUnitary
      period hPeriod hCore⟩

theorem primitiveSpinCGeometricL2FourierMonopoleDensity_gate :
    Nonempty
      (ProgramPD9PrimitiveSpinCGeometricL2FourierMonopoleDensityCertificate4D
        period hPeriod) :=
  ⟨programPD9PrimitiveSpinCGeometricL2FourierMonopoleDensityCertificate4D
    period hPeriod⟩

end
end P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2FourierMonopoleDensity4D
end JanusFormal
