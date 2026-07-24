import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarGraphPoissonDirichletToNeumann4D

/-!
# Krein resolvent formula for scalar graph boundary conditions

At a fixed real spectral parameter, assume a Dirichlet Poisson operator and a
bounded Dirichlet resolvent on the completed graph.  For a bounded Robin
operator `B`, the boundary Schur complement is `DtN - B`.

Whenever that Schur complement has a bounded two-sided inverse, the Robin
resolvent is constructed explicitly and satisfies

`R_B - R_D = - P (DtN - B)⁻¹ gamma_1 R_D`.

The proof also establishes the source equation, Robin boundary law and
uniqueness.  This is the infinite-dimensional counterpart of the finite Schur
complement already used in Program P-A.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarGraphKreinResolventFormula4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarOperatorGraphCompletion4D
open P0EFTJanusMappingTorusScalarGraphPoissonDirichletToNeumann4D

universe u v w

variable {Domain : Type u} {Ambient : Type v} {Trace : Type w}
  [AddCommGroup Domain] [Module Real Domain]
  [NormedAddCommGroup Ambient] [InnerProductSpace Real Ambient]
  [CompleteSpace Ambient]
  [NormedAddCommGroup Trace] [InnerProductSpace Real Trace]
  [CompleteSpace Trace]

/-- Bounded Dirichlet resolvent on the completed graph. -/
structure CanonicalScalarGraphDirichletResolventData
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real) where
  resolvent : Ambient →L[Real] CanonicalScalarOperatorGraphSpace data
  equation : ∀ source : Ambient,
    canonicalScalarGraphShiftedOperator data spectralParameter
      (resolvent source) = source
  value_zero : ∀ source : Ambient,
    canonicalScalarCompletedValueTrace data traceBound (resolvent source) = 0
  unique : ∀ (field : CanonicalScalarOperatorGraphSpace data) (source : Ambient),
    canonicalScalarGraphShiftedOperator data spectralParameter field = source →
    canonicalScalarCompletedValueTrace data traceBound field = 0 →
    field = resolvent source

/-- Bounded Robin resolvent on the completed graph. -/
structure CanonicalScalarGraphRobinResolventData
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (robin : Trace →L[Real] Trace) where
  resolvent : Ambient →L[Real] CanonicalScalarOperatorGraphSpace data
  equation : ∀ source : Ambient,
    canonicalScalarGraphShiftedOperator data spectralParameter
      (resolvent source) = source
  boundary : ∀ source : Ambient,
    canonicalScalarCompletedNormalTrace data traceBound (resolvent source) =
      robin (canonicalScalarCompletedValueTrace data traceBound (resolvent source))
  unique : ∀ (field : CanonicalScalarOperatorGraphSpace data) (source : Ambient),
    canonicalScalarGraphShiftedOperator data spectralParameter field = source →
    canonicalScalarCompletedNormalTrace data traceBound field =
      robin (canonicalScalarCompletedValueTrace data traceBound field) →
    field = resolvent source

/-- Bounded two-sided inverse of the boundary Schur complement. -/
structure CanonicalScalarGraphBoundarySchurInverseData
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (poissonData : CanonicalScalarGraphDirichletPoissonData
      data traceBound spectralParameter)
    (robin : Trace →L[Real] Trace) where
  inverse : Trace →L[Real] Trace
  left_inverse : ∀ boundary : Trace,
    canonicalScalarGraphBoundarySchurOperator
        data traceBound spectralParameter poissonData robin
        (inverse boundary) = boundary
  right_inverse : ∀ boundary : Trace,
    inverse (canonicalScalarGraphBoundarySchurOperator
      data traceBound spectralParameter poissonData robin boundary) = boundary

/-- Boundary correction applied to a Dirichlet source solution. -/
def canonicalScalarGraphKreinBoundaryCorrection
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (poissonData : CanonicalScalarGraphDirichletPoissonData
      data traceBound spectralParameter)
    (dirichlet : CanonicalScalarGraphDirichletResolventData
      data traceBound spectralParameter)
    (robin : Trace →L[Real] Trace)
    (schurInverse : CanonicalScalarGraphBoundarySchurInverseData
      data traceBound spectralParameter poissonData robin) :
    Ambient →L[Real] CanonicalScalarOperatorGraphSpace data :=
  poissonData.poisson.comp
    (schurInverse.inverse.comp
      ((canonicalScalarCompletedNormalTrace data traceBound).comp
        dirichlet.resolvent))

/-- Explicit Robin resolvent produced by the Krein correction. -/
def canonicalScalarGraphKreinRobinResolvent
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (poissonData : CanonicalScalarGraphDirichletPoissonData
      data traceBound spectralParameter)
    (dirichlet : CanonicalScalarGraphDirichletResolventData
      data traceBound spectralParameter)
    (robin : Trace →L[Real] Trace)
    (schurInverse : CanonicalScalarGraphBoundarySchurInverseData
      data traceBound spectralParameter poissonData robin) :
    Ambient →L[Real] CanonicalScalarOperatorGraphSpace data :=
  dirichlet.resolvent -
    canonicalScalarGraphKreinBoundaryCorrection
      data traceBound spectralParameter poissonData dirichlet robin schurInverse

@[simp] theorem canonicalScalarGraphKreinRobinResolvent_apply
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (poissonData : CanonicalScalarGraphDirichletPoissonData
      data traceBound spectralParameter)
    (dirichlet : CanonicalScalarGraphDirichletResolventData
      data traceBound spectralParameter)
    (robin : Trace →L[Real] Trace)
    (schurInverse : CanonicalScalarGraphBoundarySchurInverseData
      data traceBound spectralParameter poissonData robin)
    (source : Ambient) :
    canonicalScalarGraphKreinRobinResolvent
        data traceBound spectralParameter poissonData dirichlet robin schurInverse source =
      dirichlet.resolvent source -
        poissonData.poisson
          (schurInverse.inverse
            (canonicalScalarCompletedNormalTrace data traceBound
              (dirichlet.resolvent source))) :=
  rfl

/-- The Krein candidate solves the same bulk source equation. -/
theorem canonicalScalarGraphKreinRobinResolvent_equation
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (poissonData : CanonicalScalarGraphDirichletPoissonData
      data traceBound spectralParameter)
    (dirichlet : CanonicalScalarGraphDirichletResolventData
      data traceBound spectralParameter)
    (robin : Trace →L[Real] Trace)
    (schurInverse : CanonicalScalarGraphBoundarySchurInverseData
      data traceBound spectralParameter poissonData robin)
    (source : Ambient) :
    canonicalScalarGraphShiftedOperator data spectralParameter
      (canonicalScalarGraphKreinRobinResolvent
        data traceBound spectralParameter poissonData dirichlet robin schurInverse source) =
      source := by
  rw [canonicalScalarGraphKreinRobinResolvent_apply, map_sub,
    dirichlet.equation, poissonData.homogeneous, sub_zero]

/-- The Krein candidate satisfies the Robin boundary law. -/
theorem canonicalScalarGraphKreinRobinResolvent_boundary
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (poissonData : CanonicalScalarGraphDirichletPoissonData
      data traceBound spectralParameter)
    (dirichlet : CanonicalScalarGraphDirichletResolventData
      data traceBound spectralParameter)
    (robin : Trace →L[Real] Trace)
    (schurInverse : CanonicalScalarGraphBoundarySchurInverseData
      data traceBound spectralParameter poissonData robin)
    (source : Ambient) :
    canonicalScalarCompletedNormalTrace data traceBound
        (canonicalScalarGraphKreinRobinResolvent
          data traceBound spectralParameter poissonData dirichlet robin schurInverse source) =
      robin (canonicalScalarCompletedValueTrace data traceBound
        (canonicalScalarGraphKreinRobinResolvent
          data traceBound spectralParameter poissonData dirichlet robin schurInverse source)) := by
  let normal := canonicalScalarCompletedNormalTrace data traceBound
    (dirichlet.resolvent source)
  let boundary := schurInverse.inverse normal
  have hSchur := schurInverse.left_inverse normal
  change canonicalScalarCompletedNormalTrace data traceBound
      (dirichlet.resolvent source - poissonData.poisson boundary) =
    robin (canonicalScalarCompletedValueTrace data traceBound
      (dirichlet.resolvent source - poissonData.poisson boundary))
  rw [map_sub, map_sub, dirichlet.value_zero, poissonData.value_trace,
    zero_sub, map_neg]
  change normal -
      canonicalScalarGraphDirichletToNeumann
        data traceBound spectralParameter poissonData boundary =
    -robin boundary
  change canonicalScalarGraphDirichletToNeumann
        data traceBound spectralParameter poissonData boundary - robin boundary = normal
    at hSchur
  rw [← hSchur]
  abel

/-- Uniqueness of the Robin source solution constructed by the Krein formula. -/
theorem canonicalScalarGraphKreinRobinResolvent_unique
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (poissonData : CanonicalScalarGraphDirichletPoissonData
      data traceBound spectralParameter)
    (dirichlet : CanonicalScalarGraphDirichletResolventData
      data traceBound spectralParameter)
    (robin : Trace →L[Real] Trace)
    (schurInverse : CanonicalScalarGraphBoundarySchurInverseData
      data traceBound spectralParameter poissonData robin)
    (field : CanonicalScalarOperatorGraphSpace data) (source : Ambient)
    (hEquation : canonicalScalarGraphShiftedOperator
      data spectralParameter field = source)
    (hBoundary : canonicalScalarCompletedNormalTrace data traceBound field =
      robin (canonicalScalarCompletedValueTrace data traceBound field)) :
    field = canonicalScalarGraphKreinRobinResolvent
      data traceBound spectralParameter poissonData dirichlet robin schurInverse source := by
  let candidate := canonicalScalarGraphKreinRobinResolvent
    data traceBound spectralParameter poissonData dirichlet robin schurInverse source
  let difference := field - candidate
  have hDifferenceEquation :
      canonicalScalarGraphShiftedOperator data spectralParameter difference = 0 := by
    have hCandidateEquation :
        canonicalScalarGraphShiftedOperator data spectralParameter candidate = source := by
      simpa only [candidate] using
        canonicalScalarGraphKreinRobinResolvent_equation
          data traceBound spectralParameter poissonData dirichlet robin schurInverse source
    simp only [difference, map_sub, hEquation, hCandidateEquation, sub_self]
  have hDifferencePoisson :
      difference = poissonData.poisson
        (canonicalScalarCompletedValueTrace data traceBound difference) :=
    poissonData.reconstruct data traceBound spectralParameter difference
      hDifferenceEquation
  have hDifferenceBoundary :
      canonicalScalarCompletedNormalTrace data traceBound difference =
        robin (canonicalScalarCompletedValueTrace data traceBound difference) := by
    dsimp [difference]
    rw [map_sub, map_sub, hBoundary,
      canonicalScalarGraphKreinRobinResolvent_boundary]
    rw [map_sub]
  let boundary := canonicalScalarCompletedValueTrace data traceBound difference
  have hKernel : canonicalScalarGraphBoundarySchurOperator
      data traceBound spectralParameter poissonData robin boundary = 0 := by
    change canonicalScalarGraphDirichletToNeumann
        data traceBound spectralParameter poissonData boundary - robin boundary = 0
    have hNormal := congrArg
      (canonicalScalarCompletedNormalTrace data traceBound) hDifferencePoisson
    change canonicalScalarCompletedNormalTrace data traceBound difference =
      canonicalScalarGraphDirichletToNeumann
        data traceBound spectralParameter poissonData boundary at hNormal
    exact sub_eq_zero.mpr (hNormal.symm.trans hDifferenceBoundary)
  have hBoundaryZero : boundary = 0 := by
    calc
      boundary = schurInverse.inverse
          (canonicalScalarGraphBoundarySchurOperator
            data traceBound spectralParameter poissonData robin boundary) :=
        (schurInverse.right_inverse boundary).symm
      _ = schurInverse.inverse 0 := by rw [hKernel]
      _ = 0 := map_zero _
  have hDifferenceZero : difference = 0 := by
    calc
      difference = poissonData.poisson boundary := hDifferencePoisson
      _ = poissonData.poisson 0 := congrArg poissonData.poisson hBoundaryZero
      _ = 0 := map_zero _
  exact sub_eq_zero.mp hDifferenceZero

/-- Complete Robin resolvent data generated by the Schur inverse. -/
def canonicalScalarGraphKreinRobinResolventData
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (poissonData : CanonicalScalarGraphDirichletPoissonData
      data traceBound spectralParameter)
    (dirichlet : CanonicalScalarGraphDirichletResolventData
      data traceBound spectralParameter)
    (robin : Trace →L[Real] Trace)
    (schurInverse : CanonicalScalarGraphBoundarySchurInverseData
      data traceBound spectralParameter poissonData robin) :
    CanonicalScalarGraphRobinResolventData
      data traceBound spectralParameter robin where
  resolvent := canonicalScalarGraphKreinRobinResolvent
    data traceBound spectralParameter poissonData dirichlet robin schurInverse
  equation := canonicalScalarGraphKreinRobinResolvent_equation
    data traceBound spectralParameter poissonData dirichlet robin schurInverse
  boundary := canonicalScalarGraphKreinRobinResolvent_boundary
    data traceBound spectralParameter poissonData dirichlet robin schurInverse
  unique := canonicalScalarGraphKreinRobinResolvent_unique
    data traceBound spectralParameter poissonData dirichlet robin schurInverse

/-- Exact graph-valued Krein resolvent formula. -/
theorem canonicalScalarGraphKrein_resolvent_formula
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (poissonData : CanonicalScalarGraphDirichletPoissonData
      data traceBound spectralParameter)
    (dirichlet : CanonicalScalarGraphDirichletResolventData
      data traceBound spectralParameter)
    (robin : Trace →L[Real] Trace)
    (schurInverse : CanonicalScalarGraphBoundarySchurInverseData
      data traceBound spectralParameter poissonData robin) :
    (canonicalScalarGraphKreinRobinResolventData
        data traceBound spectralParameter poissonData dirichlet robin schurInverse).resolvent -
      dirichlet.resolvent =
    -canonicalScalarGraphKreinBoundaryCorrection
      data traceBound spectralParameter poissonData dirichlet robin schurInverse := by
  apply ContinuousLinearMap.ext
  intro source
  apply Subtype.ext
  simp [canonicalScalarGraphKreinRobinResolventData,
    canonicalScalarGraphKreinRobinResolvent,
    canonicalScalarGraphKreinBoundaryCorrection]

/-- Krein/Schur closure certificate. -/
theorem canonicalScalarGraphKreinResolvent_certificate
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (poissonData : CanonicalScalarGraphDirichletPoissonData
      data traceBound spectralParameter)
    (dirichlet : CanonicalScalarGraphDirichletResolventData
      data traceBound spectralParameter)
    (robin : Trace →L[Real] Trace)
    (schurInverse : CanonicalScalarGraphBoundarySchurInverseData
      data traceBound spectralParameter poissonData robin) :
    (∀ source : Ambient,
      canonicalScalarGraphShiftedOperator data spectralParameter
        ((canonicalScalarGraphKreinRobinResolventData
          data traceBound spectralParameter poissonData dirichlet robin schurInverse).resolvent source) =
        source) ∧
      (∀ source : Ambient,
        canonicalScalarCompletedNormalTrace data traceBound
            ((canonicalScalarGraphKreinRobinResolventData
              data traceBound spectralParameter poissonData dirichlet robin schurInverse).resolvent source) =
          robin (canonicalScalarCompletedValueTrace data traceBound
            ((canonicalScalarGraphKreinRobinResolventData
              data traceBound spectralParameter poissonData dirichlet robin schurInverse).resolvent source))) ∧
      (canonicalScalarGraphKreinRobinResolventData
          data traceBound spectralParameter poissonData dirichlet robin schurInverse).resolvent -
        dirichlet.resolvent =
      -canonicalScalarGraphKreinBoundaryCorrection
        data traceBound spectralParameter poissonData dirichlet robin schurInverse :=
  ⟨(canonicalScalarGraphKreinRobinResolventData
      data traceBound spectralParameter poissonData dirichlet robin schurInverse).equation,
    (canonicalScalarGraphKreinRobinResolventData
      data traceBound spectralParameter poissonData dirichlet robin schurInverse).boundary,
    canonicalScalarGraphKrein_resolvent_formula
      data traceBound spectralParameter poissonData dirichlet robin schurInverse⟩

end
end P0EFTJanusMappingTorusScalarGraphKreinResolventFormula4D
end JanusFormal
