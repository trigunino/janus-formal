import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarGraphKreinResolventFormula4D

/-!
# Relative Krein formula for two scalar Robin realizations

At one spectral parameter, two Robin resolvents are both compared with the same
Dirichlet resolvent.  Subtracting the two Krein formulas gives an exact relative
resolvent identity: the bulk difference is the difference of their boundary
Krein corrections.

Compactness or finite-rank information can therefore be proved entirely on the
boundary corrections and transferred to the bulk resolvent difference.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarGraphRobinResolventComparison4D

set_option autoImplicit false
noncomputable section

open Set Topology Module
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarOperatorGraphCompletion4D
open P0EFTJanusMappingTorusScalarGraphPoissonDirichletToNeumann4D
open P0EFTJanusMappingTorusScalarGraphKreinResolventFormula4D

universe u v w

variable {Domain : Type u} {Ambient : Type v} {Trace : Type w}
  [AddCommGroup Domain] [Module Real Domain]
  [NormedAddCommGroup Ambient] [InnerProductSpace Real Ambient]
  [CompleteSpace Ambient]
  [NormedAddCommGroup Trace] [InnerProductSpace Real Trace]
  [CompleteSpace Trace]

/-- Complete Robin realization built from one Schur inverse. -/
structure CanonicalScalarGraphKreinRobinRealization
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (poissonData : CanonicalScalarGraphDirichletPoissonData
      data traceBound spectralParameter)
    (dirichletResolvent : CanonicalScalarGraphDirichletResolventData
      data traceBound spectralParameter) where
  robin : Trace →L[Real] Trace
  inverseData : CanonicalScalarGraphBoundarySchurInverseData
    data traceBound spectralParameter poissonData robin

namespace CanonicalScalarGraphKreinRobinRealization

/-- Robin graph resolvent. -/
noncomputable def resolventData
    (realization : CanonicalScalarGraphKreinRobinRealization
      data traceBound spectralParameter poissonData dirichletResolvent) :
    CanonicalScalarGraphRobinResolventData
      data traceBound spectralParameter realization.robin :=
  canonicalScalarGraphKreinRobinResolventData
    data traceBound spectralParameter poissonData dirichletResolvent
      realization.robin realization.inverseData

/-- Boundary Krein correction. -/
noncomputable def correction
    (realization : CanonicalScalarGraphKreinRobinRealization
      data traceBound spectralParameter poissonData dirichletResolvent) :=
  canonicalScalarGraphKreinBoundaryCorrection
    data traceBound spectralParameter poissonData dirichletResolvent
      realization.robin realization.inverseData

/-- Krein comparison with the common Dirichlet resolvent. -/
theorem resolvent_sub_dirichlet
    (realization : CanonicalScalarGraphKreinRobinRealization
      data traceBound spectralParameter poissonData dirichletResolvent) :
    realization.resolventData.resolvent - dirichletResolvent.resolvent =
      -realization.correction :=
  canonicalScalarGraphKrein_resolvent_formula
    data traceBound spectralParameter poissonData dirichletResolvent
      realization.robin realization.inverseData

/-- Relative Krein formula for two Robin realizations. -/
theorem resolvent_sub_resolvent
    (first second : CanonicalScalarGraphKreinRobinRealization
      data traceBound spectralParameter poissonData dirichletResolvent) :
    first.resolventData.resolvent - second.resolventData.resolvent =
      second.correction - first.correction := by
  have hFirst := first.resolvent_sub_dirichlet
  have hSecond := second.resolvent_sub_dirichlet
  module at hFirst hSecond ⊢

/-- Equality of boundary corrections implies equality of the Robin resolvents. -/
theorem resolvent_eq_of_correction_eq
    (first second : CanonicalScalarGraphKreinRobinRealization
      data traceBound spectralParameter poissonData dirichletResolvent)
    (hCorrection : first.correction = second.correction) :
    first.resolventData.resolvent = second.resolventData.resolvent := by
  have hDifference := first.resolvent_sub_resolvent second
  rw [hCorrection, sub_self] at hDifference
  exact sub_eq_zero.mp hDifference

/-- Compactness data for one Krein correction. -/
structure CompactCorrection
    (realization : CanonicalScalarGraphKreinRobinRealization
      data traceBound spectralParameter poissonData dirichletResolvent) where
  compact : IsCompactOperator realization.correction

/-- Compact Robin corrections give a compact relative resolvent difference. -/
theorem resolvent_sub_resolvent_compact
    (first second : CanonicalScalarGraphKreinRobinRealization
      data traceBound spectralParameter poissonData dirichletResolvent)
    (hFirst : first.CompactCorrection)
    (hSecond : second.CompactCorrection) :
    IsCompactOperator
      (first.resolventData.resolvent - second.resolventData.resolvent) := by
  rw [first.resolvent_sub_resolvent second]
  exact hSecond.compact.sub hFirst.compact

/-- Finite-dimensional range data for a boundary correction. -/
structure FiniteRangeCorrection
    (realization : CanonicalScalarGraphKreinRobinRealization
      data traceBound spectralParameter poissonData dirichletResolvent) where
  rangeFinite : FiniteDimensional Real
    (LinearMap.range realization.correction.toLinearMap)

/-- Relative resolvent formula certificate. -/
theorem canonicalScalarGraphRobinResolventComparison_certificate
    (first second : CanonicalScalarGraphKreinRobinRealization
      data traceBound spectralParameter poissonData dirichletResolvent) :
    first.resolventData.resolvent - second.resolventData.resolvent =
        second.correction - first.correction ∧
      (first.correction = second.correction →
        first.resolventData.resolvent = second.resolventData.resolvent) :=
  ⟨first.resolvent_sub_resolvent second,
    first.resolvent_eq_of_correction_eq second⟩

end CanonicalScalarGraphKreinRobinRealization

end
end P0EFTJanusMappingTorusScalarGraphRobinResolventComparison4D
end JanusFormal
