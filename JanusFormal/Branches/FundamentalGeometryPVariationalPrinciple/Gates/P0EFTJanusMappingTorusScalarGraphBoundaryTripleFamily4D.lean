import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarGraphPoissonFromDirichletResolvent4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarGraphWeylFunctionIdentity4D

/-!
# Spectral families of scalar graph boundary triples

The previous leaves construct Poisson, Dirichlet-to-Neumann, Calderon and Krein
objects at one spectral parameter.  This file packages a whole real parameter
set.

A family contains a fixed continuous value-boundary lift and, at every admitted
parameter, a bounded Dirichlet resolvent.  The Poisson operator and Weyl function
are then constructed canonically.  Their parameter-change and Weyl identities
hold uniformly.  Supplying a Robin Schur inverse at one parameter constructs the
corresponding Robin resolvent by the Krein formula.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarGraphBoundaryTripleFamily4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarOperatorGraphCompletion4D
open P0EFTJanusMappingTorusScalarGraphPoissonDirichletToNeumann4D
open P0EFTJanusMappingTorusScalarGraphKreinResolventFormula4D
open P0EFTJanusMappingTorusScalarGraphCalderonProjector4D
open P0EFTJanusMappingTorusScalarGraphWeylFunctionIdentity4D
open P0EFTJanusMappingTorusScalarGraphPoissonFromDirichletResolvent4D

universe u v w

variable {Domain : Type u} {Ambient : Type v} {Trace : Type w}
  [AddCommGroup Domain] [Module Real Domain]
  [NormedAddCommGroup Ambient] [InnerProductSpace Real Ambient]
  [CompleteSpace Ambient]
  [NormedAddCommGroup Trace] [InnerProductSpace Real Trace]
  [CompleteSpace Trace]

/-- A real spectral family of Dirichlet boundary triples on one completed graph. -/
structure CanonicalScalarGraphBoundaryTripleFamily
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (parameters : Set Real) where
  valueLift : CanonicalScalarGraphBoundaryValueLiftData data traceBound
  dirichletResolvent : ∀ spectralParameter : Real,
    spectralParameter ∈ parameters →
      CanonicalScalarGraphDirichletResolventData
        data traceBound spectralParameter

namespace CanonicalScalarGraphBoundaryTripleFamily

/-- Canonical Poisson data at a parameter of the family. -/
noncomputable def poissonData
    (family : CanonicalScalarGraphBoundaryTripleFamily
      data traceBound parameters)
    (spectralParameter : Real) (hParameter : spectralParameter ∈ parameters) :
    CanonicalScalarGraphDirichletPoissonData
      data traceBound spectralParameter :=
  canonicalScalarGraphDirichletPoissonDataOfBoundaryLift
    data traceBound spectralParameter family.valueLift
      (family.dirichletResolvent spectralParameter hParameter)

/-- Poisson operator at a parameter of the family. -/
noncomputable def poisson
    (family : CanonicalScalarGraphBoundaryTripleFamily
      data traceBound parameters)
    (spectralParameter : Real) (hParameter : spectralParameter ∈ parameters) :
    Trace →L[Real] CanonicalScalarOperatorGraphSpace data :=
  (family.poissonData spectralParameter hParameter).poisson

/-- Weyl/Dirichlet-to-Neumann operator at a parameter of the family. -/
noncomputable def weyl
    (family : CanonicalScalarGraphBoundaryTripleFamily
      data traceBound parameters)
    (spectralParameter : Real) (hParameter : spectralParameter ∈ parameters) :
    Trace →L[Real] Trace :=
  canonicalScalarGraphDirichletToNeumann
    data traceBound spectralParameter
      (family.poissonData spectralParameter hParameter)

/-- Calderon projector at a parameter of the family. -/
noncomputable def calderon
    (family : CanonicalScalarGraphBoundaryTripleFamily
      data traceBound parameters)
    (spectralParameter : Real) (hParameter : spectralParameter ∈ parameters) :
    CanonicalScalarHilbertBoundaryDatum (Trace := Trace) →L[Real]
      CanonicalScalarHilbertBoundaryDatum (Trace := Trace) :=
  canonicalScalarGraphCalderonProjector
    data traceBound spectralParameter
      (family.poissonData spectralParameter hParameter)

/-- Cauchy-data Lagrangian at a parameter of the family. -/
noncomputable def cauchyData
    (family : CanonicalScalarGraphBoundaryTripleFamily
      data traceBound parameters)
    (spectralParameter : Real) (hParameter : spectralParameter ∈ parameters) :
    Submodule Real (CanonicalScalarHilbertBoundaryDatum (Trace := Trace)) :=
  canonicalScalarGraphCauchyDataSubmodule
    data traceBound spectralParameter
      (family.poissonData spectralParameter hParameter)

/-- Boundary Schur operator for a fixed bounded Robin operator. -/
noncomputable def schur
    (family : CanonicalScalarGraphBoundaryTripleFamily
      data traceBound parameters)
    (robin : Trace →L[Real] Trace)
    (spectralParameter : Real) (hParameter : spectralParameter ∈ parameters) :
    Trace →L[Real] Trace :=
  family.weyl spectralParameter hParameter - robin

@[simp] theorem poisson_value_trace
    (family : CanonicalScalarGraphBoundaryTripleFamily
      data traceBound parameters)
    (spectralParameter : Real) (hParameter : spectralParameter ∈ parameters)
    (boundary : Trace) :
    canonicalScalarCompletedValueTrace data traceBound
        (family.poisson spectralParameter hParameter boundary) = boundary :=
  (family.poissonData spectralParameter hParameter).value_trace boundary

@[simp] theorem poisson_homogeneous
    (family : CanonicalScalarGraphBoundaryTripleFamily
      data traceBound parameters)
    (spectralParameter : Real) (hParameter : spectralParameter ∈ parameters)
    (boundary : Trace) :
    canonicalScalarGraphShiftedOperator data spectralParameter
        (family.poisson spectralParameter hParameter boundary) = 0 :=
  (family.poissonData spectralParameter hParameter).homogeneous boundary

/-- Every family Weyl operator is symmetric. -/
theorem weyl_isSymmetric
    (family : CanonicalScalarGraphBoundaryTripleFamily
      data traceBound parameters)
    (spectralParameter : Real) (hParameter : spectralParameter ∈ parameters) :
    (family.weyl spectralParameter hParameter).toLinearMap.IsSymmetric :=
  canonicalScalarGraphDirichletToNeumann_isSymmetric
    data traceBound spectralParameter
      (family.poissonData spectralParameter hParameter)

/-- Every family Cauchy-data space is closed and Lagrangian. -/
theorem cauchyData_closed_lagrangian
    (family : CanonicalScalarGraphBoundaryTripleFamily
      data traceBound parameters)
    (spectralParameter : Real) (hParameter : spectralParameter ∈ parameters) :
    IsClosed
        (family.cauchyData spectralParameter hParameter :
          Set (CanonicalScalarHilbertBoundaryDatum (Trace := Trace))) ∧
      canonicalScalarHilbertBoundarySymplecticOrthogonal
          (family.cauchyData spectralParameter hParameter) =
        family.cauchyData spectralParameter hParameter :=
  canonicalScalarGraphCauchyDataSubmodule_closed_lagrangian
    data traceBound spectralParameter
      (family.poissonData spectralParameter hParameter)

/-- Poisson parameter-change identity for a family. -/
theorem poisson_change_parameter
    (family : CanonicalScalarGraphBoundaryTripleFamily
      data traceBound parameters)
    (firstParameter secondParameter : Real)
    (hFirst : firstParameter ∈ parameters)
    (hSecond : secondParameter ∈ parameters)
    (boundary : Trace) :
    family.poisson firstParameter hFirst boundary =
      family.poisson secondParameter hSecond boundary +
        (firstParameter - secondParameter) •
          (family.dirichletResolvent firstParameter hFirst).resolvent
            (canonicalScalarOperatorGraphInclusion data
              (family.poisson secondParameter hSecond boundary)) :=
  canonicalScalarGraphPoisson_change_parameter
    data traceBound firstParameter secondParameter
      (family.poissonData firstParameter hFirst)
      (family.poissonData secondParameter hSecond)
      (family.dirichletResolvent firstParameter hFirst) boundary

/-- Weyl identity for every pair of parameters in the family. -/
theorem weyl_identity
    (family : CanonicalScalarGraphBoundaryTripleFamily
      data traceBound parameters)
    (firstParameter secondParameter : Real)
    (hFirst : firstParameter ∈ parameters)
    (hSecond : secondParameter ∈ parameters)
    (firstBoundary secondBoundary : Trace) :
    2 * (inner Real firstBoundary
          (family.weyl secondParameter hSecond secondBoundary) -
        inner Real
          (family.weyl firstParameter hFirst firstBoundary)
          secondBoundary) =
      (firstParameter - secondParameter) *
        inner Real
          (canonicalScalarOperatorGraphInclusion data
            (family.poisson firstParameter hFirst firstBoundary))
          (canonicalScalarOperatorGraphInclusion data
            (family.poisson secondParameter hSecond secondBoundary)) :=
  canonicalScalarGraphDirichletToNeumann_weyl_identity
    data traceBound firstParameter secondParameter
      (family.poissonData firstParameter hFirst)
      (family.poissonData secondParameter hSecond)
      firstBoundary secondBoundary

/-- Schur-inverse data at one family parameter. -/
structure RobinSchurInverseAt
    (family : CanonicalScalarGraphBoundaryTripleFamily
      data traceBound parameters)
    (robin : Trace →L[Real] Trace)
    (spectralParameter : Real) (hParameter : spectralParameter ∈ parameters) where
  inverseData : CanonicalScalarGraphBoundarySchurInverseData
    data traceBound spectralParameter
      (family.poissonData spectralParameter hParameter) robin

/-- Robin resolvent constructed at one parameter from the Schur inverse. -/
noncomputable def robinResolvent
    (family : CanonicalScalarGraphBoundaryTripleFamily
      data traceBound parameters)
    (robin : Trace →L[Real] Trace)
    (spectralParameter : Real) (hParameter : spectralParameter ∈ parameters)
    (inverse : family.RobinSchurInverseAt robin spectralParameter hParameter) :
    CanonicalScalarGraphRobinResolventData
      data traceBound spectralParameter robin :=
  canonicalScalarGraphKreinRobinResolventData
    data traceBound spectralParameter
      (family.poissonData spectralParameter hParameter)
      (family.dirichletResolvent spectralParameter hParameter)
      robin inverse.inverseData

/-- Family form of the Krein resolvent formula. -/
theorem robinResolvent_sub_dirichlet
    (family : CanonicalScalarGraphBoundaryTripleFamily
      data traceBound parameters)
    (robin : Trace →L[Real] Trace)
    (spectralParameter : Real) (hParameter : spectralParameter ∈ parameters)
    (inverse : family.RobinSchurInverseAt robin spectralParameter hParameter) :
    (family.robinResolvent robin spectralParameter hParameter inverse).resolvent -
        (family.dirichletResolvent spectralParameter hParameter).resolvent =
      -canonicalScalarGraphKreinBoundaryCorrection
        data traceBound spectralParameter
          (family.poissonData spectralParameter hParameter)
          (family.dirichletResolvent spectralParameter hParameter)
          robin inverse.inverseData :=
  canonicalScalarGraphKrein_resolvent_formula
    data traceBound spectralParameter
      (family.poissonData spectralParameter hParameter)
      (family.dirichletResolvent spectralParameter hParameter)
      robin inverse.inverseData

/-- Boundary-triple family certificate. -/
theorem certificate
    (family : CanonicalScalarGraphBoundaryTripleFamily
      data traceBound parameters) :
    (∀ spectralParameter : Real, spectralParameter ∈ parameters →
      (family.weyl spectralParameter ‹spectralParameter ∈ parameters›).toLinearMap.IsSymmetric) ∧
      (∀ firstParameter secondParameter : Real,
        ∀ hFirst : firstParameter ∈ parameters,
        ∀ hSecond : secondParameter ∈ parameters,
        ∀ firstBoundary secondBoundary : Trace,
          2 * (inner Real firstBoundary
                (family.weyl secondParameter hSecond secondBoundary) -
              inner Real
                (family.weyl firstParameter hFirst firstBoundary)
                secondBoundary) =
            (firstParameter - secondParameter) *
              inner Real
                (canonicalScalarOperatorGraphInclusion data
                  (family.poisson firstParameter hFirst firstBoundary))
                (canonicalScalarOperatorGraphInclusion data
                  (family.poisson secondParameter hSecond secondBoundary))) := by
  constructor
  · intro spectralParameter hParameter
    exact family.weyl_isSymmetric spectralParameter hParameter
  · intro firstParameter secondParameter hFirst hSecond firstBoundary secondBoundary
    exact family.weyl_identity firstParameter secondParameter hFirst hSecond
      firstBoundary secondBoundary

end CanonicalScalarGraphBoundaryTripleFamily

end
end P0EFTJanusMappingTorusScalarGraphBoundaryTripleFamily4D
end JanusFormal
