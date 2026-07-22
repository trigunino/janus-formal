import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarGraphFiniteBoundaryValueLift4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarGraphDirichletCoerciveResolvent4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarGraphBoundaryTripleFamily4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarGraphBoundarySchurCoerciveInverse4D

/-!
# Automatic finite-dimensional coercive boundary-triple families

When the trace space is finite-dimensional, surjectivity of the paired trace
automatically supplies a continuous value-boundary lift.  If the completed
Dirichlet problem is coercive and surjective at every parameter of a set, each
Dirichlet resolvent is also constructed automatically.

This file combines those facts into a full spectral family of Poisson operators,
Weyl functions and Calderon projectors.  At a parameter where a Robin Schur
operator is coercive and surjective, the Krein Robin resolvent is generated
without any additional inverse datum.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarGraphFiniteCoerciveBoundaryTripleFamily4D

set_option autoImplicit false
noncomputable section

open Set Topology Module
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarOperatorGraphCompletion4D
open P0EFTJanusMappingTorusScalarGraphPoissonDirichletToNeumann4D
open P0EFTJanusMappingTorusScalarGraphPoissonFromDirichletResolvent4D
open P0EFTJanusMappingTorusScalarGraphKreinResolventFormula4D
open P0EFTJanusMappingTorusScalarGraphBoundaryTripleFamily4D
open P0EFTJanusMappingTorusScalarGraphFiniteBoundaryValueLift4D
open P0EFTJanusMappingTorusScalarGraphDirichletCoerciveResolvent4D
open P0EFTJanusMappingTorusScalarGraphBoundarySchurCoerciveInverse4D

universe u v w

variable {Domain : Type u} {Ambient : Type v} {Trace : Type w}
  [AddCommGroup Domain] [Module Real Domain]
  [NormedAddCommGroup Ambient] [InnerProductSpace Real Ambient]
  [CompleteSpace Ambient]
  [NormedAddCommGroup Trace] [InnerProductSpace Real Trace]
  [CompleteSpace Trace]
  [FiniteDimensional Real Trace]

variable
  {data : CanonicalScalarHilbertGreenSystem
    (Domain := Domain) (Ambient := Ambient) (Trace := Trace)}
  {traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data}
  {parameters : Set Real}

/-- Coercive-surjective Dirichlet data at every parameter of a finite-boundary
spectral set. -/
structure CanonicalScalarGraphFiniteCoerciveBoundaryTripleFamilyData
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (parameters : Set Real) where
  dirichletCoercive : ∀ spectralParameter : Real,
    spectralParameter ∈ parameters →
      CanonicalScalarGraphDirichletCoerciveSurjectiveData
        data traceBound spectralParameter

namespace CanonicalScalarGraphFiniteCoerciveBoundaryTripleFamilyData

/-- Automatically generated continuous value lift. -/
noncomputable def valueLift
    (family : CanonicalScalarGraphFiniteCoerciveBoundaryTripleFamilyData
      data traceBound parameters) :
    CanonicalScalarGraphBoundaryValueLiftData data traceBound :=
  canonicalScalarGraphFiniteBoundaryValueLiftData data traceBound

/-- Automatically generated Dirichlet resolvent at one admitted parameter. -/
noncomputable def dirichletResolvent
    (family : CanonicalScalarGraphFiniteCoerciveBoundaryTripleFamilyData
      data traceBound parameters)
    (spectralParameter : Real) (hParameter : spectralParameter ∈ parameters) :
    CanonicalScalarGraphDirichletResolventData
      data traceBound spectralParameter :=
  (family.dirichletCoercive spectralParameter hParameter).toDirichletResolventData

/-- Automatically generated boundary-triple family. -/
noncomputable def toBoundaryTripleFamily
    (family : CanonicalScalarGraphFiniteCoerciveBoundaryTripleFamilyData
      data traceBound parameters) :
    CanonicalScalarGraphBoundaryTripleFamily
      data traceBound parameters where
  valueLift := family.valueLift
  dirichletResolvent := family.dirichletResolvent

/-- Automatically generated Poisson data. -/
noncomputable def poissonData
    (family : CanonicalScalarGraphFiniteCoerciveBoundaryTripleFamilyData
      data traceBound parameters)
    (spectralParameter : Real) (hParameter : spectralParameter ∈ parameters) :
    CanonicalScalarGraphDirichletPoissonData
      data traceBound spectralParameter :=
  (family.toBoundaryTripleFamily).poissonData spectralParameter hParameter

/-- Automatically generated Weyl function. -/
noncomputable def weyl
    (family : CanonicalScalarGraphFiniteCoerciveBoundaryTripleFamilyData
      data traceBound parameters)
    (spectralParameter : Real) (hParameter : spectralParameter ∈ parameters) :
    Trace →L[Real] Trace :=
  (family.toBoundaryTripleFamily).weyl spectralParameter hParameter

/-- Automatically generated Calderon projector. -/
noncomputable def calderon
    (family : CanonicalScalarGraphFiniteCoerciveBoundaryTripleFamilyData
      data traceBound parameters)
    (spectralParameter : Real) (hParameter : spectralParameter ∈ parameters) :
    CanonicalScalarHilbertBoundaryDatum (Trace := Trace) →L[Real]
      CanonicalScalarHilbertBoundaryDatum (Trace := Trace) :=
  (family.toBoundaryTripleFamily).calderon spectralParameter hParameter

/-- Automatically generated Cauchy-data Lagrangian. -/
noncomputable def cauchyData
    (family : CanonicalScalarGraphFiniteCoerciveBoundaryTripleFamilyData
      data traceBound parameters)
    (spectralParameter : Real) (hParameter : spectralParameter ∈ parameters) :
    Submodule Real (CanonicalScalarHilbertBoundaryDatum (Trace := Trace)) :=
  (family.toBoundaryTripleFamily).cauchyData spectralParameter hParameter

/-- The automatically generated Weyl function is symmetric. -/
theorem weyl_isSymmetric
    (family : CanonicalScalarGraphFiniteCoerciveBoundaryTripleFamilyData
      data traceBound parameters)
    (spectralParameter : Real) (hParameter : spectralParameter ∈ parameters) :
    (family.weyl spectralParameter hParameter).toLinearMap.IsSymmetric :=
  (family.toBoundaryTripleFamily).weyl_isSymmetric
    spectralParameter hParameter

/-- The automatically generated Cauchy-data space is closed Lagrangian. -/
theorem cauchyData_closed_lagrangian
    (family : CanonicalScalarGraphFiniteCoerciveBoundaryTripleFamilyData
      data traceBound parameters)
    (spectralParameter : Real) (hParameter : spectralParameter ∈ parameters) :
    IsClosed
        (family.cauchyData spectralParameter hParameter :
          Set (CanonicalScalarHilbertBoundaryDatum (Trace := Trace))) ∧
      canonicalScalarHilbertBoundarySymplecticOrthogonal
          (family.cauchyData spectralParameter hParameter) =
        family.cauchyData spectralParameter hParameter :=
  (family.toBoundaryTripleFamily).cauchyData_closed_lagrangian
    spectralParameter hParameter

/-- Uniform Poisson parameter-change identity. -/
theorem poisson_change_parameter
    (family : CanonicalScalarGraphFiniteCoerciveBoundaryTripleFamilyData
      data traceBound parameters)
    (firstParameter secondParameter : Real)
    (hFirst : firstParameter ∈ parameters)
    (hSecond : secondParameter ∈ parameters)
    (boundary : Trace) :
    (family.poissonData firstParameter hFirst).poisson boundary =
      (family.poissonData secondParameter hSecond).poisson boundary +
        (firstParameter - secondParameter) •
          (family.dirichletResolvent firstParameter hFirst).resolvent
            (canonicalScalarOperatorGraphInclusion data
              ((family.poissonData secondParameter hSecond).poisson boundary)) :=
  (family.toBoundaryTripleFamily).poisson_change_parameter
    firstParameter secondParameter hFirst hSecond boundary

/-- Uniform Weyl identity. -/
theorem weyl_identity
    (family : CanonicalScalarGraphFiniteCoerciveBoundaryTripleFamilyData
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
            ((family.poissonData firstParameter hFirst).poisson firstBoundary))
          (canonicalScalarOperatorGraphInclusion data
            ((family.poissonData secondParameter hSecond).poisson secondBoundary)) :=
  (family.toBoundaryTripleFamily).weyl_identity
    firstParameter secondParameter hFirst hSecond
      firstBoundary secondBoundary

/-- Robin Schur coercivity at one admitted family parameter. -/
structure RobinCoerciveAt
    (family : CanonicalScalarGraphFiniteCoerciveBoundaryTripleFamilyData
      data traceBound parameters)
    (robin : Trace →L[Real] Trace)
    (spectralParameter : Real) (hParameter : spectralParameter ∈ parameters) where
  coercive : CanonicalScalarGraphBoundarySchurCoerciveSurjectiveData
    data traceBound spectralParameter
      (family.poissonData spectralParameter hParameter) robin

/-- Automatically generated Krein Schur inverse. -/
noncomputable def RobinCoerciveAt.toSchurInverse
    (family : CanonicalScalarGraphFiniteCoerciveBoundaryTripleFamilyData
      data traceBound parameters)
    (robin : Trace →L[Real] Trace)
    (spectralParameter : Real) (hParameter : spectralParameter ∈ parameters)
    (robinData : family.RobinCoerciveAt robin spectralParameter hParameter) :
    CanonicalScalarGraphBoundarySchurInverseData
      data traceBound spectralParameter
        (family.poissonData spectralParameter hParameter) robin :=
  robinData.coercive.toKreinInverseData

/-- Automatically generated Robin resolvent. -/
noncomputable def RobinCoerciveAt.robinResolvent
    (family : CanonicalScalarGraphFiniteCoerciveBoundaryTripleFamilyData
      data traceBound parameters)
    (robin : Trace →L[Real] Trace)
    (spectralParameter : Real) (hParameter : spectralParameter ∈ parameters)
    (robinData : family.RobinCoerciveAt robin spectralParameter hParameter) :
    CanonicalScalarGraphRobinResolventData
      data traceBound spectralParameter robin :=
  canonicalScalarGraphKreinRobinResolventData
    data traceBound spectralParameter
      (family.poissonData spectralParameter hParameter)
      (family.dirichletResolvent spectralParameter hParameter)
      robin (robinData.toSchurInverse family robin spectralParameter hParameter)

/-- Krein formula for the automatically generated Robin resolvent. -/
theorem RobinCoerciveAt.krein_formula
    (family : CanonicalScalarGraphFiniteCoerciveBoundaryTripleFamilyData
      data traceBound parameters)
    (robin : Trace →L[Real] Trace)
    (spectralParameter : Real) (hParameter : spectralParameter ∈ parameters)
    (robinData : family.RobinCoerciveAt robin spectralParameter hParameter) :
    (robinData.robinResolvent family robin spectralParameter hParameter).resolvent -
        (family.dirichletResolvent spectralParameter hParameter).resolvent =
      -canonicalScalarGraphKreinBoundaryCorrection
        data traceBound spectralParameter
          (family.poissonData spectralParameter hParameter)
          (family.dirichletResolvent spectralParameter hParameter)
          robin
          (robinData.toSchurInverse family robin spectralParameter hParameter) :=
  canonicalScalarGraphKrein_resolvent_formula
    data traceBound spectralParameter
      (family.poissonData spectralParameter hParameter)
      (family.dirichletResolvent spectralParameter hParameter)
      robin
      (robinData.toSchurInverse family robin spectralParameter hParameter)

/-- Automatic finite coercive boundary-triple certificate. -/
theorem certificate
    (family : CanonicalScalarGraphFiniteCoerciveBoundaryTripleFamilyData
      data traceBound parameters) :
    (∀ spectralParameter : Real,
      ∀ hParameter : spectralParameter ∈ parameters,
        (family.weyl spectralParameter hParameter).toLinearMap.IsSymmetric) ∧
      (∀ spectralParameter : Real,
        ∀ hParameter : spectralParameter ∈ parameters,
          IsClosed
            (family.cauchyData spectralParameter hParameter :
              Set (CanonicalScalarHilbertBoundaryDatum (Trace := Trace))) ∧
          canonicalScalarHilbertBoundarySymplecticOrthogonal
              (family.cauchyData spectralParameter hParameter) =
            family.cauchyData spectralParameter hParameter) := by
  constructor
  · intro spectralParameter hParameter
    exact family.weyl_isSymmetric spectralParameter hParameter
  · intro spectralParameter hParameter
    exact family.cauchyData_closed_lagrangian spectralParameter hParameter

end CanonicalScalarGraphFiniteCoerciveBoundaryTripleFamilyData

end
end P0EFTJanusMappingTorusScalarGraphFiniteCoerciveBoundaryTripleFamily4D
end JanusFormal
