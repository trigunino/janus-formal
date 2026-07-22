import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarGreenIdentityBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarGraphDirichletCoerciveResolvent4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarGraphBoundarySchurCoerciveInverse4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarGraphBoundaryCoerciveAction4D

/-!
# Physical coercive scalar boundary problem

This facade combines the remaining PDE estimates at one real spectral parameter:

* the geometric-to-Hilbert Green bridge;
* graph boundedness of the paired physical Cauchy trace;
* a bounded value-boundary lift;
* coercivity and surjectivity of the completed Dirichlet problem;
* a bounded symmetric Robin operator;
* coercivity and surjectivity of the boundary Schur operator.

From these inputs it constructs the physical Dirichlet resolvent, Poisson
operator, Dirichlet-to-Neumann map, Schur inverse, Robin resolvent and exact Krein
formula.  An optional positive quadratic Schur bound additionally gives the
unique minimizer of every sourced reduced boundary action.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarCoerciveBoundaryProblem4D

set_option autoImplicit false
noncomputable section

open scoped ENNReal
open MeasureTheory Set Topology
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarHilbertGreenSystem4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarGreenIdentityBridge4D
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarOperatorGraphCompletion4D
open P0EFTJanusMappingTorusScalarGraphPoissonDirichletToNeumann4D
open P0EFTJanusMappingTorusScalarGraphKreinResolventFormula4D
open P0EFTJanusMappingTorusScalarGraphPoissonFromDirichletResolvent4D
open P0EFTJanusMappingTorusScalarGraphDirichletCoerciveResolvent4D
open P0EFTJanusMappingTorusScalarGraphBoundaryCoerciveAction4D
open P0EFTJanusMappingTorusScalarGraphBoundarySchurCoerciveInverse4D

variable (period : Real) (hPeriod : period ≠ 0)

local instance canonicalLorentzVolumeFinite :
    IsFiniteMeasure
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

local instance canonicalThroatVolumeFinite :
    IsFiniteMeasure
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod

private abbrev PhysicalTrace := CanonicalPhysicalThroatL2 period hPeriod
private abbrev PhysicalBulk := CanonicalPhysicalBulkL2 period hPeriod

/-- Physical data through the Dirichlet Poisson/DtN construction. -/
structure CanonicalPhysicalScalarDirichletCoerciveData where
  greenBridge : CanonicalPhysicalScalarGreenIdentityBridgeData period hPeriod
  graphBound : CanonicalPhysicalPairedBoundaryGraphBound period hPeriod
    (greenBridge.toSmoothGreenData period hPeriod)
  spectralParameter : Real
  valueLift : CanonicalScalarGraphBoundaryValueLiftData
    (greenBridge.toHilbertGreenSystem period hPeriod)
    (graphBound.toAbstract period hPeriod
      (greenBridge.toSmoothGreenData period hPeriod))
  dirichletCoercive : CanonicalScalarGraphDirichletCoerciveSurjectiveData
    (greenBridge.toHilbertGreenSystem period hPeriod)
    (graphBound.toAbstract period hPeriod
      (greenBridge.toSmoothGreenData period hPeriod))
    spectralParameter

namespace CanonicalPhysicalScalarDirichletCoerciveData

/-- Physical Hilbert Green system. -/
def system
    (physical : CanonicalPhysicalScalarDirichletCoerciveData period hPeriod) :=
  physical.greenBridge.toHilbertGreenSystem period hPeriod

/-- Physical abstract graph trace bound. -/
def abstractGraphBound
    (physical : CanonicalPhysicalScalarDirichletCoerciveData period hPeriod) :=
  physical.graphBound.toAbstract period hPeriod
    (physical.greenBridge.toSmoothGreenData period hPeriod)

/-- Automatically constructed physical Dirichlet resolvent. -/
noncomputable def dirichletResolvent
    (physical : CanonicalPhysicalScalarDirichletCoerciveData period hPeriod) :
    CanonicalScalarGraphDirichletResolventData
      physical.system physical.abstractGraphBound
        physical.spectralParameter :=
  physical.dirichletCoercive.toDirichletResolventData

/-- Automatically constructed physical Poisson data. -/
noncomputable def poissonData
    (physical : CanonicalPhysicalScalarDirichletCoerciveData period hPeriod) :
    CanonicalScalarGraphDirichletPoissonData
      physical.system physical.abstractGraphBound
        physical.spectralParameter :=
  canonicalScalarGraphDirichletPoissonDataOfBoundaryLift
    physical.system physical.abstractGraphBound physical.spectralParameter
      physical.valueLift physical.dirichletResolvent

/-- Physical Poisson operator. -/
noncomputable def poisson
    (physical : CanonicalPhysicalScalarDirichletCoerciveData period hPeriod) :
    PhysicalTrace period hPeriod →L[Real]
      CanonicalScalarOperatorGraphSpace physical.system :=
  physical.poissonData.poisson

/-- Physical Dirichlet-to-Neumann map. -/
noncomputable def dirichletToNeumann
    (physical : CanonicalPhysicalScalarDirichletCoerciveData period hPeriod) :
    PhysicalTrace period hPeriod →L[Real] PhysicalTrace period hPeriod :=
  canonicalScalarGraphDirichletToNeumann
    physical.system physical.abstractGraphBound physical.spectralParameter
      physical.poissonData

/-- Physical DtN is symmetric. -/
theorem dirichletToNeumann_isSymmetric
    (physical : CanonicalPhysicalScalarDirichletCoerciveData period hPeriod) :
    physical.dirichletToNeumann.toLinearMap.IsSymmetric :=
  canonicalScalarGraphDirichletToNeumann_isSymmetric
    physical.system physical.abstractGraphBound physical.spectralParameter
      physical.poissonData

/-- Physical Cauchy-data space. -/
def cauchyData
    (physical : CanonicalPhysicalScalarDirichletCoerciveData period hPeriod) :
    Submodule Real
      (CanonicalScalarHilbertBoundaryDatum
        (Trace := PhysicalTrace period hPeriod)) :=
  canonicalScalarGraphCauchyDataSubmodule
    physical.system physical.abstractGraphBound physical.spectralParameter
      physical.poissonData

/-- Physical Cauchy data are closed Lagrangian. -/
theorem cauchyData_closed_lagrangian
    (physical : CanonicalPhysicalScalarDirichletCoerciveData period hPeriod) :
    IsClosed
        (physical.cauchyData : Set
          (CanonicalScalarHilbertBoundaryDatum
            (Trace := PhysicalTrace period hPeriod))) ∧
      canonicalScalarHilbertBoundarySymplecticOrthogonal physical.cauchyData =
        physical.cauchyData :=
  canonicalScalarGraphCauchyDataSubmodule_closed_lagrangian
    physical.system physical.abstractGraphBound physical.spectralParameter
      physical.poissonData

/-- Dirichlet construction certificate. -/
theorem certificate
    (physical : CanonicalPhysicalScalarDirichletCoerciveData period hPeriod) :
    (∀ boundary : PhysicalTrace period hPeriod,
          canonicalScalarCompletedValueTrace
          physical.system physical.abstractGraphBound
          (physical.poisson period hPeriod boundary) = boundary) ∧
      (∀ boundary : PhysicalTrace period hPeriod,
        canonicalScalarGraphShiftedOperator
          physical.system physical.spectralParameter
          (physical.poisson period hPeriod boundary) = 0) ∧
      physical.dirichletToNeumann.toLinearMap.IsSymmetric :=
  ⟨physical.poissonData.value_trace,
    physical.poissonData.homogeneous,
    physical.dirichletToNeumann_isSymmetric⟩

end CanonicalPhysicalScalarDirichletCoerciveData

/-- Physical Robin problem at the same spectral parameter. -/
structure CanonicalPhysicalScalarRobinCoerciveData
    (dirichlet : CanonicalPhysicalScalarDirichletCoerciveData period hPeriod) where
  robin : PhysicalTrace period hPeriod →L[Real] PhysicalTrace period hPeriod
  robin_symmetric : robin.toLinearMap.IsSymmetric
  schurCoercive : CanonicalScalarGraphBoundarySchurCoerciveSurjectiveData
    dirichlet.system dirichlet.abstractGraphBound dirichlet.spectralParameter
      dirichlet.poissonData robin

namespace CanonicalPhysicalScalarRobinCoerciveData

/-- Physical boundary Schur operator. -/
def schur
    {dirichlet : CanonicalPhysicalScalarDirichletCoerciveData period hPeriod}
    (robinData : CanonicalPhysicalScalarRobinCoerciveData
      period hPeriod dirichlet) :
    PhysicalTrace period hPeriod →L[Real] PhysicalTrace period hPeriod :=
  canonicalScalarGraphBoundarySchurOperator
    dirichlet.system dirichlet.abstractGraphBound dirichlet.spectralParameter
      dirichlet.poissonData robinData.robin

/-- Physical bounded Schur inverse. -/
noncomputable def schurInverse
    {dirichlet : CanonicalPhysicalScalarDirichletCoerciveData period hPeriod}
    (robinData : CanonicalPhysicalScalarRobinCoerciveData
      period hPeriod dirichlet) :
    PhysicalTrace period hPeriod →L[Real] PhysicalTrace period hPeriod :=
  robinData.schurCoercive.inverse

/-- Physical Krein inverse package. -/
noncomputable def kreinInverseData
    {dirichlet : CanonicalPhysicalScalarDirichletCoerciveData period hPeriod}
    (robinData : CanonicalPhysicalScalarRobinCoerciveData
      period hPeriod dirichlet) :
    CanonicalScalarGraphBoundarySchurInverseData
      dirichlet.system dirichlet.abstractGraphBound dirichlet.spectralParameter
        dirichlet.poissonData robinData.robin :=
  robinData.schurCoercive.toKreinInverseData

/-- Physical Robin graph resolvent. -/
noncomputable def robinResolvent
    {dirichlet : CanonicalPhysicalScalarDirichletCoerciveData period hPeriod}
    (robinData : CanonicalPhysicalScalarRobinCoerciveData
      period hPeriod dirichlet) :
    CanonicalScalarGraphRobinResolventData
      dirichlet.system dirichlet.abstractGraphBound dirichlet.spectralParameter
        robinData.robin :=
  canonicalScalarGraphKreinRobinResolventData
    dirichlet.system dirichlet.abstractGraphBound dirichlet.spectralParameter
      dirichlet.poissonData dirichlet.dirichletResolvent robinData.robin
      robinData.kreinInverseData

/-- Physical Krein resolvent formula. -/
theorem krein_formula
    {dirichlet : CanonicalPhysicalScalarDirichletCoerciveData period hPeriod}
    (robinData : CanonicalPhysicalScalarRobinCoerciveData
      period hPeriod dirichlet) :
    robinData.robinResolvent.resolvent -
        dirichlet.dirichletResolvent.resolvent =
      -canonicalScalarGraphKreinBoundaryCorrection
        dirichlet.system dirichlet.abstractGraphBound
          dirichlet.spectralParameter dirichlet.poissonData
          dirichlet.dirichletResolvent robinData.robin
          robinData.kreinInverseData :=
  canonicalScalarGraphKrein_resolvent_formula
    dirichlet.system dirichlet.abstractGraphBound dirichlet.spectralParameter
      dirichlet.poissonData dirichlet.dirichletResolvent robinData.robin
      robinData.kreinInverseData

/-- Physical Robin closure certificate. -/
theorem certificate
    {dirichlet : CanonicalPhysicalScalarDirichletCoerciveData period hPeriod}
    (robinData : CanonicalPhysicalScalarRobinCoerciveData
      period hPeriod dirichlet) :
    Function.Bijective robinData.schur ∧
      (∀ source : PhysicalTrace period hPeriod,
        robinData.schur period hPeriod
          (robinData.schurInverse period hPeriod source) = source) ∧
      robinData.robinResolvent.resolvent -
          dirichlet.dirichletResolvent.resolvent =
        -canonicalScalarGraphKreinBoundaryCorrection
          dirichlet.system dirichlet.abstractGraphBound
            dirichlet.spectralParameter dirichlet.poissonData
            dirichlet.dirichletResolvent robinData.robin
            robinData.kreinInverseData :=
  ⟨robinData.schurCoercive.bijective,
    robinData.schurCoercive.schur_inverse,
    robinData.krein_formula⟩

end CanonicalPhysicalScalarRobinCoerciveData

/-- Optional positive quadratic Schur bound, needed for minimization of sourced
reduced boundary actions. -/
structure CanonicalPhysicalScalarRobinPositiveActionData
    {dirichlet : CanonicalPhysicalScalarDirichletCoerciveData period hPeriod}
    (robinData : CanonicalPhysicalScalarRobinCoerciveData
      period hPeriod dirichlet) where
  quadraticCoercive : CanonicalScalarGraphBoundarySchurCoerciveData
    dirichlet.system dirichlet.abstractGraphBound dirichlet.spectralParameter
      dirichlet.poissonData robinData.robin

/-- The Schur inverse is the unique global minimizer of the sourced physical
reduced action under the positive quadratic bound. -/
theorem canonicalPhysicalScalarRobinReducedAction_minimizer
    {dirichlet : CanonicalPhysicalScalarDirichletCoerciveData period hPeriod}
    (robinData : CanonicalPhysicalScalarRobinCoerciveData
      period hPeriod dirichlet)
    (positive : CanonicalPhysicalScalarRobinPositiveActionData
      period hPeriod robinData)
    (source : PhysicalTrace period hPeriod) :
    let solution := robinData.schurInverse period hPeriod source
    CanonicalScalarGraphBoundarySourceStationary
        dirichlet.system dirichlet.abstractGraphBound
          dirichlet.spectralParameter dirichlet.poissonData robinData.robin
          source solution ∧
      (∀ boundary : PhysicalTrace period hPeriod,
        canonicalScalarGraphBoundarySourceAction
            dirichlet.system dirichlet.abstractGraphBound
              dirichlet.spectralParameter dirichlet.poissonData robinData.robin
              source solution ≤
          canonicalScalarGraphBoundarySourceAction
            dirichlet.system dirichlet.abstractGraphBound
              dirichlet.spectralParameter dirichlet.poissonData robinData.robin
              source boundary) ∧
      (∀ boundary : PhysicalTrace period hPeriod,
        canonicalScalarGraphBoundarySourceAction
            dirichlet.system dirichlet.abstractGraphBound
              dirichlet.spectralParameter dirichlet.poissonData robinData.robin
              source boundary =
          canonicalScalarGraphBoundarySourceAction
            dirichlet.system dirichlet.abstractGraphBound
              dirichlet.spectralParameter dirichlet.poissonData robinData.robin
              source solution →
        boundary = solution) :=
  canonicalScalarGraphBoundaryCoerciveAction_certificate
    dirichlet.system dirichlet.abstractGraphBound dirichlet.spectralParameter
      dirichlet.poissonData robinData.robin positive.quadraticCoercive
      robinData.schurCoercive.toBoundedInverseData source

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarCoerciveBoundaryProblem4D
end JanusFormal
