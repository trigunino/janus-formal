import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarAnalyticClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarGraphBoundaryReducedAction4D

/-!
# Physical Janus Poisson/Dirichlet-to-Neumann boundary reduction

This file specializes the completed-graph Poisson, Dirichlet-to-Neumann,
Calderon and reduced-boundary-action constructions to the canonical physical
bulk and throat L2 spaces.

The resulting facade isolates one remaining PDE input at a chosen real
spectral parameter: the continuous physical Poisson solution operator with its
uniqueness theorem.  Once supplied, every boundary reduction below is a
concrete theorem on the actual Janus Hilbert spaces.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarBoundaryReduction4D

set_option autoImplicit false
noncomputable section

open scoped ENNReal
open MeasureTheory Set Topology
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarHilbertGreenSystem4D
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarOperatorGraphCompletion4D
open P0EFTJanusMappingTorusScalarGraphPoissonDirichletToNeumann4D
open P0EFTJanusMappingTorusScalarGraphCalderonProjector4D
open P0EFTJanusMappingTorusScalarGraphBoundarySpectrumReduction4D
open P0EFTJanusMappingTorusScalarGraphBoundaryReducedAction4D

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

/-- Physical Poisson input at one spectral parameter. -/
structure CanonicalPhysicalScalarBoundaryReductionData where
  smoothGreen : CanonicalPhysicalSmoothScalarGreenData period hPeriod
  graphBound : CanonicalPhysicalPairedBoundaryGraphBound
    period hPeriod smoothGreen
  spectralParameter : Real
  poisson : CanonicalScalarGraphDirichletPoissonData
    (canonicalPhysicalScalarHilbertGreenSystem period hPeriod smoothGreen)
    (graphBound.toAbstract period hPeriod smoothGreen)
    spectralParameter

namespace CanonicalPhysicalScalarBoundaryReductionData

/-- Underlying physical Hilbert Green system. -/
def system
    (reduction : CanonicalPhysicalScalarBoundaryReductionData period hPeriod) :=
  canonicalPhysicalScalarHilbertGreenSystem
    period hPeriod reduction.smoothGreen

/-- Underlying abstract graph trace bound. -/
def abstractGraphBound
    (reduction : CanonicalPhysicalScalarBoundaryReductionData period hPeriod) :=
  reduction.graphBound.toAbstract period hPeriod reduction.smoothGreen

/-- Physical Dirichlet-to-Neumann operator. -/
def dirichletToNeumann
    (reduction : CanonicalPhysicalScalarBoundaryReductionData period hPeriod) :
    PhysicalTrace period hPeriod →L[Real] PhysicalTrace period hPeriod :=
  canonicalScalarGraphDirichletToNeumann
    reduction.system reduction.abstractGraphBound
      reduction.spectralParameter reduction.poisson

/-- Physical Calderon projector. -/
def calderonProjector
    (reduction : CanonicalPhysicalScalarBoundaryReductionData period hPeriod) :
    CanonicalScalarHilbertBoundaryDatum (Trace := PhysicalTrace period hPeriod) →L[Real]
      CanonicalScalarHilbertBoundaryDatum (Trace := PhysicalTrace period hPeriod) :=
  canonicalScalarGraphCalderonProjector
    reduction.system reduction.abstractGraphBound
      reduction.spectralParameter reduction.poisson

/-- Physical Cauchy-data subspace. -/
def cauchyDataSubmodule
    (reduction : CanonicalPhysicalScalarBoundaryReductionData period hPeriod) :
    Submodule Real
      (CanonicalScalarHilbertBoundaryDatum
        (Trace := PhysicalTrace period hPeriod)) :=
  canonicalScalarGraphCauchyDataSubmodule
    reduction.system reduction.abstractGraphBound
      reduction.spectralParameter reduction.poisson

/-- Physical boundary Schur operator against a supplied bounded Robin operator. -/
def boundarySchurOperator
    (reduction : CanonicalPhysicalScalarBoundaryReductionData period hPeriod)
    (robin : PhysicalTrace period hPeriod →L[Real]
      PhysicalTrace period hPeriod) :
    PhysicalTrace period hPeriod →L[Real] PhysicalTrace period hPeriod :=
  canonicalScalarGraphBoundarySchurOperator
    reduction.system reduction.abstractGraphBound
      reduction.spectralParameter reduction.poisson robin

/-- Physical reduced boundary action. -/
def robinReducedAction
    (reduction : CanonicalPhysicalScalarBoundaryReductionData period hPeriod)
    (robin : PhysicalTrace period hPeriod →L[Real]
      PhysicalTrace period hPeriod)
    (boundary : PhysicalTrace period hPeriod) : Real :=
  canonicalScalarGraphRobinReducedAction
    reduction.system reduction.abstractGraphBound
      reduction.spectralParameter reduction.poisson robin boundary

/-- Physical Robin homogeneous graph-solution space. -/
def robinHomogeneousSolutionSubmodule
    (reduction : CanonicalPhysicalScalarBoundaryReductionData period hPeriod)
    (robin : PhysicalTrace period hPeriod →L[Real]
      PhysicalTrace period hPeriod) :=
  canonicalScalarGraphRobinHomogeneousSolutionSubmodule
    reduction.system reduction.abstractGraphBound
      reduction.spectralParameter robin

/-- Physical DtN is symmetric. -/
theorem dirichletToNeumann_isSymmetric
    (reduction : CanonicalPhysicalScalarBoundaryReductionData period hPeriod) :
    reduction.dirichletToNeumann period hPeriod |>.toLinearMap.IsSymmetric :=
  canonicalScalarGraphDirichletToNeumann_isSymmetric
    reduction.system reduction.abstractGraphBound
      reduction.spectralParameter reduction.poisson

/-- Physical Cauchy data form a closed Lagrangian subspace. -/
theorem cauchyData_closed_lagrangian
    (reduction : CanonicalPhysicalScalarBoundaryReductionData period hPeriod) :
    IsClosed
        (reduction.cauchyDataSubmodule period hPeriod :
          Set (CanonicalScalarHilbertBoundaryDatum
            (Trace := PhysicalTrace period hPeriod))) ∧
      canonicalScalarHilbertBoundarySymplecticOrthogonal
          (reduction.cauchyDataSubmodule period hPeriod) =
        reduction.cauchyDataSubmodule period hPeriod :=
  canonicalScalarGraphCauchyDataSubmodule_closed_lagrangian
    reduction.system reduction.abstractGraphBound
      reduction.spectralParameter reduction.poisson

/-- Physical Robin bulk modes are exactly the kernel of the physical boundary
Schur operator. -/
noncomputable def robinSolutionSchurKernelEquiv
    (reduction : CanonicalPhysicalScalarBoundaryReductionData period hPeriod)
    (robin : PhysicalTrace period hPeriod →L[Real]
      PhysicalTrace period hPeriod) :
    reduction.robinHomogeneousSolutionSubmodule period hPeriod robin ≃ₗ[Real]
      LinearMap.ker
        (reduction.boundarySchurOperator period hPeriod robin).toLinearMap :=
  canonicalScalarGraphRobinSolutionSchurKernelEquiv
    reduction.system reduction.abstractGraphBound
      reduction.spectralParameter reduction.poisson robin

/-- Physical boundary stationarity is exactly the Robin homogeneous bulk
problem. -/
theorem robinBoundaryStationary_iff_bulk
    (reduction : CanonicalPhysicalScalarBoundaryReductionData period hPeriod)
    (robin : PhysicalTrace period hPeriod →L[Real]
      PhysicalTrace period hPeriod)
    (boundary : PhysicalTrace period hPeriod) :
    CanonicalScalarGraphRobinBoundaryStationary
        reduction.system reduction.abstractGraphBound
          reduction.spectralParameter reduction.poisson robin boundary ↔
      reduction.poisson.poisson boundary ∈
        reduction.robinHomogeneousSolutionSubmodule period hPeriod robin :=
  canonicalScalarGraphRobinBoundaryStationary_iff_bulk_solution
    reduction.system reduction.abstractGraphBound
      reduction.spectralParameter reduction.poisson robin boundary

/-- Complete physical boundary-reduction certificate. -/
theorem certificate
    (reduction : CanonicalPhysicalScalarBoundaryReductionData period hPeriod)
    (robin : PhysicalTrace period hPeriod →L[Real]
      PhysicalTrace period hPeriod)
    (hRobin : robin.toLinearMap.IsSymmetric) :
    (reduction.dirichletToNeumann period hPeriod).toLinearMap.IsSymmetric ∧
      IsClosed
        (reduction.cauchyDataSubmodule period hPeriod :
          Set (CanonicalScalarHilbertBoundaryDatum
            (Trace := PhysicalTrace period hPeriod))) ∧
      canonicalScalarHilbertBoundarySymplecticOrthogonal
          (reduction.cauchyDataSubmodule period hPeriod) =
        reduction.cauchyDataSubmodule period hPeriod ∧
      (∀ boundary variation : PhysicalTrace period hPeriod,
        HasDerivAt
          (fun parameter : Real =>
            reduction.robinReducedAction period hPeriod robin
              (boundary + parameter • variation))
          (inner Real variation
            (reduction.boundarySchurOperator period hPeriod robin boundary)) 0) :=
  ⟨reduction.dirichletToNeumann_isSymmetric period hPeriod,
    (reduction.cauchyData_closed_lagrangian period hPeriod).1,
    (reduction.cauchyData_closed_lagrangian period hPeriod).2,
    canonicalScalarGraphRobinReducedAction_hasDerivAt
      reduction.system reduction.abstractGraphBound
        reduction.spectralParameter reduction.poisson robin hRobin⟩

end CanonicalPhysicalScalarBoundaryReductionData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarBoundaryReduction4D
end JanusFormal
