import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCoerciveBoundaryProblem4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarGraphInterfaceCoerciveGluing4D

/-!
# Physical scalar two-bulk interface gluing

Two physical coercive Dirichlet problems at the same real spectral parameter
produce two Poisson/DtN maps on the canonical throat Hilbert space.  A symmetric
junction operator glues them through the interface Schur operator

`M_left + M_right - J`.

Coercivity and surjectivity of this interface operator construct the common
boundary value, the two bulk fields and the unique sourced junction solution.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarInterfaceGluing4D

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
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCoerciveBoundaryProblem4D
open P0EFTJanusMappingTorusScalarGraphInterfaceGluing4D
open P0EFTJanusMappingTorusScalarGraphInterfaceCoerciveGluing4D

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

/-- Two physical Dirichlet problems at one common spectral parameter. -/
structure CanonicalPhysicalScalarInterfaceDirichletData where
  left : CanonicalPhysicalScalarDirichletCoerciveData period hPeriod
  right : CanonicalPhysicalScalarDirichletCoerciveData period hPeriod
  sameParameter : left.spectralParameter = right.spectralParameter

namespace CanonicalPhysicalScalarInterfaceDirichletData

/-- Common spectral parameter. -/
def spectralParameter
    (physical : CanonicalPhysicalScalarInterfaceDirichletData period hPeriod) : Real :=
  physical.left.spectralParameter

/-- Right Poisson data transported to the common parameter. -/
noncomputable def rightPoissonAtCommon
    (physical : CanonicalPhysicalScalarInterfaceDirichletData period hPeriod) :
    P0EFTJanusMappingTorusScalarGraphPoissonDirichletToNeumann4D.CanonicalScalarGraphDirichletPoissonData
      physical.right.system physical.right.abstractGraphBound
        physical.spectralParameter := by
  rw [physical.sameParameter]
  exact physical.right.poissonData

/-- Physical two-sided interface Poisson data. -/
noncomputable def interfaceData
    (physical : CanonicalPhysicalScalarInterfaceDirichletData period hPeriod) :
    CanonicalScalarGraphInterfacePoissonData
      physical.left.system physical.left.abstractGraphBound
      physical.right.system physical.right.abstractGraphBound
      physical.spectralParameter where
  leftPoisson := physical.left.poissonData
  rightPoisson := physical.rightPoissonAtCommon period hPeriod

/-- Left physical DtN. -/
def leftDtN
    (physical : CanonicalPhysicalScalarInterfaceDirichletData period hPeriod) :=
  physical.interfaceData.leftDtN

/-- Right physical DtN. -/
def rightDtN
    (physical : CanonicalPhysicalScalarInterfaceDirichletData period hPeriod) :=
  physical.interfaceData.rightDtN

/-- Interface Schur operator for a physical junction law. -/
def schur
    (physical : CanonicalPhysicalScalarInterfaceDirichletData period hPeriod)
    (junction : PhysicalTrace period hPeriod →L[Real]
      PhysicalTrace period hPeriod) :=
  physical.interfaceData.schurOperator junction

/-- Interface Schur symmetry. -/
theorem schur_isSymmetric
    (physical : CanonicalPhysicalScalarInterfaceDirichletData period hPeriod)
    (junction : PhysicalTrace period hPeriod →L[Real]
      PhysicalTrace period hPeriod)
    (hJunction : junction.toLinearMap.IsSymmetric) :
    (physical.schur junction).toLinearMap.IsSymmetric :=
  physical.interfaceData.schurOperator_isSymmetric junction hJunction

end CanonicalPhysicalScalarInterfaceDirichletData

/-- Coercive physical interface problem. -/
structure CanonicalPhysicalScalarInterfaceCoerciveData
    (physical : CanonicalPhysicalScalarInterfaceDirichletData period hPeriod) where
  junction : PhysicalTrace period hPeriod →L[Real]
    PhysicalTrace period hPeriod
  coercive : CanonicalScalarGraphInterfaceSchurCoerciveSurjectiveData
    physical.interfaceData junction
  positive : CanonicalScalarGraphInterfaceSchurPositiveData
    physical.interfaceData junction

namespace CanonicalPhysicalScalarInterfaceCoerciveData

/-- Bounded common-boundary inverse. -/
noncomputable def boundaryInverse
    {physical : CanonicalPhysicalScalarInterfaceDirichletData period hPeriod}
    (gluing : CanonicalPhysicalScalarInterfaceCoerciveData
      period hPeriod physical) :
    PhysicalTrace period hPeriod →L[Real] PhysicalTrace period hPeriod :=
  gluing.coercive.inverse

/-- Glued physical bulk pair. -/
def gluedSolution
    {physical : CanonicalPhysicalScalarInterfaceDirichletData period hPeriod}
    (gluing : CanonicalPhysicalScalarInterfaceCoerciveData
      period hPeriod physical) :=
  gluing.coercive.gluedSolution

/-- Exact sourced physical interface equation. -/
theorem junction_equation
    {physical : CanonicalPhysicalScalarInterfaceDirichletData period hPeriod}
    (gluing : CanonicalPhysicalScalarInterfaceCoerciveData
      period hPeriod physical)
    (source : PhysicalTrace period hPeriod) :
    physical.interfaceData.schurOperator gluing.junction
        (gluing.boundaryInverse source) = source :=
  gluing.coercive.schur_inverse source

/-- Unique minimizing physical interface boundary. -/
theorem boundary_unique_minimizer
    {physical : CanonicalPhysicalScalarInterfaceDirichletData period hPeriod}
    (gluing : CanonicalPhysicalScalarInterfaceCoerciveData
      period hPeriod physical)
    (source : PhysicalTrace period hPeriod) :
    (∀ boundary : PhysicalTrace period hPeriod,
      canonicalScalarGraphInterfaceSourceAction
          physical.interfaceData gluing.junction source
          (gluing.boundaryInverse source) ≤
        canonicalScalarGraphInterfaceSourceAction
          physical.interfaceData gluing.junction source boundary) ∧
      (∀ boundary : PhysicalTrace period hPeriod,
        canonicalScalarGraphInterfaceSourceAction
            physical.interfaceData gluing.junction source boundary =
          canonicalScalarGraphInterfaceSourceAction
            physical.interfaceData gluing.junction source
            (gluing.boundaryInverse source) →
        boundary = gluing.boundaryInverse source) :=
  canonicalScalarGraphInterfaceSourceAction_unique_minimizer
    physical.interfaceData gluing.junction gluing.positive source
      (gluing.boundaryInverse source) (gluing.junction_equation source)

/-- Physical interface gluing certificate. -/
theorem certificate
    {physical : CanonicalPhysicalScalarInterfaceDirichletData period hPeriod}
    (gluing : CanonicalPhysicalScalarInterfaceCoerciveData
      period hPeriod physical)
    (source : PhysicalTrace period hPeriod) :
    physical.interfaceData.schurOperator gluing.junction
          (gluing.boundaryInverse source) = source ∧
      (∀ boundary : PhysicalTrace period hPeriod,
        canonicalScalarGraphInterfaceSourceAction
            physical.interfaceData gluing.junction source
            (gluing.boundaryInverse source) ≤
          canonicalScalarGraphInterfaceSourceAction
            physical.interfaceData gluing.junction source boundary) ∧
      P0EFTJanusMappingTorusScalarGraphPoissonDirichletToNeumann4D.canonicalScalarGraphShiftedOperator
          physical.left.system physical.spectralParameter
          (gluing.gluedSolution source).1 = 0 ∧
      P0EFTJanusMappingTorusScalarGraphPoissonDirichletToNeumann4D.canonicalScalarGraphShiftedOperator
          physical.right.system physical.spectralParameter
          (gluing.gluedSolution source).2 = 0 :=
  canonicalScalarGraphInterfaceCoerciveGluing_certificate
    physical.interfaceData gluing.junction gluing.coercive gluing.positive source

end CanonicalPhysicalScalarInterfaceCoerciveData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarInterfaceGluing4D
end JanusFormal
