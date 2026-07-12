import Mathlib
import JanusFormal.Branches.FundamentalGeometryD9ImmersedSpinCEllipticComplex.Gates.P0EFTJanusImmersionFiberAlgebra
import JanusFormal.Branches.FundamentalGeometryD9ImmersedSpinCEllipticComplex.Gates.P0EFTJanusCompleteGaugeFixedEllipticSymbol
import JanusFormal.Branches.FundamentalGeometryD9ImmersedSpinCEllipticComplex.Gates.P0EFTJanusNormalRootMonopoleSeparation
import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusNormalPinLiftBoundaryConditions

namespace JanusFormal
namespace P0EFTJanusImmersedSpinCOriginSynthesis

set_option autoImplicit false

open P0EFTJanusImmersionFiberAlgebra
open P0EFTJanusCompleteGaugeFixedEllipticSymbol
open P0EFTJanusNormalRootMonopoleSeparation
open P0EFTJanusNormalPinLiftBoundaryConditions

/--
The common geometric seed is not three unrelated bundles.  It is an immersed
SpinC hypersurface together with its symmetry group and action functional.

* the immersion gives `TΣ`, `NΣ`, the second fundamental form and metric
  variations;
* the SpinC determinant line gives the primitive monopole connection;
* the nontrivial normal line gives the flat quarter-root boundary twist;
* quotienting the configuration space by diffeomorphisms and `U(1)` gauge
  transformations produces the ghost complexes;
* the Hessian of the action produces Jacobi, Maxwell, Lichnerowicz and Dirac
  operators.
-/
structure ImmersedSpinCDerivedModuliProblem where
  hypersurfaceImmersionConstructed : Prop
  ambientMetricConstructed : Prop
  tangentNormalExactSequenceConstructed : Prop
  normalLineNontrivialProved : Prop
  normalRootFlatLineConstructed : Prop
  primitiveSpinCDeterminantLineConstructed : Prop
  normalAndMonopoleLinesDistinguished : Prop
  spinorModuleConstructed : Prop
  diffeomorphismSymmetryConstructed : Prop
  u1GaugeSymmetryConstructed : Prop
  invariantActionFunctionalConstructed : Prop
  gaugeFixingFermionConstructed : Prop
  brstBvTangentComplexConstructed : Prop
  hessianOperatorsConstructed : Prop

/-- Local fiber consequences of the immersion. -/
theorem immersion_rank_origin_matrix :
    (4 = 3 + 1) /\
    (symmetricTwoTensorRank 3 = 6) /\
    (tracelessSymmetricTwoTensorRank 3 = 5) /\
    (6 = 1 + 5) /\
    (gravityOneLoopSuperRank = 0) /\
    (maxwellOneLoopSuperRank = 1) := by
  exact ⟨by norm_num,
    janus_symmetric_tensor_rank,
    janus_traceless_tensor_rank,
    by norm_num,
    gravity_one_loop_super_rank_zero,
    maxwell_one_loop_super_rank_one⟩

/-- The immersion exact sequence identifies tangential directions as gauge and the quotient as normal. -/
theorem immersion_deformation_quotient_matrix
    (deformation : TangentVector3 × ℝ) :
    normalProjection (tangentInclusion deformation.1) = 0 /\
    (normalProjection deformation = 0 →
      ∃ vector : TangentVector3,
        tangentInclusion vector = deformation) /\
    (∃ representative : TangentVector3 × ℝ,
      normalProjection representative = deformation.2) := by
  exact ⟨normal_projection_tangent_inclusion deformation.1,
    ambient_kernel_is_tangential_image deformation,
    normal_projection_surjective deformation.2⟩

/-- The normal-root and primitive monopole lines cannot be collapsed into one line bundle. -/
theorem two_line_inputs_are_genuinely_distinct
    (normalRoot : NormalRootLineChernData)
    (monopole : PrimitiveMonopoleLineChernData) :
    normalRoot.firstChernNumber ≠ monopole.firstChernNumber :=
  normal_root_line_not_primitive_monopole normalRoot monopole

/-- Local ellipticity and global boundary phases originate in different parts of the same datum. -/
structure LocalGlobalOriginSplit where
  localPrincipalSymbolFromTangentMetric : Prop
  normalJacobiSymbolFromImmersion : Prop
  maxwellSymbolFromConnection : Prop
  metricSymbolFromHessian : Prop
  diracSymbolFromCliffordModule : Prop
  quarterBoundaryFromNormalRoot : Prop
  primitiveFluxFromSpinCLine : Prop
  ghostsFromGaugeQuotient : Prop

/-- Closure of the full origin statement. -/
def immersedSpinCOriginClosed
    (geometry : ImmersedSpinCDerivedModuliProblem)
    (split : LocalGlobalOriginSplit) : Prop :=
  geometry.hypersurfaceImmersionConstructed /\
  geometry.ambientMetricConstructed /\
  geometry.tangentNormalExactSequenceConstructed /\
  geometry.normalLineNontrivialProved /\
  geometry.normalRootFlatLineConstructed /\
  geometry.primitiveSpinCDeterminantLineConstructed /\
  geometry.normalAndMonopoleLinesDistinguished /\
  geometry.spinorModuleConstructed /\
  geometry.diffeomorphismSymmetryConstructed /\
  geometry.u1GaugeSymmetryConstructed /\
  geometry.invariantActionFunctionalConstructed /\
  geometry.gaugeFixingFermionConstructed /\
  geometry.brstBvTangentComplexConstructed /\
  geometry.hessianOperatorsConstructed /\
  split.localPrincipalSymbolFromTangentMetric /\
  split.normalJacobiSymbolFromImmersion /\
  split.maxwellSymbolFromConnection /\
  split.metricSymbolFromHessian /\
  split.diracSymbolFromCliffordModule /\
  split.quarterBoundaryFromNormalRoot /\
  split.primitiveFluxFromSpinCLine /\
  split.ghostsFromGaugeQuotient

/-- An immersion without the primitive determinant line cannot close the twisted Dirac/gauge sector. -/
theorem immersion_alone_does_not_close_origin
    (geometry : ImmersedSpinCDerivedModuliProblem)
    (split : LocalGlobalOriginSplit)
    (hMissing : Not geometry.primitiveSpinCDeterminantLineConstructed) :
    Not (immersedSpinCOriginClosed geometry split) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.2.1

/-- Bundles without a gauge-invariant action do not determine the Hessian or ghost complex. -/
theorem bundles_without_action_do_not_close_origin
    (geometry : ImmersedSpinCDerivedModuliProblem)
    (split : LocalGlobalOriginSplit)
    (hMissing : Not geometry.invariantActionFunctionalConstructed) :
    Not (immersedSpinCOriginClosed geometry split) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.2.2.2.2.2.2.1

/-- A gauge-invariant action without gauge fixing does not define the one-loop elliptic complex. -/
theorem action_without_gauge_fixing_does_not_close_origin
    (geometry : ImmersedSpinCDerivedModuliProblem)
    (split : LocalGlobalOriginSplit)
    (hMissing : Not geometry.gaugeFixingFermionConstructed) :
    Not (immersedSpinCOriginClosed geometry split) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.2.2.2.2.2.2.2.1

/--
The deepest common origin is therefore a derived moduli problem, not a single
ordinary bundle: immersed SpinC hypersurfaces with connection, modulo
reparametrizations and gauge transformations.  Its tangent/BRST complex yields
the fields and ghosts; its action Hessian yields the elliptic operators.
-/
structure DerivedModuliPhysicalStatus where
  configurationStackDefined : Prop
  immersionObjectsDefined : Prop
  spinCConnectionsDefined : Prop
  automorphismGroupoidDefined : Prop
  derivedTangentComplexComputed : Prop
  brstBvResolutionConstructed : Prop
  invariantActionDefined : Prop
  hessianEllipticAfterGaugeFixing : Prop
  determinantLineAndOrientationConstructed : Prop
  quantumMasterEquationProved : Prop
  renormalizedSuperdeterminantDerived : Prop
  physicalVacuumSelected : Prop


def derivedModuliPhysicalClosure
    (s : DerivedModuliPhysicalStatus) : Prop :=
  s.configurationStackDefined /\
  s.immersionObjectsDefined /\
  s.spinCConnectionsDefined /\
  s.automorphismGroupoidDefined /\
  s.derivedTangentComplexComputed /\
  s.brstBvResolutionConstructed /\
  s.invariantActionDefined /\
  s.hessianEllipticAfterGaugeFixing /\
  s.determinantLineAndOrientationConstructed /\
  s.quantumMasterEquationProved /\
  s.renormalizedSuperdeterminantDerived /\
  s.physicalVacuumSelected

end P0EFTJanusImmersedSpinCOriginSynthesis
end JanusFormal
