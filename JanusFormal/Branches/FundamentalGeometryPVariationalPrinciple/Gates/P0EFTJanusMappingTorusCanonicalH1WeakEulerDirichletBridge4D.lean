import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalH1FunctionQuotient4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalH1DirichletSpace4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGlobalHolonomicScalarActualHessian4D

/-!
# Canonical H1 boundary domain for the global scalar weak equation

The canonical graph-H1 trace already has a genuine homogeneous Dirichlet
kernel.  We map that kernel to the new function quotient and prove that every
smooth homogeneous Dirichlet variation lands in this quotient domain.  On
exactly the same smooth variations, stationarity of the unchanged global D8
scalar action is equivalent to its weak Euler equation, and its actual mixed
Hessian is the symmetric Jacobi pairing.

This does not assert that the weak Euler operator extends continuously to the
whole H1 quotient.  It also does not identify the positive static energy model
with the full Lorentzian dynamics.  A trace on the function quotient still
requires the already isolated vertical-kernel condition.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalH1WeakEulerDirichletBridge4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarAction4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarVariation4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarWeakJacobiRiesz4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarActualHessian4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusPositiveLatitudeRadialPolarJacobian4D
open P0EFTJanusMappingTorusCanonicalH1FunctionQuotient4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1DirichletSpace4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Smooth variations carrying the retained homogeneous throat condition. -/
abbrev SmoothHomogeneousDirichletScalarTest :=
  { variation : GlobalScalarTestSpace period hPeriod //
    SatisfiesDirichlet period hPeriod Real 0 variation }

/-- The honest boundary domain in the function quotient: classes admitting a
representative in the kernel of the already constructed graph-H1 trace. -/
def CanonicalH1FunctionQuotientDirichletDomain :
    Submodule Real
      (CanonicalPhysicalScalarH1FunctionQuotient period hPeriod) :=
  (CanonicalPhysicalDirichletH1 period hPeriod).map
    (canonicalH1FunctionQuotientMap period hPeriod).toLinearMap

/-- Every smooth pointwise homogeneous Dirichlet variation enters that
quotient boundary domain through the canonical smooth H1 map. -/
theorem smooth_dirichlet_mem_functionQuotientDirichletDomain
    (variation : GlobalScalarTestSpace period hPeriod)
    (hDirichlet : SatisfiesDirichlet period hPeriod Real 0 variation) :
    smoothToCanonicalH1FunctionQuotient period hPeriod variation ∈
      CanonicalH1FunctionQuotientDirichletDomain period hPeriod := by
  refine ⟨smoothToCanonicalPhysicalScalarH1 period hPeriod variation,
    smooth_zeroDirichlet_mem_canonicalPhysicalDirichletH1 period hPeriod
      variation hDirichlet, ?_⟩
  rfl

/-- If the exact vertical-kernel condition holds, every class in the quotient
Dirichlet domain has zero descended trace. -/
theorem functionQuotientDirichletDomain_le_traceKernel
    (hDescends : CanonicalH1TraceDescendsToFunctionQuotient period hPeriod) :
    CanonicalH1FunctionQuotientDirichletDomain period hPeriod ≤
      (canonicalH1FunctionQuotientTrace period hPeriod hDescends).ker := by
  rintro _ ⟨representative, hRepresentative, rfl⟩
  change canonicalPhysicalH1TraceRadialPolar period hPeriod representative = 0
  exact hRepresentative

/-- Stationarity of the unchanged global scalar action along precisely the
smooth variations satisfying the retained homogeneous boundary condition. -/
def CanonicalH1DirichletGlobalScalarStationary
    (data : GlobalHolonomicScalarFormData period hPeriod)
    (field : GlobalScalarTestSpace period hPeriod) : Prop :=
  ∀ variation : SmoothHomogeneousDirichletScalarTest period hPeriod,
    HasDerivAt
      (fun epsilon : Real =>
        globalHolonomicScalarAction period hPeriod data.massSquared
          data.magnitude
          (scalarAffineCurve period hPeriod field variation.1 epsilon)
          data.measure)
      0 0

/-- The weak Euler equation tested on that same smooth Dirichlet core. -/
def SatisfiesCanonicalH1DirichletWeakScalarEquation
    (data : GlobalHolonomicScalarFormData period hPeriod)
    (field : GlobalScalarTestSpace period hPeriod) : Prop :=
  ∀ variation : SmoothHomogeneousDirichletScalarTest period hPeriod,
    weakGlobalHolonomicScalarEulerOperator period hPeriod data field
      variation.1 = 0

/-- The boundary-restricted weak equation is exactly stationarity of the same
global action, not an independently postulated Euler operator. -/
theorem canonicalH1DirichletGlobalScalarStationary_iff_weakEuler
    (data : GlobalHolonomicScalarFormData period hPeriod)
    (field : GlobalScalarTestSpace period hPeriod) :
    CanonicalH1DirichletGlobalScalarStationary period hPeriod data field ↔
      SatisfiesCanonicalH1DirichletWeakScalarEquation period hPeriod data
        field := by
  constructor
  · intro hStationary variation
    exact (globalHolonomicScalarAction_hasDerivAt_weakEuler period hPeriod data
      field variation.1).unique (hStationary variation)
  · intro hWeak variation
    simpa [hWeak variation] using
      (globalHolonomicScalarAction_hasDerivAt_weakEuler period hPeriod data
        field variation.1)

/-- On two variations from the same boundary core, the actual Hessian of the
unchanged action is exactly the previously derived Jacobi pairing. -/
theorem canonicalH1Dirichlet_actualHessian_eq_jacobi
    (data : GlobalHolonomicScalarFormData period hPeriod)
    (field : GlobalScalarTestSpace period hPeriod)
    (first second : SmoothHomogeneousDirichletScalarTest period hPeriod) :
    globalHolonomicScalarActionMixedHessian period hPeriod data field
        first.1 second.1 =
      weakGlobalHolonomicScalarJacobiOperator period hPeriod data
        first.1 second.1 :=
  globalHolonomicScalarActionMixedHessian_eq_jacobi period hPeriod data field
    first.1 second.1

/-- Schwarz symmetry remains valid after imposing the same H1 boundary core
on both Hessian directions. -/
theorem canonicalH1Dirichlet_actualHessian_symmetric
    (data : GlobalHolonomicScalarFormData period hPeriod)
    (field : GlobalScalarTestSpace period hPeriod)
    (first second : SmoothHomogeneousDirichletScalarTest period hPeriod) :
    globalHolonomicScalarActionMixedHessian period hPeriod data field
        first.1 second.1 =
      globalHolonomicScalarActionMixedHessian period hPeriod data field
        second.1 first.1 :=
  globalHolonomicScalarActionMixedHessian_symmetric period hPeriod data field
    first.1 second.1

theorem canonical_h1_weak_euler_dirichlet_bridge4D
    (data : GlobalHolonomicScalarFormData period hPeriod)
    (field : GlobalScalarTestSpace period hPeriod) :
    (∀ variation : SmoothHomogeneousDirichletScalarTest period hPeriod,
      smoothToCanonicalH1FunctionQuotient period hPeriod variation.1 ∈
        CanonicalH1FunctionQuotientDirichletDomain period hPeriod) ∧
    (CanonicalH1DirichletGlobalScalarStationary period hPeriod data field ↔
      SatisfiesCanonicalH1DirichletWeakScalarEquation period hPeriod data
        field) ∧
    (∀ first second : SmoothHomogeneousDirichletScalarTest period hPeriod,
      globalHolonomicScalarActionMixedHessian period hPeriod data field
          first.1 second.1 =
        globalHolonomicScalarActionMixedHessian period hPeriod data field
          second.1 first.1) := by
  exact ⟨fun variation =>
      smooth_dirichlet_mem_functionQuotientDirichletDomain period hPeriod
        variation.1 variation.2,
    canonicalH1DirichletGlobalScalarStationary_iff_weakEuler period hPeriod
      data field,
    canonicalH1Dirichlet_actualHessian_symmetric period hPeriod data field⟩

end

end P0EFTJanusMappingTorusCanonicalH1WeakEulerDirichletBridge4D
end JanusFormal
