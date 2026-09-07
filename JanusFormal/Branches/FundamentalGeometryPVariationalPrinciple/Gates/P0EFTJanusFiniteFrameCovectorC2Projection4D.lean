import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameLorenzCovariantTrace4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D

/-! # Bounded projection onto coherent finite-frame covector coefficients

The transpose reconstruction matrix sends arbitrary coefficients to the
evaluations of their reconstructed covector. It fixes genuine potential
coefficients and is idempotent on the whole completed C² coefficient space.
-/

namespace JanusFormal
namespace P0EFTJanusFiniteFrameCovectorC2Projection4D

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section
open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D
open P0EFTJanusFiniteFrameBRSTPairing4D
open P0EFTJanusFiniteFrameMetricContraction4D
open P0EFTJanusFiniteFrameLorenzCovariantTrace4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
private abbrev C2Scalar := CanonicalPhysicalScalarC2JetCore period hPeriod

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod
local instance : NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (C2Scalar period hPeriod) := inferInstance

private abbrev TangentFiber (point : EffectiveQuotient period hPeriod) :=
  TangentSpace coverModelWithCorners point
private abbrev SmoothCovectorSection :=
  ContMDiffSection coverModelWithCorners (CoverCoordinates →L[Real] Real) ∞
    (fun point : EffectiveQuotient period hPeriod => TangentFiber period hPeriod point →L[Real] Real)

variable (frame : SmoothD8Frame period hPeriod)
  (reference : SmoothGeneralLorentzMetric period hPeriod)

/-- Entry `(output,input)` is the true dual evaluation `θ_input(e_output)`. -/
def finiteFrameCovectorProjectionCoefficient (output input : Fin frame.count) :
    SmoothScalarField period hPeriod :=
  generalMetricFiniteFrameCoefficient period hPeriod frame reference
    (smoothFrameVectorSection period hPeriod frame output) input

@[simp] theorem finiteFrameCovectorProjectionCoefficient_apply
    (output input : Fin frame.count) (point : EffectiveQuotient period hPeriod) :
    finiteFrameCovectorProjectionCoefficient period hPeriod frame reference output input point =
      generalMetricFiniteFrameCoefficientAt period hPeriod frame reference point input
        (frame.vectorAt point output) := rfl

/-- A genuine smooth covector reconstructed from arbitrary smooth coefficients. -/
def finiteFrameCovectorFromSmoothCoefficients
    (coefficients : Fin frame.count → SmoothScalarField period hPeriod) : SmoothCovectorSection period hPeriod :=
  ∑ index : Fin frame.count,
    { toFun := fun point => coefficients index point • finiteFrameDualCovector period hPeriod frame reference index point
      contMDiff_toFun := (coefficients index).contMDiff_toFun.smul_section
        (finiteFrameDualCovector period hPeriod frame reference index).contMDiff }

@[simp] theorem finiteFrameCovectorFromSmoothCoefficients_apply
    (coefficients : Fin frame.count → SmoothScalarField period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    finiteFrameCovectorFromSmoothCoefficients period hPeriod frame reference coefficients point =
      ∑ index : Fin frame.count, coefficients index point •
        generalMetricFiniteFrameCoefficientAt period hPeriod frame reference point index := by
  let evaluation : SmoothCovectorSection period hPeriod →ₗ[Real]
      (TangentFiber period hPeriod point →L[Real] Real) :=
    { toFun := fun field => field point
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  simpa only [finiteFrameDualCovector_apply, finiteFrameCovectorFromSmoothCoefficients,
    evaluation, LinearMap.coe_mk, AddHom.coe_mk, ContMDiffSection.coeFn_mk] using
    (map_sum evaluation (fun index : Fin frame.count =>
      ({ toFun := fun current => coefficients index current •
          finiteFrameDualCovector period hPeriod frame reference index current
         contMDiff_toFun := (coefficients index).contMDiff_toFun.smul_section
           (finiteFrameDualCovector period hPeriod frame reference index).contMDiff } :
        SmoothCovectorSection period hPeriod)) Finset.univ)

def finiteFrameCovectorSmoothProjection
    (coefficients : Fin frame.count → SmoothScalarField period hPeriod) :
    Fin frame.count → SmoothScalarField period hPeriod :=
  fun output => ∑ input : Fin frame.count, smoothScalarFieldMul period hPeriod
    (finiteFrameCovectorProjectionCoefficient period hPeriod frame reference output input) (coefficients input)

/-- Projected smooth coefficients are the actual evaluations of the reconstructed covector. -/
theorem finiteFrameCovectorSmoothProjection_apply
    (coefficients : Fin frame.count → SmoothScalarField period hPeriod)
    (output : Fin frame.count) (point : EffectiveQuotient period hPeriod) :
    finiteFrameCovectorSmoothProjection period hPeriod frame reference coefficients output point =
      finiteFrameCovectorFromSmoothCoefficients period hPeriod frame reference coefficients point
        (frame.vectorAt point output) := by
  rw [finiteFrameCovectorFromSmoothCoefficients_apply]
  simp only [finiteFrameCovectorSmoothProjection,
    P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0FiniteMatrixProduct4D.smoothScalarFieldFinsetSum_apply,
    smoothScalarFieldMul_apply, finiteFrameCovectorProjectionCoefficient_apply,
    sum_apply, smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro input _
  exact mul_comm _ _

theorem finiteFrameCovectorSmoothProjection_reconstructs
    (coefficients : Fin frame.count → SmoothScalarField period hPeriod) :
    finiteFrameCovectorFromSmoothCoefficients period hPeriod frame reference
      (finiteFrameCovectorSmoothProjection period hPeriod frame reference coefficients) =
    finiteFrameCovectorFromSmoothCoefficients period hPeriod frame reference coefficients := by
  apply ContMDiffSection.ext
  intro point
  rw [finiteFrameCovectorFromSmoothCoefficients_apply]
  simp_rw [finiteFrameCovectorSmoothProjection_apply]
  exact (finiteFrameCovector_reconstructs period hPeriod frame reference point
    (finiteFrameCovectorFromSmoothCoefficients period hPeriod frame reference coefficients point)).symm

theorem finiteFrameCovectorSmoothProjection_idempotent
    (coefficients : Fin frame.count → SmoothScalarField period hPeriod) :
    finiteFrameCovectorSmoothProjection period hPeriod frame reference
      (finiteFrameCovectorSmoothProjection period hPeriod frame reference coefficients) =
    finiteFrameCovectorSmoothProjection period hPeriod frame reference coefficients := by
  funext output
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  simp only [finiteFrameCovectorSmoothProjection_apply, finiteFrameCovectorSmoothProjection_reconstructs]

def finiteFrameCovectorC2Projection :
    (Fin frame.count → C2Scalar period hPeriod) →L[Real] (Fin frame.count → C2Scalar period hPeriod) :=
  ContinuousLinearMap.pi fun output => ∑ input : Fin frame.count,
    (canonicalPhysicalScalarC2JetCoreProduct period hPeriod
      (smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
        (finiteFrameCovectorProjectionCoefficient period hPeriod frame reference output input))).comp
      (ContinuousLinearMap.proj input)

@[simp] theorem finiteFrameCovectorC2Projection_apply
    (coefficients : Fin frame.count → C2Scalar period hPeriod) (output : Fin frame.count) :
    finiteFrameCovectorC2Projection period hPeriod frame reference coefficients output =
      ∑ input : Fin frame.count, canonicalPhysicalScalarC2JetCoreProduct period hPeriod
        (smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
          (finiteFrameCovectorProjectionCoefficient period hPeriod frame reference output input))
        (coefficients input) := by
  simp only [finiteFrameCovectorC2Projection, ContinuousLinearMap.pi_apply, sum_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]

theorem finiteFrameCovectorC2Projection_smooth_coefficients
    (coefficients : Fin frame.count → SmoothScalarField period hPeriod) :
    finiteFrameCovectorC2Projection period hPeriod frame reference
      (fun input => smoothToCanonicalPhysicalScalarC2JetCore period hPeriod (coefficients input)) =
    fun output => smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
      (finiteFrameCovectorSmoothProjection period hPeriod frame reference coefficients output) := by
  funext output
  rw [finiteFrameCovectorC2Projection_apply]
  change (∑ input : Fin frame.count, canonicalPhysicalScalarC2JetCoreProduct period hPeriod
    (smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
      (finiteFrameCovectorProjectionCoefficient period hPeriod frame reference output input))
    (smoothToCanonicalPhysicalScalarC2JetCore period hPeriod (coefficients input))) =
    smoothToCanonicalPhysicalScalarC2JetCore period hPeriod (∑ input : Fin frame.count,
      smoothScalarFieldMul period hPeriod
        (finiteFrameCovectorProjectionCoefficient period hPeriod frame reference output input) (coefficients input))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro input _
  exact canonicalPhysicalScalarC2JetCoreProduct_smooth period hPeriod _ _

/-- Every true potential coefficient tuple is fixed, as a whole C² equality. -/
theorem finiteFrameCovectorC2Projection_fixes_potential
    (potential : SmoothAbelianGaugePotential period hPeriod) (component : Fin 2) :
    finiteFrameCovectorC2Projection period hPeriod frame reference
      (fun index => smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
        (finiteFramePotentialCoefficient period hPeriod frame potential component index)) =
    fun index => smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
      (finiteFramePotentialCoefficient period hPeriod frame potential component index) := by
  rw [finiteFrameCovectorC2Projection_smooth_coefficients]
  funext output
  apply congrArg (smoothToCanonicalPhysicalScalarC2JetCore period hPeriod)
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  rw [finiteFrameCovectorSmoothProjection_apply, finiteFrameCovectorFromSmoothCoefficients_apply]
  simpa only [sum_apply, smul_apply, smul_eq_mul, finiteFramePotentialCoefficient_apply] using
    (finiteFrameCovector_pairing period hPeriod frame reference point
      (potential.toFun component point) (frame.vectorAt point output)).symm

/-- Idempotence holds on all completed coefficients, including noncanonical packets. -/
theorem finiteFrameCovectorC2Projection_idempotent
    (coefficients : Fin frame.count → C2Scalar period hPeriod) :
    finiteFrameCovectorC2Projection period hPeriod frame reference
      (finiteFrameCovectorC2Projection period hPeriod frame reference coefficients) =
    finiteFrameCovectorC2Projection period hPeriod frame reference coefficients := by
  have hDense : DenseRange (fun fields : Fin frame.count → SmoothScalarField period hPeriod =>
      fun index => smoothToCanonicalPhysicalScalarC2JetCore period hPeriod (fields index)) :=
    DenseRange.piMap fun _ => smoothToCanonicalPhysicalScalarC2JetCore_denseRange period hPeriod
  refine hDense.induction_on coefficients
    (isClosed_eq ((finiteFrameCovectorC2Projection period hPeriod frame reference).comp
      (finiteFrameCovectorC2Projection period hPeriod frame reference)).continuous
        (finiteFrameCovectorC2Projection period hPeriod frame reference).continuous) ?_
  intro fields
  simp only [finiteFrameCovectorC2Projection_smooth_coefficients, finiteFrameCovectorSmoothProjection_idempotent]

/-- The same bounded projection acts separately on the two abelian components. -/
def finiteFrameGaugeC2Projection :
    (Fin 2 → Fin frame.count → C2Scalar period hPeriod) →L[Real]
      (Fin 2 → Fin frame.count → C2Scalar period hPeriod) :=
  ContinuousLinearMap.pi fun component =>
    (finiteFrameCovectorC2Projection period hPeriod frame reference).comp (ContinuousLinearMap.proj component)

@[simp] theorem finiteFrameGaugeC2Projection_apply
    (coefficients : Fin 2 → Fin frame.count → C2Scalar period hPeriod) (component : Fin 2) :
    finiteFrameGaugeC2Projection period hPeriod frame reference coefficients component =
      finiteFrameCovectorC2Projection period hPeriod frame reference (coefficients component) := rfl

theorem finiteFrameGaugeC2Projection_fixes_potential (potential : SmoothAbelianGaugePotential period hPeriod) :
    finiteFrameGaugeC2Projection period hPeriod frame reference
      (fun component index => smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
        (finiteFramePotentialCoefficient period hPeriod frame potential component index)) =
    fun component index => smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
      (finiteFramePotentialCoefficient period hPeriod frame potential component index) := by
  funext component
  exact finiteFrameCovectorC2Projection_fixes_potential period hPeriod frame reference potential component

theorem finiteFrameGaugeC2Projection_idempotent
    (coefficients : Fin 2 → Fin frame.count → C2Scalar period hPeriod) :
    finiteFrameGaugeC2Projection period hPeriod frame reference
      (finiteFrameGaugeC2Projection period hPeriod frame reference coefficients) =
    finiteFrameGaugeC2Projection period hPeriod frame reference coefficients := by
  funext component
  exact finiteFrameCovectorC2Projection_idempotent period hPeriod frame reference (coefficients component)

end
end P0EFTJanusFiniteFrameCovectorC2Projection4D
end JanusFormal
