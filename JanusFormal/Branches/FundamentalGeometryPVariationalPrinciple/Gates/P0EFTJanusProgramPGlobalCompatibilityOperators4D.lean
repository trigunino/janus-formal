import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalFieldSpace4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusQuotientLorentzGramAlgebraicIdentity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusQuotientLorentzGramRotationComplex4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusSaintVenantEinsteinBianchiSymbolBridge
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusAbelianGaugeNoetherOperator4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntrinsicLeviCivitaBianchi4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalTotalHolonomicAtlasScalarStressClosure4D

/-!
# Global Program-P compatibility operators

This gate gives separate names to the already constructed nonlinear Gram
output, its genuine quotient Jacobian, the quotient rotation generator, the
curved Levi--Civita curvature/Bianchi differential, and the Noether operator.
The flat `Fin 4` Saint--Venant sequence is retained only as a principal-symbol
corollary.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCompatibilityOperators4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusIntrinsicCoverLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusQuotientLorentzGramAlgebraicIdentity4D
open P0EFTJanusMappingTorusQuotientLorentzGramRotationComplex4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusAbelianGaugeNoetherOperator4D
open P0EFTJanusMappingTorusIntrinsicLeviCivitaBianchi4D
open P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionJets4D
open P0EFTJanusMappingTorusCanonicalTotalHolonomicAtlasScalarStressClosure4D
open P0EFTJanusArbitraryFrequencySaintVenantExactness
open P0EFTJanusLinearizedEinsteinBianchiSymbol
open P0EFTJanusSaintVenantEinsteinBianchiSymbolBridge
open P0EFTJanusProgramPGlobalFieldSpace4D

variable (period : Real) (hPeriod : period ≠ 0)

abbrev SymbolCovector :=
  P0EFTJanusSaintVenantEinsteinBianchiSymbolBridge.Covector4
abbrev SymbolVector :=
  P0EFTJanusSaintVenantEinsteinBianchiSymbolBridge.Vector4
abbrev SymbolTensor2 :=
  P0EFTJanusSaintVenantEinsteinBianchiSymbolBridge.Tensor2
abbrev SymbolTensor4 :=
  P0EFTJanusArbitraryFrequencySaintVenantExactness.CovariantFourTensor
abbrev EinsteinPerturbation :=
  P0EFTJanusSaintVenantEinsteinBianchiSymbolBridge.SymmetricPerturbation
abbrev IntrinsicCurvatureEndomorphism :=
  P0EFTJanusMappingTorusIntrinsicLeviCivitaBianchi4D.Endomorphism4
abbrev IntrinsicVector4 :=
  P0EFTJanusMappingTorusIntrinsicLeviCivitaBianchi4D.Vector4
abbrev IntrinsicIndex4 :=
  P0EFTJanusMappingTorusIntrinsicLeviCivitaBianchi4D.Index4
abbrev IntrinsicCurvatureAtlasField :=
  SmoothHolonomicFrameChart4 period hPeriod →
    IntrinsicVector4 → IntrinsicIndex4 → IntrinsicIndex4 →
      IntrinsicCurvatureEndomorphism
abbrev IntrinsicBianchiAtlasField :=
  SmoothHolonomicFrameChart4 period hPeriod →
    IntrinsicVector4 → IntrinsicIndex4 → IntrinsicIndex4 →
      IntrinsicIndex4 → IntrinsicCurvatureEndomorphism

private abbrev EffectiveCover :=
  MappingTorusCover (reflectedSphereData period hPeriod)
private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveCoverChartedSpace :
    ChartedSpace CoverModel (EffectiveCover period hPeriod) :=
  reflectedSphereCoverChartedSpace period hPeriod

local instance effectiveCoverIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveCover period hPeriod) :=
  reflectedSphereCover_isManifold period hPeriod

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- `K_Gram`: the nonlinear Gram output of the actual Janus immersion on the
true quotient tensor bundle. -/
def K_Gram : SmoothCovariantTwoTensor period hPeriod :=
  quotientCanonicalLorentzGramCompatibilityOutput period hPeriod

/-- `DK_Gram`: the genuine quotient component Jacobian on its smooth descent
domain. -/
def DK_Gram
    (first second : CoverCoordinates)
    (variation :
      QuotientLorentzGramJacobianDomain period hPeriod first second) :
    SmoothQuotientField period hPeriod Real :=
  quotientLorentzGramJacobianOperator period hPeriod first second variation

/-- `R`: the descended spatial-rotation generator, already valued in the
domain of `DK_Gram`. -/
def R
    (first second : CoverCoordinates) (axis : Fin 3) :
    QuotientLorentzGramJacobianDomain period hPeriod first second :=
  quotientLorentzGramRotationIntoJacobianDomain period hPeriod
    first second axis

/-- Flat Saint--Venant principal symbol, retained for comparison with the
intrinsic differential operator. -/
def K_SV_symbol
    (covector : SymbolCovector) (tensor : SymbolTensor2) :
    SymbolTensor4 :=
  saintVenantSymbol covector tensor

/-- Corresponding flat infinitesimal-strain symbol. -/
def R_SV_symbol (covector : SymbolCovector) (variation : SymbolVector) :
    SymbolTensor2 :=
  strainSymbol covector variation

/-- `K_SV`: the genuine second-order curvature compatibility operator on
every patch of the canonical total holonomic atlas. -/
def K_SV
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    IntrinsicCurvatureAtlasField period hPeriod :=
  fun patch =>
    localLeviCivitaCurvatureField period hPeriod metric patch

/-- `B_Noether`: the exact global abelian Noether operator on smooth quotient
ghosts and smooth quotient one-forms. -/
def B_Noether
    (euler : SmoothAbelianGaugePotential period hPeriod →ₗ[Real] Real) :
    SmoothQuotientField period hPeriod GaugeLieAlgebra →ₗ[Real] Real :=
  abelianGaugeNoetherOperator period hPeriod euler

/-- Flat raised-divergence principal symbol, retained as a symbol-level
corollary. -/
def B_Bianchi_symbol
    (covector : SymbolCovector) (tensor : SymbolTensor2) : SymbolCovector :=
  raisedTensorDivergenceSymbol covector tensor

/-- `B_Bianchi`: the genuine covariant cyclic derivative on an arbitrary
curvature presentation over the same canonical total atlas. -/
def B_Bianchi
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (curvature : IntrinsicCurvatureAtlasField period hPeriod) :
    IntrinsicBianchiAtlasField period hPeriod :=
  fun patch =>
    localLeviCivitaBianchiDifferential period hPeriod metric patch
      (curvature patch)

/-- The two global `U(1)` ghosts are read from the unique Program-P
configuration. -/
def globalAbelianGaugeParameters
    (configuration : GlobalFieldConfiguration period hPeriod) :
    SmoothQuotientField period hPeriod GaugeLieAlgebra ×
      SmoothQuotientField period hPeriod GaugeLieAlgebra :=
  configuration.coefficientFields.ghosts

@[simp]
theorem DK_Gram_comp_R_eq_zero
    (axis : Fin 3) (first second : CoverCoordinates)
    (point : EffectiveQuotient period hPeriod) :
    DK_Gram period hPeriod first second
        (R period hPeriod first second axis) point = 0 :=
  quotientLorentzGramJacobian_comp_rotation_eq_zero period hPeriod
    axis first second point

@[simp]
theorem K_SV_comp_R_SV_eq_zero
    (covector : SymbolCovector) (variation : SymbolVector) :
    K_SV_symbol covector (R_SV_symbol covector variation) = 0 :=
  saintVenantSymbol_strainSymbol_eq_zero covector variation

@[simp]
theorem B_Bianchi_symbol_comp_linearizedEinstein_eq_zero
    (covector : SymbolCovector) (perturbation : EinsteinPerturbation) :
    B_Bianchi_symbol covector
        (linearizedEinsteinSymbol covector perturbation) = 0 :=
  raisedTensorDivergenceSymbol_comp_linearizedEinstein_eq_zero
    covector perturbation

@[simp]
theorem B_Bianchi_comp_K_SV_eq_zero
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : IntrinsicVector4)
    (first second third : IntrinsicIndex4) :
    B_Bianchi period hPeriod metric (K_SV period hPeriod metric)
        patch coordinate first second third = 0 :=
  localLeviCivitaBianchiOperator_eq_zero period hPeriod metric patch
    coordinate first second third

/-- The connection used by `K_SV/B_Bianchi` has the genuine nonlinear
Levi--Civita transition law on every overlap. -/
theorem intrinsicLeviCivita_transition_agreement
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : IntrinsicVector4)
    (samePoint : firstPatch.coordinateMap firstCoordinate =
      secondPatch.coordinateMap secondCoordinate) :
    HolonomicLeviCivitaTransitionAgreement period hPeriod metric firstPatch
      secondPatch firstCoordinate secondCoordinate :=
  canonicalHolonomicLeviCivitaTransitionAgreement period hPeriod metric
    firstPatch secondPatch firstCoordinate secondCoordinate samePoint

/-- Coordinate-global form: every physical quotient point has a canonical
holonomic representative on which the true Bianchi composite vanishes in all
components. -/
theorem B_Bianchi_comp_K_SV_eq_zero_at_every_point
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    ∃ patch : SmoothHolonomicFrameChart4 period hPeriod,
      ∃ coordinate : IntrinsicVector4,
        patch.coordinateMap coordinate = point ∧
          ∀ first second third : IntrinsicIndex4,
            B_Bianchi period hPeriod metric (K_SV period hPeriod metric)
              patch coordinate first second third = 0 := by
  rcases canonicalTotalHolonomicChartThroughEveryPoint period hPeriod point with
    ⟨patch, coordinate, hCoordinate⟩
  exact ⟨patch, coordinate, hCoordinate, fun first second third =>
    B_Bianchi_comp_K_SV_eq_zero period hPeriod metric patch coordinate
      first second third⟩

@[simp]
theorem B_Noether_apply
    (euler : SmoothAbelianGaugePotential period hPeriod →ₗ[Real] Real)
    (ghost : SmoothQuotientField period hPeriod GaugeLieAlgebra) :
    B_Noether period hPeriod euler ghost =
      euler (exactGaugePotential period hPeriod ghost) :=
  abelianGaugeNoetherOperator_apply period hPeriod euler ghost

/-- Concrete operator-level closure on the physical quotient, together with
the explicitly separated flat principal-symbol corollaries. -/
theorem global_compatibility_operator_gate
    (axis : Fin 3) (first second : CoverCoordinates)
    (point : EffectiveQuotient period hPeriod)
    (covector : SymbolCovector) (variation : SymbolVector)
    (perturbation : EinsteinPerturbation)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : IntrinsicVector4)
    (curvatureFirst curvatureSecond curvatureThird : IntrinsicIndex4)
    (euler : SmoothAbelianGaugePotential period hPeriod →ₗ[Real] Real)
    (ghost : SmoothQuotientField period hPeriod GaugeLieAlgebra) :
    DK_Gram period hPeriod first second
          (R period hPeriod first second axis) point = 0 ∧
      K_SV_symbol covector (R_SV_symbol covector variation) = 0 ∧
      B_Bianchi_symbol covector
          (linearizedEinsteinSymbol covector perturbation) = 0 ∧
      B_Bianchi period hPeriod metric (K_SV period hPeriod metric)
          patch coordinate curvatureFirst curvatureSecond curvatureThird = 0 ∧
      (∃ physicalPatch : SmoothHolonomicFrameChart4 period hPeriod,
        ∃ physicalCoordinate : IntrinsicVector4,
          physicalPatch.coordinateMap physicalCoordinate = point ∧
            ∀ left middle right : IntrinsicIndex4,
              B_Bianchi period hPeriod metric (K_SV period hPeriod metric)
                physicalPatch physicalCoordinate left middle right = 0) ∧
      B_Noether period hPeriod euler ghost =
        euler (exactGaugePotential period hPeriod ghost) := by
  exact ⟨DK_Gram_comp_R_eq_zero period hPeriod axis first second point,
    K_SV_comp_R_SV_eq_zero covector variation,
    B_Bianchi_symbol_comp_linearizedEinstein_eq_zero covector perturbation,
    B_Bianchi_comp_K_SV_eq_zero period hPeriod metric patch coordinate
      curvatureFirst curvatureSecond curvatureThird,
    B_Bianchi_comp_K_SV_eq_zero_at_every_point period hPeriod metric point,
    B_Noether_apply period hPeriod euler ghost⟩

end
end P0EFTJanusProgramPGlobalCompatibilityOperators4D
end JanusFormal
