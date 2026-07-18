import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusAbelianGaugeBRST4D

/-!
# Abelian gauge generator and Noether operator on the D8 quotient

The exact infinitesimal action `c ↦ dc` is bundled as a real linear map,
both for one gauge potential and for the two independent sectors.  Euler
covectors then compose with this generator to give the Noether operator.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusAbelianGaugeNoetherOperator4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

instance : SMul Real (SmoothAbelianGaugePotential period hPeriod) where
  smul scalar potential :=
    { toFun := fun component point =>
        scalar • potential.toFun component point
      contMDiff_eval := fun component => by
        have h := (contMDiff_const :
          ContMDiff coverModelWithCorners.tangent
            (modelWithCornersSelf Real Real) ∞
            (fun _ : TangentBundle coverModelWithCorners
              (EffectiveQuotient period hPeriod) => scalar)).mul
            (potential.contMDiff_eval component)
        convert h using 1
        funext vector
        change scalar * potential.toFun component vector.1 vector.2 = _
        rfl }

@[simp]
theorem smoothAbelianGaugePotential_smul_apply
    (scalar : Real) (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2) (point) (tangent) :
    (scalar • potential).toFun component point tangent =
      scalar • potential.toFun component point tangent :=
  rfl

instance : Module Real (SmoothAbelianGaugePotential period hPeriod) where
  one_smul := by intro potential; apply SmoothAbelianGaugePotential.ext; intro c p v; exact congrArg (fun f : TangentSpace coverModelWithCorners p →L[Real] Real => f v) (one_smul Real (potential.toFun c p))
  mul_smul := by intro a b potential; apply SmoothAbelianGaugePotential.ext; intro c p v; exact congrArg (fun f : TangentSpace coverModelWithCorners p →L[Real] Real => f v) (mul_smul a b (potential.toFun c p))
  smul_add := by intro a first second; apply SmoothAbelianGaugePotential.ext; intro c p v; exact congrArg (fun f : TangentSpace coverModelWithCorners p →L[Real] Real => f v) (smul_add a (first.toFun c p) (second.toFun c p))
  smul_zero := by intro a; apply SmoothAbelianGaugePotential.ext; intro _ p v; exact congrArg (fun f : TangentSpace coverModelWithCorners p →L[Real] Real => f v) (smul_zero a)
  add_smul := by intro a b potential; apply SmoothAbelianGaugePotential.ext; intro c p v; exact congrArg (fun f : TangentSpace coverModelWithCorners p →L[Real] Real => f v) (add_smul a b (potential.toFun c p))
  zero_smul := by intro potential; apply SmoothAbelianGaugePotential.ext; intro c p v; exact congrArg (fun f : TangentSpace coverModelWithCorners p →L[Real] Real => f v) (zero_smul Real (potential.toFun c p))

theorem exactGaugePotential_smul
    (scalar : Real)
    (ghost : SmoothQuotientField period hPeriod GaugeLieAlgebra) :
    exactGaugePotential period hPeriod (scalar • ghost) =
      scalar • exactGaugePotential period hPeriod ghost := by
  apply SmoothAbelianGaugePotential.ext
  intro component point tangent
  change mvfderiv _
      (ghostComponent period hPeriod (scalar • ghost) component).toFun point tangent = _
  have hComponent :
      ghostComponent period hPeriod (scalar • ghost) component =
        scalar • ghostComponent period hPeriod ghost component := by
    apply SmoothQuotientField.ext period hPeriod Real
    intro x
    exact (EuclideanSpace.proj component).map_smul scalar (ghost x)
  rw [hComponent]
  change mvfderiv coverModelWithCorners
      ((fun _ : EffectiveQuotient period hPeriod => scalar) *
        (ghostComponent period hPeriod ghost component).toFun) point tangent = _
  have hConst : MDifferentiableAt coverModelWithCorners
      (modelWithCornersSelf Real Real)
      (fun _ : EffectiveQuotient period hPeriod => scalar) point :=
    (contMDiff_const : ContMDiff coverModelWithCorners
      (modelWithCornersSelf Real Real) ∞
      (fun _ : EffectiveQuotient period hPeriod => scalar)).mdifferentiableAt (by simp)
  rw [mvfderiv_mul
    hConst
    ((ghostComponent period hPeriod ghost component).contMDiff_toFun.mdifferentiableAt
      (by simp))]
  rw [mvfderiv_const scalar]
  change scalar * _ + _ * 0 = scalar * _
  rw [mul_zero, add_zero]
  rfl

/-- The infinitesimal abelian gauge generator `R_A(c) = dc`. -/
def abelianGaugeGenerator :
    SmoothQuotientField period hPeriod GaugeLieAlgebra →ₗ[Real]
      SmoothAbelianGaugePotential period hPeriod where
  toFun := exactGaugePotential period hPeriod
  map_add' := exactGaugePotential_add period hPeriod
  map_smul' := exactGaugePotential_smul period hPeriod

@[simp]
theorem abelianGaugeGenerator_apply
    (parameter : SmoothQuotientField period hPeriod GaugeLieAlgebra) :
    abelianGaugeGenerator period hPeriod parameter =
      exactGaugePotential period hPeriod parameter :=
  rfl

/-- The exact generator acting independently on the two gauge sectors. -/
def abelianGaugePairGenerator :
    (SmoothQuotientField period hPeriod GaugeLieAlgebra ×
      SmoothQuotientField period hPeriod GaugeLieAlgebra) →ₗ[Real]
    (SmoothAbelianGaugePotential period hPeriod ×
      SmoothAbelianGaugePotential period hPeriod) where
  toFun parameters :=
    (abelianGaugeGenerator period hPeriod parameters.1,
      abelianGaugeGenerator period hPeriod parameters.2)
  map_add' first second := by
    apply Prod.ext
    · exact exactGaugePotential_add period hPeriod first.1 second.1
    · exact exactGaugePotential_add period hPeriod first.2 second.2
  map_smul' scalar parameters := by
    apply Prod.ext
    · exact exactGaugePotential_smul period hPeriod scalar parameters.1
    · exact exactGaugePotential_smul period hPeriod scalar parameters.2

@[simp]
theorem abelianGaugePairGenerator_apply
    (parameters : SmoothQuotientField period hPeriod GaugeLieAlgebra ×
      SmoothQuotientField period hPeriod GaugeLieAlgebra) :
    abelianGaugePairGenerator period hPeriod parameters =
      (exactGaugePotential period hPeriod parameters.1,
        exactGaugePotential period hPeriod parameters.2) :=
  rfl

/-- The affine gauge action by translation with the exact potential. -/
def abelianGaugeAffineAction
    (parameter : SmoothQuotientField period hPeriod GaugeLieAlgebra)
    (potential : SmoothAbelianGaugePotential period hPeriod) :
    SmoothAbelianGaugePotential period hPeriod :=
  potential + abelianGaugeGenerator period hPeriod parameter

@[simp]
theorem abelianGaugeAffineAction_apply
    (parameter : SmoothQuotientField period hPeriod GaugeLieAlgebra)
    (potential : SmoothAbelianGaugePotential period hPeriod) :
    abelianGaugeAffineAction period hPeriod parameter potential =
      potential + exactGaugePotential period hPeriod parameter :=
  rfl

/-- The Noether operator `E_A ∘ R_A`. -/
def abelianGaugeNoetherOperator
    (euler : SmoothAbelianGaugePotential period hPeriod →ₗ[Real] Real) :
    SmoothQuotientField period hPeriod GaugeLieAlgebra →ₗ[Real] Real :=
  euler.comp (abelianGaugeGenerator period hPeriod)

@[simp]
theorem abelianGaugeNoetherOperator_apply
    (euler : SmoothAbelianGaugePotential period hPeriod →ₗ[Real] Real)
    (parameter : SmoothQuotientField period hPeriod GaugeLieAlgebra) :
    abelianGaugeNoetherOperator period hPeriod euler parameter =
      euler (exactGaugePotential period hPeriod parameter) :=
  rfl

/-- The existing independent ghosts are exactly the two abelian parameters. -/
def independentFieldsAbelianGaugeParameters
    (fields : IndependentFields period hPeriod) :
    SmoothQuotientField period hPeriod GaugeLieAlgebra ×
      SmoothQuotientField period hPeriod GaugeLieAlgebra :=
  fields.ghosts

@[simp]
theorem independentFieldsAbelianGaugeParameters_eq
    (fields : IndependentFields period hPeriod) :
    independentFieldsAbelianGaugeParameters period hPeriod fields = fields.ghosts :=
  rfl

end


end P0EFTJanusMappingTorusAbelianGaugeNoetherOperator4D
end JanusFormal
