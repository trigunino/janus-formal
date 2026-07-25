import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusLocalMaxwellStressVariation4D

/-!
# Local Maxwell Euler term and boundary current

The gauge part of the Maxwell variation is integrated by parts pointwise:
it is the Maxwell Euler coefficient paired with the potential variation,
minus the coordinate divergence of the corresponding boundary current.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusLocalMaxwellEulerBoundary4D

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open P0EFTJanusMappingTorusLocalMaxwellStressVariation4D

abbrev Index4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Index4
abbrev Vector4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4
abbrev Matrix4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Matrix4

local instance localRealNormedAddCommGroup : NormedAddCommGroup ℝ :=
  inferInstance

local instance localRealNormedSpace : NormedSpace ℝ ℝ :=
  inferInstance

local instance localRealAddCommGroup : AddCommGroup ℝ :=
  localRealNormedAddCommGroup.toAddCommGroup

local instance (priority := 10000) localRealModule : Module ℝ ℝ :=
  localRealNormedSpace.toModule

def coordinatePartial
    (field : Vector4 → ℝ) (coordinate : Vector4) (index : Index4) : ℝ :=
  fderiv ℝ field coordinate (Pi.single index 1)

def gaugeCurvatureVelocity
    (variation : Vector4 → Vector4) (coordinate : Vector4)
    (first second : Index4) : ℝ :=
  coordinatePartial (fun current => variation current second) coordinate first -
    coordinatePartial (fun current => variation current first) coordinate second

def maxwellEulerCoefficient
    (excitation : Vector4 → Matrix4) (coordinate : Vector4)
    (second : Index4) : ℝ :=
  ∑ first : Index4,
    coordinatePartial (fun current => excitation current first second)
      coordinate first

def maxwellEulerPairing
    (excitation : Vector4 → Matrix4) (variation : Vector4 → Vector4)
    (coordinate : Vector4) : ℝ :=
  ∑ second : Index4,
    maxwellEulerCoefficient excitation coordinate second *
      variation coordinate second

def maxwellBoundaryCurrent
    (excitation : Vector4 → Matrix4) (variation : Vector4 → Vector4)
    (coordinate : Vector4) (first : Index4) : ℝ :=
  ∑ second : Index4,
    excitation coordinate first second * variation coordinate second

theorem maxwellBoundaryCurrent_eq_zero_of_dirichlet
    (excitation : Vector4 → Matrix4) (variation : Vector4 → Vector4)
    (coordinate : Vector4) (first : Index4)
    (hDirichlet : variation coordinate = 0) :
    maxwellBoundaryCurrent excitation variation coordinate first = 0 := by
  unfold maxwellBoundaryCurrent
  apply Finset.sum_eq_zero
  intro second _
  rw [hDirichlet]
  simp

def maxwellBoundaryDivergence
    (excitation : Vector4 → Matrix4) (variation : Vector4 → Vector4)
    (coordinate : Vector4) : ℝ :=
  ∑ first : Index4,
    coordinatePartial
      (fun current => maxwellBoundaryCurrent excitation variation current first)
      coordinate first

def rawMaxwellGaugeVariation
    (excitation : Vector4 → Matrix4) (variation : Vector4 → Vector4)
    (coordinate : Vector4) : ℝ :=
  -(1 / 2 : ℝ) *
    ∑ first : Index4, ∑ second : Index4,
      excitation coordinate first second *
        gaugeCurvatureVelocity variation coordinate first second

private theorem sum_four_swap_pairs
    (function : Index4 → Index4 → Index4 → Index4 → ℝ) :
    (∑ first : Index4, ∑ second : Index4,
      ∑ third : Index4, ∑ fourth : Index4,
        function first second third fourth) =
      ∑ third : Index4, ∑ fourth : Index4,
        ∑ first : Index4, ∑ second : Index4,
          function first second third fourth := by
  have hGroup (summand : Index4 → Index4 → ℝ) :
      (∑ first : Index4, ∑ second : Index4,
        summand first second) =
        ∑ pair : Index4 × Index4, summand pair.1 pair.2 :=
    (Fintype.sum_prod_type' summand).symm
  calc
    (∑ first : Index4, ∑ second : Index4,
        ∑ third : Index4, ∑ fourth : Index4,
          function first second third fourth) =
        ∑ firstSecond : Index4 × Index4,
          ∑ third : Index4, ∑ fourth : Index4,
            function firstSecond.1 firstSecond.2 third fourth :=
      hGroup _
    _ = ∑ firstSecond : Index4 × Index4,
          ∑ thirdFourth : Index4 × Index4,
            function firstSecond.1 firstSecond.2
              thirdFourth.1 thirdFourth.2 := by
          apply Finset.sum_congr rfl
          intro firstSecond _
          exact hGroup _
    _ = ∑ thirdFourth : Index4 × Index4,
          ∑ firstSecond : Index4 × Index4,
            function firstSecond.1 firstSecond.2
              thirdFourth.1 thirdFourth.2 := Finset.sum_comm
    _ = ∑ thirdFourth : Index4 × Index4,
          ∑ first : Index4, ∑ second : Index4,
            function first second thirdFourth.1 thirdFourth.2 := by
          apply Finset.sum_congr rfl
          intro thirdFourth _
          exact (hGroup (fun first second =>
            function first second thirdFourth.1 thirdFourth.2)).symm
    _ = ∑ third : Index4, ∑ fourth : Index4,
          ∑ first : Index4, ∑ second : Index4,
            function first second third fourth :=
      (hGroup (fun third fourth =>
        ∑ first : Index4, ∑ second : Index4,
          function first second third fourth)).symm

/-- The excitation field is derived pointwise from the varying volume,
inverse metric and curvature. -/
def maxwellExcitationField
    (volume : Vector4 → ℝ) (inverse : Vector4 → Matrix4)
    (curvature : Fin 2 → Vector4 → Matrix4)
    (component : Fin 2) (coordinate : Vector4) : Matrix4 :=
  maxwellExcitationAt (volume coordinate) (inverse coordinate)
    (curvature component coordinate)

private theorem gaugePairing_secondTerm_eq_firstTerm
    (inverse : Matrix4) (curvature curvatureVelocity : Matrix4)
    (hInverse : ∀ first second,
      inverse first second = inverse second first) :
    (∑ first : Index4, ∑ second : Index4,
      ∑ third : Index4, ∑ fourth : Index4,
        inverse first third * inverse second fourth *
          (curvature first second * curvatureVelocity third fourth)) =
      ∑ first : Index4, ∑ second : Index4,
        ∑ third : Index4, ∑ fourth : Index4,
          inverse first third * inverse second fourth *
            (curvatureVelocity first second * curvature third fourth) := by
  calc
    (∑ first : Index4, ∑ second : Index4,
        ∑ third : Index4, ∑ fourth : Index4,
          inverse first third * inverse second fourth *
            (curvature first second * curvatureVelocity third fourth)) =
        ∑ third : Index4, ∑ fourth : Index4,
          ∑ first : Index4, ∑ second : Index4,
            inverse first third * inverse second fourth *
              (curvature first second * curvatureVelocity third fourth) :=
      sum_four_swap_pairs _
    _ = ∑ third : Index4, ∑ fourth : Index4,
          ∑ first : Index4, ∑ second : Index4,
            inverse third first * inverse fourth second *
              (curvatureVelocity third fourth * curvature first second) := by
          apply Finset.sum_congr rfl
          intro third _
          apply Finset.sum_congr rfl
          intro fourth _
          apply Finset.sum_congr rfl
          intro first _
          apply Finset.sum_congr rfl
          intro second _
          rw [hInverse first third, hInverse second fourth]
          ring
    _ = _ := rfl

/-- The metric definition of the Maxwell gauge variation agrees exactly
with the sum of the raw excitation/curvature variations. -/
theorem localMaxwellGaugeVariation_eq_sum_raw
    (volume : Vector4 → ℝ) (inverse : Vector4 → Matrix4)
    (curvature : Fin 2 → Vector4 → Matrix4)
    (variation : Fin 2 → Vector4 → Vector4) (coordinate : Vector4)
    (hInverse : ∀ first second,
      inverse coordinate first second =
        inverse coordinate second first) :
    localMaxwellGaugeVariation (volume coordinate) (inverse coordinate)
        (fun component => curvature component coordinate)
        (fun component =>
          gaugeCurvatureVelocity (variation component) coordinate) =
      ∑ component : Fin 2,
        rawMaxwellGaugeVariation
          (maxwellExcitationField volume inverse curvature component)
          (variation component) coordinate := by
  unfold localMaxwellGaugeVariation maxwellGaugePairingVelocityAt
  have hPairing (component : Fin 2) :
      (∑ first : Index4, ∑ second : Index4,
        ∑ third : Index4, ∑ fourth : Index4,
          inverse coordinate first third *
            inverse coordinate second fourth *
            (gaugeCurvatureVelocity (variation component) coordinate
                  first second *
                curvature component coordinate third fourth +
              curvature component coordinate first second *
                gaugeCurvatureVelocity (variation component) coordinate
                  third fourth)) =
        2 * ∑ first : Index4, ∑ second : Index4,
          ∑ third : Index4, ∑ fourth : Index4,
            inverse coordinate first third *
              inverse coordinate second fourth *
              gaugeCurvatureVelocity (variation component) coordinate
                first second *
              curvature component coordinate third fourth := by
    simp_rw [mul_add, Finset.sum_add_distrib]
    rw [gaugePairing_secondTerm_eq_firstTerm
      (inverse coordinate) (curvature component coordinate)
      (gaugeCurvatureVelocity (variation component) coordinate) hInverse]
    ring
  simp_rw [hPairing]
  unfold rawMaxwellGaugeVariation maxwellExcitationField maxwellExcitationAt
  have hExcitation (component : Fin 2) :
      (∑ first : Index4, ∑ second : Index4,
        (volume coordinate *
          ∑ third : Index4, ∑ fourth : Index4,
            inverse coordinate first third *
              inverse coordinate second fourth *
              curvature component coordinate third fourth) *
          gaugeCurvatureVelocity (variation component) coordinate
            first second) =
        volume coordinate *
          ∑ first : Index4, ∑ second : Index4,
            ∑ third : Index4, ∑ fourth : Index4,
              inverse coordinate first third *
                inverse coordinate second fourth *
                gaugeCurvatureVelocity (variation component) coordinate
                  first second *
                curvature component coordinate third fourth := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro first _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro second _
    rw [mul_assoc]
    apply congrArg (volume coordinate * ·)
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro third _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro fourth _
    ring
  simp_rw [hExcitation]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro component _
  ring

private theorem boundaryDivergence_productRule
    (excitation : Vector4 → Matrix4) (variation : Vector4 → Vector4)
    (coordinate : Vector4)
    (hExcitation : ∀ first second,
      DifferentiableAt ℝ (fun current => excitation current first second)
        coordinate)
    (hVariation : ∀ second,
      DifferentiableAt ℝ (fun current => variation current second) coordinate) :
    maxwellBoundaryDivergence excitation variation coordinate =
      maxwellEulerPairing excitation variation coordinate +
        ∑ first : Index4, ∑ second : Index4,
          excitation coordinate first second *
            coordinatePartial (fun current => variation current second)
              coordinate first := by
  unfold maxwellBoundaryDivergence maxwellBoundaryCurrent coordinatePartial
    maxwellEulerPairing maxwellEulerCoefficient
  calc
    (∑ first : Index4,
        fderiv ℝ
          (fun current =>
            ∑ second : Index4,
              excitation current first second * variation current second)
          coordinate (Pi.single first 1)) =
        ∑ first : Index4, ∑ second : Index4,
          fderiv ℝ
            (fun current =>
              excitation current first second * variation current second)
            coordinate (Pi.single first 1) := by
      apply Finset.sum_congr rfl
      intro first _
      rw [fderiv_fun_sum]
      · simp
      · intro second _
        exact (hExcitation first second).mul (hVariation second)
    _ = _ := by
      have hProduct : ∀ first second : Index4,
          fderiv ℝ
              (fun current =>
                excitation current first second * variation current second)
              coordinate (Pi.single first 1) =
            fderiv ℝ (fun current => excitation current first second)
                coordinate (Pi.single first 1) * variation coordinate second +
              excitation coordinate first second *
                fderiv ℝ (fun current => variation current second)
                  coordinate (Pi.single first 1) := by
        intro first second
        have hDerivative := fderiv_mul
          (hExcitation first second) (hVariation second)
        have hApply := congrArg
          (fun derivative : Vector4 →L[ℝ] ℝ =>
            derivative (Pi.single first 1)) hDerivative
        simp only [ContinuousLinearMap.add_apply,
          ContinuousLinearMap.smul_apply, smul_eq_mul] at hApply
        rw [show
          (fun current =>
            excitation current first second * variation current second) =
          ((fun current => excitation current first second) *
            fun current => variation current second) by rfl]
        convert hApply using 1 <;> ring
      simp_rw [hProduct]
      simp_rw [Finset.sum_add_distrib]
      apply congrArg₂ (· + ·)
      · rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro second _
        rw [Finset.sum_mul]
        rfl
      · rfl

private theorem rawGaugeVariation_eq_neg_transport
    (excitation : Vector4 → Matrix4) (variation : Vector4 → Vector4)
    (coordinate : Vector4)
    (hSkew : ∀ first second,
      excitation coordinate second first =
        -excitation coordinate first second) :
    rawMaxwellGaugeVariation excitation variation coordinate =
      -(∑ first : Index4, ∑ second : Index4,
          excitation coordinate first second *
            coordinatePartial (fun current => variation current second)
              coordinate first) := by
  have hSwapped :
      (∑ first : Index4, ∑ second : Index4,
          excitation coordinate first second *
            coordinatePartial (fun current => variation current first)
              coordinate second) =
        -(∑ first : Index4, ∑ second : Index4,
          excitation coordinate first second *
            coordinatePartial (fun current => variation current second)
              coordinate first) := by
    calc
      (∑ first : Index4, ∑ second : Index4,
          excitation coordinate first second *
            coordinatePartial (fun current => variation current first)
              coordinate second) =
          ∑ first : Index4, ∑ second : Index4,
            excitation coordinate second first *
              coordinatePartial (fun current => variation current second)
                coordinate first := by
            rw [Finset.sum_comm]
      _ = ∑ first : Index4, ∑ second : Index4,
            (-excitation coordinate first second) *
              coordinatePartial (fun current => variation current second)
                coordinate first := by
            apply Finset.sum_congr rfl
            intro first _
            apply Finset.sum_congr rfl
            intro second _
            rw [hSkew first second]
      _ = _ := by
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro first _
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro second _
            ring
  unfold rawMaxwellGaugeVariation gaugeCurvatureVelocity
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  rw [hSwapped]
  ring

/-- Exact local Maxwell integration-by-parts identity. -/
theorem rawMaxwellGaugeVariation_eq_euler_sub_boundaryDivergence
    (excitation : Vector4 → Matrix4) (variation : Vector4 → Vector4)
    (coordinate : Vector4)
    (hExcitation : ∀ first second,
      DifferentiableAt ℝ (fun current => excitation current first second)
        coordinate)
    (hVariation : ∀ second,
      DifferentiableAt ℝ (fun current => variation current second) coordinate)
    (hSkew : ∀ first second,
      excitation coordinate second first =
        -excitation coordinate first second) :
    rawMaxwellGaugeVariation excitation variation coordinate =
      maxwellEulerPairing excitation variation coordinate -
        maxwellBoundaryDivergence excitation variation coordinate := by
  rw [rawGaugeVariation_eq_neg_transport excitation variation coordinate hSkew,
    boundaryDivergence_productRule excitation variation coordinate
      hExcitation hVariation]
  ring

end

end P0EFTJanusMappingTorusLocalMaxwellEulerBoundary4D
end JanusFormal
