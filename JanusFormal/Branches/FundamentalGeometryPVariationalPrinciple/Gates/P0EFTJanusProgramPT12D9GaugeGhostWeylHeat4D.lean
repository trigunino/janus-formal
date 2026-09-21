import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusD9GaugeGhostContinuumHeatRegulator4D

/-!
A time-independent inverse-square summability input for the exact D9
diagonal spectrum implies positive-time heat summability and the existing
nuclear D9 heat certificate.  No full physical heat operator is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT12D9GaugeGhostWeylHeat4D

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section

open Set
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusD9GaugeGhostContinuumHeatRegulator4D
open P0EFTJanusGaugeGhostBlockD9UnboundedFredholm4D
open P0EFTJanusImmersionFiberAlgebra
open P0EFTJanusProgramPGlobalPhysicalLLHessianHeatRegulator4D

/-- Inverse-square weight away from the finite characteristic set. -/
def d9GaugeGhostInverseSquareWeight
    {ι : Type*}
    (covector : ι → TangentVector3)
    (index : ι × Fin 8) : Real :=
  if d9GaugeGhostUnboundedWeight covector index = 0 then 0
  else (d9GaugeGhostUnboundedWeight covector index ^ 2)⁻¹

/-- One time-independent Schatten-two input for the exact D9 multiplier. -/
structure D9GaugeGhostInverseSquareData4D
    {ι : Type*}
    (covector : ι → TangentVector3) where
  ellipticity : D9GaugeGhostFiniteCharacteristicEllipticity covector
  inverseSquareSummable :
    Summable (d9GaugeGhostInverseSquareWeight covector)

namespace D9GaugeGhostInverseSquareData4D

private theorem exp_neg_mul_le_inverseSquareMajorant
    (time weight : Real) (hTime : 0 < time) (hWeight : 0 < weight) :
    Real.exp (-time * weight) ≤
      (2 * Real.exp (-1) * time⁻¹) ^ 2 * (weight ^ 2)⁻¹ := by
  let halfEnergy := time * weight / 2
  have hHalfEnergy : 0 < halfEnergy := by
    dsimp only [halfEnergy]
    positivity
  have hLinear :
      Real.exp (-halfEnergy) ≤ Real.exp (-1) / halfEnergy := by
    apply (le_div_iff₀ hHalfEnergy).2
    simpa [mul_comm] using Real.mul_exp_neg_le_exp_neg_one halfEnergy
  have hSquare :
      Real.exp (-halfEnergy) ^ 2 ≤
        (Real.exp (-1) / halfEnergy) ^ 2 :=
    (sq_le_sq₀ (Real.exp_nonneg _) (by positivity)).2 hLinear
  calc
    Real.exp (-time * weight) = Real.exp (-halfEnergy) ^ 2 := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      dsimp only [halfEnergy]
      ring
    _ ≤ (Real.exp (-1) / halfEnergy) ^ 2 := hSquare
    _ = (2 * Real.exp (-1) * time⁻¹) ^ 2 * (weight ^ 2)⁻¹ := by
      dsimp only [halfEnergy]
      field_simp [ne_of_gt hTime, ne_of_gt hWeight]

/-- Every positive-time D9 heat series converges from the inverse-square input. -/
theorem heatSummable
    {ι : Type*} [DecidableEq ι]
    {covector : ι → TangentVector3}
    (spectral : D9GaugeGhostInverseSquareData4D covector)
    (time : HeatTime) :
    D9GaugeGhostHeatSummability4D covector time := by
  let zeroPart : ι × Fin 8 → Real := fun index =>
    if d9GaugeGhostUnboundedWeight covector index = 0 then
      d9GaugeGhostHeatWeight covector time index
    else 0
  let nonzeroPart : ι × Fin 8 → Real := fun index =>
    if d9GaugeGhostUnboundedWeight covector index = 0 then 0
    else d9GaugeGhostHeatWeight covector time index
  have hZeroPart : Summable zeroPart := by
    apply summable_of_hasFiniteSupport
    refine (Set.finite_coe_iff.mp spectral.ellipticity.characteristicFinite).subset ?_
    intro index hIndex
    by_contra hWeight
    change d9GaugeGhostUnboundedWeight covector index ≠ 0 at hWeight
    exact hIndex (by simp [zeroPart, hWeight])
  have hNonzeroPart : Summable nonzeroPart := by
    let constant := (2 * Real.exp (-1) * time.1⁻¹) ^ 2
    have hMajorant : Summable (fun index =>
        constant * d9GaugeGhostInverseSquareWeight covector index) :=
      spectral.inverseSquareSummable.mul_left constant
    apply hMajorant.of_nonneg_of_le
    · intro index
      simp only [nonzeroPart]
      split_ifs
      · exact le_rfl
      · exact d9GaugeGhostHeatWeight_nonnegative covector time index
    · intro index
      by_cases hWeight : d9GaugeGhostUnboundedWeight covector index = 0
      · simp [nonzeroPart, d9GaugeGhostInverseSquareWeight, hWeight]
      · have hWeightPos :
            0 < d9GaugeGhostUnboundedWeight covector index :=
          lt_of_le_of_ne
            (d9GaugeGhostUnboundedWeight_nonnegative covector index)
            (Ne.symm hWeight)
        simpa [nonzeroPart, d9GaugeGhostInverseSquareWeight, hWeight,
          constant, d9GaugeGhostHeatWeight] using
          exp_neg_mul_le_inverseSquareMajorant time.1
            (d9GaugeGhostUnboundedWeight covector index) time.2 hWeightPos
  have hTotal : Summable (fun index => zeroPart index + nonzeroPart index) :=
    hZeroPart.add hNonzeroPart
  refine hTotal.congr ?_
  intro index
  by_cases hWeight : d9GaugeGhostUnboundedWeight covector index = 0
  · simp [zeroPart, nonzeroPart, hWeight]
  · simp [zeroPart, nonzeroPart, hWeight]

/-- Existing nuclear D9 heat certificate generated at every positive time. -/
def toHeatNuclearCertificate
    {ι : Type*} [DecidableEq ι]
    {covector : ι → TangentVector3}
    (spectral : D9GaugeGhostInverseSquareData4D covector)
    (time : HeatTime) :
    D9GaugeGhostHeatNuclearCertificate4D covector time :=
  d9GaugeGhostHeatNuclearCertificate4D covector time
    (spectral.heatSummable time)

/-- Public conditional D9 Weyl-to-nuclear-heat checkpoint. -/
theorem nuclearHeat_gate
    {ι : Type*} [DecidableEq ι]
    {covector : ι → TangentVector3}
    (spectral : D9GaugeGhostInverseSquareData4D covector)
    (time : HeatTime) :
    Nonempty (D9GaugeGhostHeatNuclearCertificate4D covector time) :=
  ⟨spectral.toHeatNuclearCertificate time⟩

end D9GaugeGhostInverseSquareData4D

end
end P0EFTJanusProgramPT12D9GaugeGhostWeylHeat4D
end JanusFormal
