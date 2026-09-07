import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusInteractionSpectralCommutatorReduction4D

/-! # Actual relative-velocity recentering algebra

For a metric-chart root `S`, its inverse `T`, and their velocities `U`, `V`,
the differentiated root and inverse identities determine the frame commutator.
The original Leibniz velocity of `T * C * T` consequently has the same spectral
variation as the centered velocity. No relative-velocity equality or selected
root equivariance is assumed.
-/

namespace JanusFormal
namespace P0EFTJanusPairedRelativeVelocityCommutator4D
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
open scoped Matrix.Norms.Frobenius
open P0EFTJanusReciprocalBimetricPotential
open P0EFTJanusMatrixInteractionFrechetNoether
open P0EFTJanusInteractionSpectralCommutatorReduction4D
private abbrev Matrix4 := Matrix (Fin 4) (Fin 4) Real

/-- The actual three-factor Leibniz derivative, with the native parentheses. -/
def matrixPairedOriginalRelativeVelocity (T V C dC : Matrix4) : Matrix4 :=
  T * (C * V + dC * T) + V * (C * T)

/-- Centered velocity with transported metric and cross directions. -/
def matrixPairedRelativeCenterVelocity (relative metricDirection crossDirection : Matrix4) :
    Matrix4 :=
  relative * (-((1 / 2 : Real) • metricDirection)) + crossDirection +
    (-((1 / 2 : Real) • metricDirection)) * relative

/-- The frame generator forced by the original inverse-root velocity. -/
def matrixPairedRecenterGenerator (S T V K : Matrix4) : Matrix4 :=
  S * V + (1 / 2 : Real) • (T * (K * T))

/-- Differentiating the square and inverse identities fixes the symmetric
part of the frame velocity. -/
theorem matrixInverseRootVelocity_sylvester_sandwich
    (S T U V K : Matrix4)
    (hST : S * T = 1) (hTS : T * S = 1)
    (hRoot : S * U + U * S = K)
    (hInverse : V = -(T * (U * T))) :
    V * S + S * V = -(T * (K * T)) := by
  have hLeft : V * S = -(T * U) := by
    calc
      V * S = -((T * (U * T)) * S) := by rw [hInverse, neg_mul]
      _ = -(T * (U * (T * S))) := by simp only [mul_assoc]
      _ = -(T * U) := by rw [hTS, mul_one]
  have hRight : S * V = -(U * T) := by
    calc
      S * V = -(S * (T * (U * T))) := by rw [hInverse, mul_neg]
      _ = -((S * T) * (U * T)) := by rw [mul_assoc]
      _ = -(U * T) := by rw [hST, one_mul]
  have hSandwich : T * (K * T) = U * T + T * U := by
    calc
      T * (K * T) = (T * S) * (U * T) + (T * U) * (S * T) := by
        rw [← hRoot]
        noncomm_ring
      _ = U * T + T * U := by rw [hTS, hST, one_mul, mul_one]
  rw [hLeft, hRight, hSandwich]
  abel

private theorem matrixPairedRelativeVelocity_commutator_of_half
    (S T V C dC half : Matrix4)
    (hST : S * T = 1) (hTS : T * S = 1)
    (hVelocity : V * S + S * V = -(half + half)) :
    T * (C * V + dC * T) + V * (C * T) =
      ((T * (C * T)) * (-half) + T * (dC * T) +
        (-half) * (T * (C * T))) +
      ((T * (C * T)) * (S * V + half) -
        (S * V + half) * (T * (C * T))) := by
  have hLeft : (V * S) * (T * (C * T)) = V * (C * T) := by
    calc
      (V * S) * (T * (C * T)) = V * ((S * T) * (C * T)) := by
        noncomm_ring
      _ = V * (C * T) := by rw [hST, one_mul]
  have hRight : (T * (C * T)) * (S * V) = T * (C * V) := by
    calc
      (T * (C * T)) * (S * V) = T * (C * ((T * S) * V)) := by
        noncomm_ring
      _ = T * (C * V) := by rw [hTS, one_mul]
  have hAnticommutator : V * S = -(S * V) - half - half := by
    calc
      V * S = (V * S + S * V) - S * V := by abel
      _ = -(half + half) - S * V := by rw [hVelocity]
      _ = -(S * V) - half - half := by abel
  calc
    _ = (V * S) * (T * (C * T)) + T * (dC * T) +
        (T * (C * T)) * (S * V) := by
      rw [hLeft, hRight]
      noncomm_ring
    _ = _ := by
      rw [hAnticommutator]
      noncomm_ring

/-- Concrete commutator identity for original and recentered relative
velocities. Its hypotheses are precisely the differentiated branch identities. -/
theorem matrixPairedRelativeVelocity_recenter_commutator
    (S T U V K C dC : Matrix4)
    (hST : S * T = 1) (hTS : T * S = 1)
    (hRoot : S * U + U * S = K)
    (hInverse : V = -(T * (U * T))) :
    matrixPairedOriginalRelativeVelocity T V C dC =
      matrixPairedRelativeCenterVelocity (T * (C * T)) (T * (K * T))
        (T * (dC * T)) +
      ((T * (C * T)) * matrixPairedRecenterGenerator S T V K -
        matrixPairedRecenterGenerator S T V K * (T * (C * T))) := by
  have hHalf : (1 / 2 : Real) • (T * (K * T)) +
      (1 / 2 : Real) • (T * (K * T)) = T * (K * T) := by
    rw [← add_smul]
    norm_num
  have hVelocity : V * S + S * V =
      -((1 / 2 : Real) • (T * (K * T)) +
        (1 / 2 : Real) • (T * (K * T))) := by
    rw [hHalf]
    exact matrixInverseRootVelocity_sylvester_sandwich S T U V K hST hTS hRoot hInverse
  exact matrixPairedRelativeVelocity_commutator_of_half S T V C dC
    ((1 / 2 : Real) • (T * (K * T))) hST hTS hVelocity

/-- The spectral differential agrees for the actual original Leibniz velocity
and the transported centered velocity. Only square/inverse identities and the
two root-derivative Sylvester equations are required. -/
theorem matrixPairedSpectralDerivative_recenter
    (coefficients : PotentialCoefficients)
    (S T U V K C dC root originalRootVelocity centeredRootVelocity : Matrix4)
    (hST : S * T = 1) (hTS : T * S = 1)
    (hRoot : S * U + U * S = K)
    (hInverse : V = -(T * (U * T)))
    (hSquare : root * root = 1 + T * (C * T))
    (hInjective : Function.Injective (fun velocity : Matrix4 => root * velocity + velocity * root))
    (hOriginalSylvester : root * originalRootVelocity + originalRootVelocity * root =
      matrixPairedOriginalRelativeVelocity T V C dC)
    (hCenteredSylvester : root * centeredRootVelocity + centeredRootVelocity * root =
      matrixPairedRelativeCenterVelocity (T * (C * T)) (T * (K * T))
        (T * (dC * T))) :
    matrixSpectralPotentialDerivative coefficients root originalRootVelocity =
      matrixSpectralPotentialDerivative coefficients root centeredRootVelocity := by
  apply matrixSpectralPotentialDerivative_eq_of_relative_commutator coefficients root
    (T * (C * T)) originalRootVelocity centeredRootVelocity
    (matrixPairedRecenterGenerator S T V K) hSquare hInjective
  rw [hOriginalSylvester, hCenteredSylvester]
  exact matrixPairedRelativeVelocity_recenter_commutator S T U V K C dC
    hST hTS hRoot hInverse

end
end P0EFTJanusPairedRelativeVelocityCommutator4D
end JanusFormal
