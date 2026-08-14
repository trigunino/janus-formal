import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteCommutingProjectionKernelResolution4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPDifferentiableFiniteKernelBasisFamily4D

/-!
# Sector-preserving transport of finite actual kernels

A family of actual kernels may be globally trivialized without projecting an
arbitrary moving basis.  It is enough to have linear equivalences between the
true kernel fibres that commute with the physical kernel projectors.

Transporting one sector-resolved basepoint basis then gives a basis of every
kernel whose vectors remain fixed by the same sector projectors.  This route has
no Gram determinant and no angle condition: the only geometric input is a
sector-preserving kernel transport.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiniteSectorPreservingKernelTransport4D

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open P0EFTJanusProgramPFiniteKernelBasisFamily4D
open P0EFTJanusProgramPDifferentiableFiniteKernelBasisFamily4D

variable {Sector ZeroMode E : Type*}
  [Fintype Sector] [DecidableEq Sector]
  [Fintype ZeroMode] [DecidableEq ZeroMode]
  [NormedAddCommGroup E] [NormedSpace Real E]

/-- A coherent family of actual-kernel equivalences commuting with a supplied
physical projector resolution on every kernel fibre. -/
structure FiniteSectorPreservingKernelTransportData
    (operator : Real → E →L[Real] E)
    (kernelProjection : ∀ parameter,
      Sector → (operator parameter).ker →L[Real] (operator parameter).ker) where
  transport : ∀ first second,
    (operator first).ker ≃ₗ[Real] (operator second).ker
  transport_self : ∀ parameter,
    transport parameter parameter = LinearEquiv.refl Real _
  transport_trans : ∀ first second third,
    (transport second third).comp (transport first second) =
      transport first third
  transport_commutes : ∀ first second sector vector,
    transport first second (kernelProjection first sector vector) =
      kernelProjection second sector (transport first second vector)

namespace FiniteSectorPreservingKernelTransportData

/-- Transport one basepoint basis to the current actual kernel fibre. -/
def transportedBasis
    {operator : Real → E →L[Real] E}
    {kernelProjection : ∀ parameter,
      Sector → (operator parameter).ker →L[Real] (operator parameter).ker}
    (data : FiniteSectorPreservingKernelTransportData
      operator kernelProjection)
    (basisZero : Basis ZeroMode Real (operator 0).ker)
    (parameter : Real) :
    Basis ZeroMode Real (operator parameter).ker :=
  basisZero.map (data.transport 0 parameter)

@[simp]
theorem transportedBasis_apply
    {operator : Real → E →L[Real] E}
    {kernelProjection : ∀ parameter,
      Sector → (operator parameter).ker →L[Real] (operator parameter).ker}
    (data : FiniteSectorPreservingKernelTransportData
      operator kernelProjection)
    (basisZero : Basis ZeroMode Real (operator 0).ker)
    (parameter : Real) (mode : ZeroMode) :
    data.transportedBasis basisZero parameter mode =
      data.transport 0 parameter (basisZero mode) :=
  rfl

/-- At the basepoint the transported basis is literally the selected initial
basis. -/
theorem transportedBasis_zero
    {operator : Real → E →L[Real] E}
    {kernelProjection : ∀ parameter,
      Sector → (operator parameter).ker →L[Real] (operator parameter).ker}
    (data : FiniteSectorPreservingKernelTransportData
      operator kernelProjection)
    (basisZero : Basis ZeroMode Real (operator 0).ker) :
    data.transportedBasis basisZero 0 = basisZero := by
  ext mode
  rw [transportedBasis_apply, data.transport_self 0]
  rfl

/-- Sector resolution at the basepoint is preserved exactly by transport. -/
theorem transportedBasis_fixed_by_sector
    {operator : Real → E →L[Real] E}
    {kernelProjection : ∀ parameter,
      Sector → (operator parameter).ker →L[Real] (operator parameter).ker}
    (data : FiniteSectorPreservingKernelTransportData
      operator kernelProjection)
    (basisZero : Basis ZeroMode Real (operator 0).ker)
    (sectorOf : ZeroMode → Sector)
    (hBasepoint : ∀ mode,
      kernelProjection 0 (sectorOf mode) (basisZero mode) = basisZero mode)
    (parameter : Real) (mode : ZeroMode) :
    kernelProjection parameter (sectorOf mode)
        (data.transportedBasis basisZero parameter mode) =
      data.transportedBasis basisZero parameter mode := by
  rw [transportedBasis_apply]
  rw [← data.transport_commutes 0 parameter (sectorOf mode) (basisZero mode)]
  rw [hBasepoint mode]

/-- The transported bases form an ordinary fixed-label finite kernel family. -/
def toFiniteKernelBasisFamily
    {operator : Real → E →L[Real] E}
    {kernelProjection : ∀ parameter,
      Sector → (operator parameter).ker →L[Real] (operator parameter).ker}
    (data : FiniteSectorPreservingKernelTransportData
      operator kernelProjection)
    (basisZero : Basis ZeroMode Real (operator 0).ker) :
    FiniteKernelBasisFamilyData operator ZeroMode where
  basis := data.transportedBasis basisZero

/-- Ambient vector of the transported kernel family. -/
theorem toFiniteKernelBasisFamily_vector
    {operator : Real → E →L[Real] E}
    {kernelProjection : ∀ parameter,
      Sector → (operator parameter).ker →L[Real] (operator parameter).ker}
    (data : FiniteSectorPreservingKernelTransportData
      operator kernelProjection)
    (basisZero : Basis ZeroMode Real (operator 0).ker)
    (parameter : Real) (mode : ZeroMode) :
    (data.toFiniteKernelBasisFamily basisZero).vector parameter mode =
      (data.transport 0 parameter (basisZero mode)).1 :=
  rfl

/-- The canonical coordinate transport generated by the transported basis maps
all transported basis vectors exactly as the supplied geometric transport does. -/
theorem coordinateTransport_agrees_on_basis
    {operator : Real → E →L[Real] E}
    {kernelProjection : ∀ parameter,
      Sector → (operator parameter).ker →L[Real] (operator parameter).ker}
    (data : FiniteSectorPreservingKernelTransportData
      operator kernelProjection)
    (basisZero : Basis ZeroMode Real (operator 0).ker)
    (first second : Real) (mode : ZeroMode) :
    (data.toFiniteKernelBasisFamily basisZero).kernelTransport first second
        (data.transportedBasis basisZero first mode) =
      data.transport first second
        (data.transportedBasis basisZero first mode) := by
  rw [(data.toFiniteKernelBasisFamily basisZero).kernelTransport_basis]
  rw [transportedBasis_apply, transportedBasis_apply]
  have hTrans := congrArg (fun equivalence => equivalence (basisZero mode))
    (data.transport_trans 0 first second)
  exact hTrans.symm

/-- Differentiability of transported ambient basis vectors upgrades the
algebraic construction to the standard C1 kernel-family packet. -/
def toDifferentiableFiniteKernelBasisFamily
    {operator : Real → E →L[Real] E}
    {kernelProjection : ∀ parameter,
      Sector → (operator parameter).ker →L[Real] (operator parameter).ker}
    (data : FiniteSectorPreservingKernelTransportData
      operator kernelProjection)
    (basisZero : Basis ZeroMode Real (operator 0).ker)
    (hDifferentiable : ∀ mode,
      Differentiable Real
        (fun parameter : Real =>
          (data.transport 0 parameter (basisZero mode)).1)) :
    DifferentiableFiniteKernelBasisFamilyData operator ZeroMode where
  kernels := data.toFiniteKernelBasisFamily basisZero
  vector_differentiable := hDifferentiable

/-- Public sector-preserving actual-kernel transport checkpoint. -/
theorem finite_sector_preserving_kernel_transport_gate
    {operator : Real → E →L[Real] E}
    {kernelProjection : ∀ parameter,
      Sector → (operator parameter).ker →L[Real] (operator parameter).ker}
    (data : FiniteSectorPreservingKernelTransportData
      operator kernelProjection)
    (basisZero : Basis ZeroMode Real (operator 0).ker)
    (sectorOf : ZeroMode → Sector)
    (hBasepoint : ∀ mode,
      kernelProjection 0 (sectorOf mode) (basisZero mode) = basisZero mode) :
    (∀ parameter mode,
      kernelProjection parameter (sectorOf mode)
          (data.transportedBasis basisZero parameter mode) =
        data.transportedBasis basisZero parameter mode) ∧
    (data.transportedBasis basisZero 0 = basisZero) ∧
    (∀ first second mode,
      (data.toFiniteKernelBasisFamily basisZero).kernelTransport first second
          (data.transportedBasis basisZero first mode) =
        data.transport first second
          (data.transportedBasis basisZero first mode)) :=
  ⟨data.transportedBasis_fixed_by_sector basisZero sectorOf hBasepoint,
    data.transportedBasis_zero basisZero,
    data.coordinateTransport_agrees_on_basis basisZero⟩

end FiniteSectorPreservingKernelTransportData

end
end P0EFTJanusProgramPFiniteSectorPreservingKernelTransport4D
end JanusFormal