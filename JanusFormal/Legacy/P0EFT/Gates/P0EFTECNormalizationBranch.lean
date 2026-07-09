import JanusFormal.Legacy.P0EFT.Gates.P0EFTCTorsionContractionCheck

namespace JanusFormal
namespace P0EFTECNormalizationBranch

set_option autoImplicit false

structure ECNormalizationBranch where
  noHolstStandardECAction : Prop
  torsionScalarDecompositionSelected : Prop
  cECEqualsTwentyThreeOverSix : Prop
  alphaIsoReadyInBranch : Prop
  noExtraTorsionTerms : Prop

def cECClosedForStandardBranch (e : ECNormalizationBranch) : Prop :=
  e.noHolstStandardECAction /\
  e.torsionScalarDecompositionSelected /\
  e.cECEqualsTwentyThreeOverSix /\
  e.alphaIsoReadyInBranch /\
  e.noExtraTorsionTerms

theorem standard_no_holst_branch_fixes_cEC
    (e : ECNormalizationBranch)
    (hEC : e.noHolstStandardECAction)
    (hDecomp : e.torsionScalarDecompositionSelected)
    (hC : e.cECEqualsTwentyThreeOverSix)
    (hAlpha : e.alphaIsoReadyInBranch)
    (hNoExtra : e.noExtraTorsionTerms) :
    cECClosedForStandardBranch e := by
  exact And.intro hEC
    (And.intro hDecomp
      (And.intro hC
        (And.intro hAlpha hNoExtra)))

theorem holst_or_extra_torsion_terms_block_this_branch
    (e : ECNormalizationBranch)
    (hMissing : Not e.noExtraTorsionTerms) :
    Not (cECClosedForStandardBranch e) := by
  intro h
  exact hMissing h.right.right.right.right

end P0EFTECNormalizationBranch
end JanusFormal
