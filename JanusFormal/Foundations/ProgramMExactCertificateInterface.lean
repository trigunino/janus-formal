import JanusFormal.Foundations.ProgramMInducedPatternHierarchy

/-!
# MF-CERT-002: exact-certificate dependency interface

This file records the premises of an exact identification theorem.  In
particular, finite statistical acceptance is not one of these premises.
-/

namespace JanusFormal.ProgramM

/-- The unformalized representation and forcing results are passed explicitly
as a bridge; they are not installed as axioms of Program M. -/
structure ExactMinkowskiBridge (Law : Type*) where
  globalTwoOrderRepresentation : Law → Prop
  exchangeableRandomRealizerLift : Law → Prop
  continuousPermutonRepresentation : Law → Prop
  exactRankFourMatch : Law → Prop
  uniformMinkowskiLaw : Law → Prop
  forceUniform : ∀ law,
    globalTwoOrderRepresentation law →
    exchangeableRandomRealizerLift law →
    continuousPermutonRepresentation law →
    exactRankFourMatch law →
    uniformMinkowskiLaw law

theorem exactMinkowski_of_explicit_premises
    {Law : Type*} (bridge : ExactMinkowskiBridge Law) (law : Law)
    (hGlobal : bridge.globalTwoOrderRepresentation law)
    (hLift : bridge.exchangeableRandomRealizerLift law)
    (hContinuous : bridge.continuousPermutonRepresentation law)
    (hRankFour : bridge.exactRankFourMatch law) :
    bridge.uniformMinkowskiLaw law :=
  bridge.forceUniform law hGlobal hLift hContinuous hRankFour

/-- A finite pass is deliberately only data; no theorem turns it into any of
the exact premises above. -/
structure FiniteCertificateObservation where
  reconstructionSamplePassed : Bool
  rankFourSamplePassed : Bool
  sampleSize : Nat

end JanusFormal.ProgramM
