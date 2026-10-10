import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.Asymptotic
import OAI.RepresentationTheory.UniversalSquare.Support.ExceptionalFourteen
import OAI.RepresentationTheory.UniversalSquare.Support.SmallDegrees
import OAI.RepresentationTheory.UniversalSquare.Finite.NumericalDegree11
import OAI.RepresentationTheory.UniversalSquare.Finite.NumericalDegree12
import OAI.RepresentationTheory.UniversalSquare.Finite.NumericalDegree13
import OAI.RepresentationTheory.UniversalSquare.Finite.NumericalDegree14
import OAI.RepresentationTheory.UniversalSquare.Finite.NumericalDegree16
import OAI.RepresentationTheory.UniversalSquare.Finite.NumericalDegree17
import OAI.RepresentationTheory.UniversalSquare.Finite.NumericalDegree18
import OAI.RepresentationTheory.UniversalSquare.Finite.NumericalDegree19
import OAI.RepresentationTheory.UniversalSquare.Finite.NumericalDegree20
import OAI.RepresentationTheory.UniversalSquare.Finite.NumericalDegree22
import OAI.RepresentationTheory.UniversalSquare.Finite.NumericalDegree23
import OAI.RepresentationTheory.UniversalSquare.Finite.NumericalDegree24
import OAI.RepresentationTheory.UniversalSquare.Finite.NumericalDegree25
import OAI.RepresentationTheory.UniversalSquare.Finite.NumericalDegree26
import OAI.RepresentationTheory.UniversalSquare.Finite.NumericalDegree27
import OAI.RepresentationTheory.UniversalSquare.Finite.NumericalDegree29
import OAI.RepresentationTheory.UniversalSquare.Finite.NumericalDegree30
import OAI.RepresentationTheory.UniversalSquare.Finite.NumericalDegree31
import OAI.RepresentationTheory.UniversalSquare.Finite.NumericalDegree32
import OAI.RepresentationTheory.UniversalSquare.Finite.NumericalDegree33
import OAI.RepresentationTheory.UniversalSquare.Finite.NumericalDegree34
import OAI.RepresentationTheory.UniversalSquare.Finite.NumericalDegree35
import OAI.RepresentationTheory.UniversalSquare.Finite.NumericalDegree37
import OAI.RepresentationTheory.UniversalSquare.Finite.NumericalDegree38
import OAI.RepresentationTheory.UniversalSquare.Finite.NumericalDegree39
import OAI.RepresentationTheory.UniversalSquare.Finite.NumericalDegree40
import OAI.RepresentationTheory.UniversalSquare.Finite.NumericalDegree41
import OAI.RepresentationTheory.UniversalSquare.Finite.NumericalDegree42
import OAI.RepresentationTheory.UniversalSquare.Finite.NumericalDegree43
import OAI.RepresentationTheory.UniversalSquare.Finite.NumericalDegree44
import OAI.RepresentationTheory.UniversalSquare.Finite.NumericalDegree46
import OAI.RepresentationTheory.UniversalSquare.Finite.NumericalDegree47
import OAI.RepresentationTheory.UniversalSquare.Finite.NumericalDegree48
import OAI.RepresentationTheory.UniversalSquare.Finite.NumericalDegree49
import OAI.RepresentationTheory.UniversalSquare.Finite.NumericalDegree50
import OAI.RepresentationTheory.UniversalSquare.Finite.NumericalDegree51
import OAI.RepresentationTheory.UniversalSquare.Finite.NumericalDegree52
import OAI.RepresentationTheory.UniversalSquare.Finite.NumericalDegree53
import OAI.RepresentationTheory.UniversalSquare.Finite.NumericalDegree54
import OAI.RepresentationTheory.UniversalSquare.Finite.NumericalDegree56
import OAI.RepresentationTheory.UniversalSquare.Finite.NumericalDegree57
import OAI.RepresentationTheory.UniversalSquare.Finite.NumericalDegree58
import OAI.RepresentationTheory.UniversalSquare.Finite.NumericalDegree59
import OAI.RepresentationTheory.UniversalSquare.Finite.NumericalDegree60
import OAI.RepresentationTheory.UniversalSquare.Finite.NumericalDegree61
import OAI.RepresentationTheory.UniversalSquare.Finite.NumericalDegree62
import OAI.RepresentationTheory.UniversalSquare.Finite.NumericalDegree63
import OAI.RepresentationTheory.UniversalSquare.Finite.NumericalDegree64
import OAI.RepresentationTheory.UniversalSquare.Finite.NumericalDegree89
import OAI.RepresentationTheory.UniversalSquare.Finite.NumericalDegree112
import OAI.RepresentationTheory.UniversalSquare.Finite.NumericalDegree116
import OAI.RepresentationTheory.UniversalSquare.Finite.NumericalDegree118
import OAI.RepresentationTheory.UniversalSquare.Finite.NumericalDegree151

namespace OAI

/-! Universal tensor squares. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl

lemma universal_partition_le64 (n : ℕ) (hn : 0 < n)
    (h2 : n ≠ 2) (h4 : n ≠ 4) (h9 : n ≠ 9) (hsmall : n ≤ 64) :
    ∃ (lam : YoungDiagram) (hc : lam.card = n),
      ∀ (μ : YoungDiagram) (hμ : μ.card = n),
        0 < kronecker (canonicalTableau lam hc) (canonicalTableau lam hc)
          (canonicalTableau μ hμ) := by
  by_cases hten : n ≤ 10
  · obtain ⟨lam,hc,hpos,_⟩ := universal_tensor_square_le_ten.{0} n hn h2 h4 h9 hten
    exact ⟨lam,hc,hpos⟩
  have hlo : 11 ≤ n := by omega
  interval_cases n
  · exact ⟨_,degreeCard11,degree_pos11⟩
  · exact ⟨_,degreeCard12,degree_pos12⟩
  · exact ⟨_,degreeCard13,degree_pos13⟩
  · exact ⟨_,degreeCard14,degree_pos14⟩
  · exact ⟨staircase 5,staircase_card 5,saxl_kronecker_pos 5 (by decide)⟩
  · exact ⟨_,degreeCard16,degree_pos16⟩
  · exact ⟨_,degreeCard17,degree_pos17⟩
  · exact ⟨_,degreeCard18,degree_pos18⟩
  · exact ⟨_,degreeCard19,degree_pos19⟩
  · exact ⟨_,degreeCard20,degree_pos20⟩
  · exact ⟨staircase 6,staircase_card 6,saxl_kronecker_pos 6 (by decide)⟩
  · exact ⟨_,degreeCard22,degree_pos22⟩
  · exact ⟨_,degreeCard23,degree_pos23⟩
  · exact ⟨_,degreeCard24,degree_pos24⟩
  · exact ⟨_,degreeCard25,degree_pos25⟩
  · exact ⟨_,degreeCard26,degree_pos26⟩
  · exact ⟨_,degreeCard27,degree_pos27⟩
  · exact ⟨staircase 7,staircase_card 7,saxl_kronecker_pos 7 (by decide)⟩
  · exact ⟨_,degreeCard29,degree_pos29⟩
  · exact ⟨_,degreeCard30,degree_pos30⟩
  · exact ⟨_,degreeCard31,degree_pos31⟩
  · exact ⟨_,degreeCard32,degree_pos32⟩
  · exact ⟨_,degreeCard33,degree_pos33⟩
  · exact ⟨_,degreeCard34,degree_pos34⟩
  · exact ⟨_,degreeCard35,degree_pos35⟩
  · exact ⟨staircase 8,staircase_card 8,saxl_kronecker_pos 8 (by decide)⟩
  · exact ⟨_,degreeCard37,degree_pos37⟩
  · exact ⟨_,degreeCard38,degree_pos38⟩
  · exact ⟨_,degreeCard39,degree_pos39⟩
  · exact ⟨_,degreeCard40,degree_pos40⟩
  · exact ⟨_,degreeCard41,degree_pos41⟩
  · exact ⟨_,degreeCard42,degree_pos42⟩
  · exact ⟨_,degreeCard43,degree_pos43⟩
  · exact ⟨_,degreeCard44,degree_pos44⟩
  · exact ⟨staircase 9,staircase_card 9,saxl_kronecker_pos 9 (by decide)⟩
  · exact ⟨_,degreeCard46,degree_pos46⟩
  · exact ⟨_,degreeCard47,degree_pos47⟩
  · exact ⟨_,degreeCard48,degree_pos48⟩
  · exact ⟨_,degreeCard49,degree_pos49⟩
  · exact ⟨_,degreeCard50,degree_pos50⟩
  · exact ⟨_,degreeCard51,degree_pos51⟩
  · exact ⟨_,degreeCard52,degree_pos52⟩
  · exact ⟨_,degreeCard53,degree_pos53⟩
  · exact ⟨_,degreeCard54,degree_pos54⟩
  · exact ⟨staircase 10,staircase_card 10,saxl_kronecker_pos 10 (by decide)⟩
  · exact ⟨_,degreeCard56,degree_pos56⟩
  · exact ⟨_,degreeCard57,degree_pos57⟩
  · exact ⟨_,degreeCard58,degree_pos58⟩
  · exact ⟨_,degreeCard59,degree_pos59⟩
  · exact ⟨_,degreeCard60,degree_pos60⟩
  · exact ⟨_,degreeCard61,degree_pos61⟩
  · exact ⟨_,degreeCard62,degree_pos62⟩
  · exact ⟨_,degreeCard63,degree_pos63⟩
  · exact ⟨_,degreeCard64,degree_pos64⟩

lemma universal_partition_exceptional (n : ℕ)
    (hexc : exceptionalPair (staircaseIndex n) (remainderPairs n)) :
    ∃ (lam : YoungDiagram) (hc : lam.card = n),
      ∀ (μ : YoungDiagram) (hμ : μ.card = n),
        0 < kronecker (canonicalTableau lam hc) (canonicalTableau lam hc)
          (canonicalTableau μ hμ) := by
  have he := degree_eq n
  rw [staircase_card] at he
  have hcases : n = 71 ∨ n = 73 ∨ n = 75 ∨ n = 77 ∨ n = 79 ∨ n = 81 ∨ n = 83 ∨ n = 85 ∨ n = 87 ∨ n = 89 ∨ n = 106 ∨ n = 108 ∨ n = 110 ∨ n = 112 ∨ n = 114 ∨ n = 116 ∨ n = 118 ∨ n = 149 ∨ n = 151 := by
    unfold exceptionalPair at hexc
    rcases hexc with ⟨hM,hr⟩ | ⟨hM,hr⟩ | ⟨hM,hr⟩ <;>
      rw [hM] at he <;> norm_num at he <;> omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_,exceptionalCard71,exceptional_pos71⟩
  · exact ⟨_,exceptionalCard73,exceptional_pos73⟩
  · exact ⟨_,exceptionalCard75,exceptional_pos75⟩
  · exact ⟨_,exceptionalCard77,exceptional_pos77⟩
  · exact ⟨_,exceptionalCard79,exceptional_pos79⟩
  · exact ⟨_,exceptionalCard81,exceptional_pos81⟩
  · exact ⟨_,exceptionalCard83,exceptional_pos83⟩
  · exact ⟨_,exceptionalCard85,exceptional_pos85⟩
  · exact ⟨_,exceptionalCard87,exceptional_pos87⟩
  · exact ⟨_,degreeCard89,degree_pos89⟩
  · exact ⟨_,exceptionalCard106,exceptional_pos106⟩
  · exact ⟨_,exceptionalCard108,exceptional_pos108⟩
  · exact ⟨_,exceptionalCard110,exceptional_pos110⟩
  · exact ⟨_,degreeCard112,degree_pos112⟩
  · exact ⟨_,exceptionalCard114,exceptional_pos114⟩
  · exact ⟨_,degreeCard116,degree_pos116⟩
  · exact ⟨_,degreeCard118,degree_pos118⟩
  · exact ⟨_,exceptionalCard149,exceptional_pos149⟩
  · exact ⟨_,degreeCard151,degree_pos151⟩

universe u

theorem universal_tensor_square
    (n : ℕ) (hn : 0 < n) (h2 : n ≠ 2) (h4 : n ≠ 4) (h9 : n ≠ 9) :
    ∃ (lam : YoungDiagram) (hlam : lam.card = n),
      (∀ (ν : YoungDiagram) (hν : ν.card = n),
        0 < Saxl.kronecker (Saxl.canonicalTableau lam hlam)
          (Saxl.canonicalTableau lam hlam) (Saxl.canonicalTableau ν hν)) ∧
      Representation.IsIrreducible (Saxl.spechtRep (Saxl.canonicalTableau lam hlam)) ∧
      ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
        (ρ : Representation ℂ (Equiv.Perm (Fin n)) V) [Representation.IsIrreducible ρ],
        ∃ F : Representation.IntertwiningMap ρ
          ((Saxl.spechtRep (Saxl.canonicalTableau lam hlam)).tprod
            (Saxl.spechtRep (Saxl.canonicalTableau lam hlam))),
          Function.Injective F := by
  have hex : ∃ (lam : YoungDiagram) (hc : lam.card = n),
      ∀ (μ : YoungDiagram) (hμ : μ.card = n),
        0 < kronecker (canonicalTableau lam hc) (canonicalTableau lam hc)
          (canonicalTableau μ hμ) := by
    by_cases hsmall : n ≤ 64
    · exact universal_partition_le64 n hn h2 h4 h9 hsmall
    · have hlarge : 64 < n := by omega
      by_cases hexc : exceptionalPair (staircaseIndex n) (remainderPairs n)
      · exact universal_partition_exceptional n hexc
      · have hM := (fixedCandidate_large_degree n hlarge).1
        exact ⟨fixedCandidate n,fixedCandidate_card n (by omega),
          fixedCandidate_nonexceptional_pos n hlarge hexc⟩
  obtain ⟨lam,hc,hpos⟩ := hex
  exact ⟨lam,hc,hpos,irreducibles_of_kronecker_pos lam hc hpos⟩

end UniversalTensorSquare
end
end

namespace UniversalTensorSquares
universe u
theorem universal_tensor_square
    (n : ℕ) (hn : 0 < n) (h2 : n ≠ 2) (h4 : n ≠ 4) (h9 : n ≠ 9) :
    ∃ (lam : YoungDiagram) (hlam : lam.card = n),
      (∀ (ν : YoungDiagram) (hν : ν.card = n),
        0 < Saxl.kronecker (Saxl.canonicalTableau lam hlam)
          (Saxl.canonicalTableau lam hlam) (Saxl.canonicalTableau ν hν)) ∧
      Representation.IsIrreducible (Saxl.spechtRep (Saxl.canonicalTableau lam hlam)) ∧
      ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
        (ρ : Representation ℂ (Equiv.Perm (Fin n)) V) [Representation.IsIrreducible ρ],
        ∃ F : Representation.IntertwiningMap ρ
          ((Saxl.spechtRep (Saxl.canonicalTableau lam hlam)).tprod
            (Saxl.spechtRep (Saxl.canonicalTableau lam hlam))),
          Function.Injective F := by
  exact UniversalTensorSquare.universal_tensor_square n hn h2 h4 h9
end UniversalTensorSquares

end OAI
