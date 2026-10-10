import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupTensor

namespace OAI

/-! Kronecker Semigroup. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl
open Columns FlagColumns

lemma tableau_card_eq {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) : μ.card = n := by
  have h := Fintype.card_congr t
  simpa only [Fintype.card_fin,Fintype.card_coe,YoungDiagram.card] using h.symm

lemma columnTableau_sum {n : ℕ} {rs : List ℕ} (t : Tableau n (columnShape rs)) :
    rs.sum = n := (columnShape_card rs).symm.trans (tableau_card_eq t)

lemma columnShape_height_sum (rs : List ℕ) : (columnShape rs).colLen 0 ≤ rs.sum :=
  columnShape_height rs rs.sum (fun a ha => List.single_le_sum (fun x _ => Nat.zero_le x) a ha)

theorem kronecker_pos_append {n m : ℕ} {ra rb rt sa sb st : List ℕ}
    (a : Tableau n (columnShape ra)) (b : Tableau n (columnShape rb))
    (t : Tableau n (columnShape rt))
    (c : Tableau m (columnShape sa)) (d : Tableau m (columnShape sb))
    (u : Tableau m (columnShape st))
    (A : Tableau (n+m) (columnShape (ra++sa)))
    (B : Tableau (n+m) (columnShape (rb++sb)))
    (T : Tableau (n+m) (columnShape (rt++st)))
    (h : 0 < kronecker a b t) (h' : 0 < kronecker c d u) :
    0 < kronecker A B T := by
  have ha : (columnShape ra).colLen 0 ≤ n+m := by
    have := columnShape_height_sum ra
    rw [columnTableau_sum a] at this
    omega
  have hb : (columnShape rb).colLen 0 ≤ n+m := by
    have := columnShape_height_sum rb
    rw [columnTableau_sum b] at this
    omega
  have ht : (columnShape rt).colLen 0 ≤ n+m := by
    have := columnShape_height_sum rt
    rw [columnTableau_sum t] at this
    omega
  have hc : (columnShape sa).colLen 0 ≤ n+m := by
    have := columnShape_height_sum sa
    rw [columnTableau_sum c] at this
    omega
  have hd : (columnShape sb).colLen 0 ≤ n+m := by
    have := columnShape_height_sum sb
    rw [columnTableau_sum d] at this
    omega
  have hu : (columnShape st).colLen 0 ≤ n+m := by
    have := columnShape_height_sum st
    rw [columnTableau_sum u] at this
    omega
  obtain ⟨ea,eb,et,L,hL⟩ := nonzero_positioned_of_kronecker_pos a b t ha hb ht h
  obtain ⟨ec,ed,eu,M,hM⟩ := nonzero_positioned_of_kronecker_pos c d u hc hd hu h'
  obtain ⟨P,hP,hP'⟩ := wordMap_common_two _ _ _ _ ⟨L,hL⟩ ⟨M,hM⟩
  obtain ⟨eA,heA⟩ := positioned_append ra sa ea ec (standard (n+m))
  obtain ⟨eB,heB⟩ := positioned_append rb sb eb ed (standard (n+m))
  obtain ⟨eT,heT⟩ := positioned_append rt st et eu (standard (n+m))
  apply kronecker_pos_of_positioned A B T eA eB eT
    (by simpa [List.sum_append,columnTableau_sum a,columnTableau_sum c] using
      columnShape_height_sum (ra++sa))
    (by simpa [List.sum_append,columnTableau_sum b,columnTableau_sum d] using
      columnShape_height_sum (rb++sb))
    (by simpa [List.sum_append,columnTableau_sum t,columnTableau_sum u] using
      columnShape_height_sum (rt++st)) P
  rw [heA,heB,heT,wordTensor_positionProduct,wordMap_positionProduct,positionProduct_pair]
  exact mul_ne_zero hP hP'

end Saxl
end
end

end OAI
