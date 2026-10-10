import Mathlib
import OAI.Topology.ArtinGroups.Realizations.CellDeligne

namespace OAI

namespace HarmonicArtin
universe u
variable {S:Type u} (M:CoxeterMatrix S)

instance liftedPartialOrder : PartialOrder (LiftedCell M) where
  toPreorder:=inferInstance
  le_antisymm:=fun _ _=>lifted_le_antisymm M

lemma lifted_eq_of_le_type_eq {a b:LiftedCell M} (h:a≤b) (ht:a.2.val=b.2.val) : a=b := by
  obtain ⟨hab,w,hw,hred,hmin,he⟩:=(lifted_le_iff_face M a b).mp h
  have hmem:wordCoxeter M w∈coxeterParabolic M a.2.val:=by
    rw [ht];exact wordCoxeter_mem_parabolic M b.2.val w hw
  have hl:=hmin ⟨(wordCoxeter M w)⁻¹,(coxeterParabolic M a.2.val).inv_mem hmem⟩
  simp only [mul_inv_cancel,M.toCoxeterSystem.length_one] at hl
  have hn:w=[]:=List.eq_nil_of_length_eq_zero (by omega)
  rw [hn] at he
  simp only [wordArtin,List.map_nil,List.prod_nil,mul_one] at he
  exact Prod.ext he (Subtype.ext ht)

lemma lifted_lt_type {a b:LiftedCell M} (h:a<b) : a.2.val⊂b.2.val :=
  lt_of_le_of_ne ((lifted_le_iff_face M a b).mp h.le).1
    (fun ht=>h.ne (lifted_eq_of_le_type_eq M h.le ht))

lemma lifted_rank_bound [Finite S] (a:LiftedCell M) : a.2.val.ncard≤Nat.card S :=
  Set.ncard_le_card _

lemma lifted_rank_strict [Finite S] : StrictMono (fun a:LiftedCell M=>a.2.val.ncard) := by
  intro a b h
  exact Set.ncard_lt_ncard (lifted_lt_type M h) (Set.toFinite _)

lemma liftedFace_deck_iff (g:Artin M) (a b:LiftedCell M) :
    LiftedFace M (g*a.1,a.2) (g*b.1,b.2) ↔ LiftedFace M a b := by
  constructor
  · rintro ⟨ht,w,hw,hr,hm,he⟩
    refine ⟨ht,w,hw,hr,hm,?_⟩
    apply mul_left_cancel (a:=g)
    simpa only [mul_assoc] using he
  · rintro ⟨ht,w,hw,hr,hm,he⟩
    exact ⟨ht,w,hw,hr,hm,by dsimp;rw [he,mul_assoc]⟩

def liftedDeck (g:Artin M) : LiftedCell M≃oLiftedCell M where
  toFun a:=(g*a.1,a.2)
  invFun a:=(g⁻¹*a.1,a.2)
  left_inv:=by intro a;ext <;> simp
  right_inv:=by intro a;ext <;> simp
  map_rel_iff':=by
    intro a b
    rw [lifted_le_iff_face,lifted_le_iff_face]
    exact liftedFace_deck_iff M g a b

def SphericalLiftedFiber (T:Set S) :=
  {a:LiftedCell M // a.2.val⊆T ∧ a.1∈artinParabolic M T}

instance (T:Set S) : PartialOrder (SphericalLiftedFiber M T) :=
  inferInstanceAs (PartialOrder {a:LiftedCell M // a.2.val⊆T ∧ a.1∈artinParabolic M T})

end HarmonicArtin

end OAI
