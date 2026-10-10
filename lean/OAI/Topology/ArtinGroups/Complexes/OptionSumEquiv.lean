import Mathlib
import OAI.Topology.ArtinGroups.Complexes.PacketPermReindex

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
open Zigzag

universe u
attribute [local instance] Classical.decEq
variable {V A : Type u} {K : Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  (hn:∀ a,Q.source a≠Q.target a)

omit [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A] in
lemma packet_orthogonal_inl {J L:Type u} (v:J ⊕ L → V)
    (hv:Pairwise fun a b => OrthogonalVertices Q (v a) (v b)) :
    Pairwise fun a b => OrthogonalVertices Q ((v ∘ Sum.inl) a) ((v ∘ Sum.inl) b) :=
  fun _ _ h=>hv (fun hh=>h (Sum.inl.inj hh))

omit [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A] in
lemma packet_orthogonal_inr {J L:Type u} (v:J ⊕ L → V)
    (hv:Pairwise fun a b => OrthogonalVertices Q (v a) (v b)) :
    Pairwise fun a b => OrthogonalVertices Q ((v ∘ Sum.inr) a) ((v ∘ Sum.inr) b) :=
  fun _ _ h=>hv (fun hh=>h (Sum.inr.inj hh))

omit [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A] in
lemma packet_orthogonal_fiber {J L:Type u} (v:J × L → V)
    (hv:Pairwise fun a b => OrthogonalVertices Q (v a) (v b)) (j:J) :
    Pairwise fun a b => OrthogonalVertices Q (v (j,a)) (v (j,b)) :=
  fun _ _ h=>hv (fun hh=>h (congrArg Prod.snd hh))

def optionSumEquiv (J L:Type u) : Option (J ⊕ L) ≃ Option J ⊕ L where
  toFun z := z.elim (.inl none) (fun x => x.elim (fun j=>.inl (some j)) Sum.inr)
  invFun z := z.elim (fun j => j.elim none (fun j=>some (.inl j))) (fun l=>some (.inr l))
  left_inv z := by cases z with | none => rfl | some z => cases z <;> rfl
  right_inv z := by cases z with | inl z => cases z <;> rfl | inr z => rfl

lemma classPacketPerm_sumIndex {J L:Type u} [Fintype J] [Fintype L] (v:J ⊕ L → V)
    (hv:Pairwise fun a b => OrthogonalVertices Q (v a) (v b)) :
    classPacketPerm Q (K:=K) hn v hv =
      classPacketPerm Q hn (v ∘ Sum.inl) (packet_orthogonal_inl Q v hv) *
      classPacketPerm Q hn (v ∘ Sum.inr) (packet_orthogonal_inr Q v hv) := by
  suffices hh : ∀ (J:Type u) [Fintype J] (v:J ⊕ L → V)
    (hv:Pairwise fun a b => OrthogonalVertices Q (v a) (v b)),
    classPacketPerm Q (K:=K) hn v hv =
      classPacketPerm Q hn (v ∘ Sum.inl) (packet_orthogonal_inl Q v hv) *
      classPacketPerm Q hn (v ∘ Sum.inr) (packet_orthogonal_inr Q v hv) from hh J v hv
  intro J inst
  apply Fintype.induction_empty_option (P:=fun J _ => ∀ (v:J ⊕ L → V)
    (hv:Pairwise fun a b => OrthogonalVertices Q (v a) (v b)),
    classPacketPerm Q (K:=K) hn v hv =
      classPacketPerm Q hn (v ∘ Sum.inl) (packet_orthogonal_inl Q v hv) *
      classPacketPerm Q hn (v ∘ Sum.inr) (packet_orthogonal_inr Q v hv)) _ _ _ J
  · intro J J' instJ' e ih
    let := Fintype.ofEquiv J' e.symm
    intro v hv
    erw [classPacketPerm_reindex Q hn v hv (Equiv.sumCongr e (Equiv.refl L)),
      classPacketPerm_reindex Q hn (v ∘ Sum.inl) _ e]
    exact ih _ _
  · intro v hv
    erw [classPacketPerm_empty Q hn (v ∘ Sum.inl),show (Equiv.refl _ : Equiv.Perm (FiniteHomotopyClass Q (K:=K))) = 1 from rfl,_root_.one_mul]
    let e : L ≃ PEmpty ⊕ L :=
      { toFun:=Sum.inr
        invFun:=fun x=>x.elim PEmpty.elim id
        left_inv:=fun _=>rfl
        right_inv:=by intro x; cases x with | inl x=>exact x.elim | inr x=>rfl }
    exact classPacketPerm_reindex Q hn v hv e
  · intro J instJ ih v hv
    erw [classPacketPerm_reindex Q hn v hv (optionSumEquiv J L),classPacketPerm_cons Q hn (v ∘ (optionSumEquiv J L)),
      classPacketPerm_cons Q hn (v ∘ Sum.inl),_root_.mul_assoc]
    apply congrArg (fun p => classTwistPerm Q (K:=K) hn (v (.inl none)) * p)
    exact ih _ _

def optionProdEquiv (J L:Type u) : L ⊕ (J × L) ≃ Option J × L where
  toFun z := z.elim (fun l=>(none,l)) (fun p=>(some p.1,p.2))
  invFun z := z.1.elim (.inl z.2) (fun j=>.inr (j,z.2))
  left_inv z := by cases z <;> rfl
  right_inv z := by rcases z with ⟨j,l⟩; cases j <;> rfl

lemma exists_packetGroupWord {J L:Type u} [Fintype J] [Fintype L] (v:J × L → V)
    (hv:Pairwise fun a b => OrthogonalVertices Q (v a) (v b)) :
    ∃ w:List J, classPacketPerm Q (K:=K) hn v hv =
      (w.map fun j=>classPacketPerm Q hn (fun l=>v (j,l))
        (packet_orthogonal_fiber Q v hv j)).prod := by
  suffices hh : ∀ (J:Type u) [Fintype J] (v:J × L → V)
    (hv:Pairwise fun a b => OrthogonalVertices Q (v a) (v b)),
    ∃ w:List J, classPacketPerm Q (K:=K) hn v hv =
      (w.map fun j=>classPacketPerm Q hn (fun l=>v (j,l))
        (packet_orthogonal_fiber Q v hv j)).prod from hh J v hv
  intro J inst
  apply Fintype.induction_empty_option (P:=fun J _ => ∀ (v:J × L → V)
    (hv:Pairwise fun a b => OrthogonalVertices Q (v a) (v b)),
    ∃ w:List J, classPacketPerm Q (K:=K) hn v hv =
      (w.map fun j=>classPacketPerm Q hn (fun l=>v (j,l))
        (packet_orthogonal_fiber Q v hv j)).prod) _ _ _ J
  · intro J J' instJ' e ih
    let := Fintype.ofEquiv J' e.symm
    intro v hv
    erw [classPacketPerm_reindex Q hn v hv (Equiv.prodCongr e (Equiv.refl L))]
    obtain ⟨w,hw⟩ := ih _ _
    refine ⟨w.map e,hw.trans ?_⟩
    simp only [List.map_map]
    apply congrArg List.prod
    apply List.map_congr_left
    intro j hj
    rfl
  · intro v hv
    refine ⟨[],?_⟩
    erw [classPacketPerm_empty Q hn v hv]
    rfl
  · intro J instJ ih v hv
    erw [classPacketPerm_reindex Q hn v hv (optionProdEquiv J L),classPacketPerm_sumIndex Q hn (v ∘ (optionProdEquiv J L))]
    obtain ⟨w,hw⟩ := ih (fun p=>v (some p.1,p.2))
      (by
        intro a b hab
        apply hv
        intro hh
        simp only [Prod.mk.injEq,Option.some.injEq] at hh
        exact hab (Prod.ext hh.1 hh.2))
    refine ⟨none::w.map some,?_⟩
    simp only [List.map_cons,List.prod_cons,List.map_map]
    exact congrArg (fun p=>classPacketPerm Q hn (fun l=>v (none,l)) _ * p) hw

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
