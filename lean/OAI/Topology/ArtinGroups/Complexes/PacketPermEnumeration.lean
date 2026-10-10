import Mathlib
import OAI.Topology.ArtinGroups.Complexes.PacketPermReindex
import OAI.Topology.ArtinGroups.Coxeter.PositiveBraidRel

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V A : Type u} {K : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  (hn : ∀ a,Q.source a≠Q.target a)

lemma classPacketPerm_enumeration {J : Type u} [Fintype J] (v : J → V)
    (hv : Pairwise fun a b => OrthogonalVertices Q (v a) (v b)) :
    ∃ l : List J, l.Nodup ∧ (∀ j,j∈l) ∧
      (l.map fun j => classTwistPerm Q (K:=K) hn (v j)).prod=classPacketPerm Q hn v hv := by
  suffices hh : ∀ (J : Type u) [Fintype J] (v : J → V)
    (hv : Pairwise fun a b => OrthogonalVertices Q (v a) (v b)),
    ∃ l : List J, l.Nodup ∧ (∀ j,j∈l) ∧
      (l.map fun j => classTwistPerm Q (K:=K) hn (v j)).prod=classPacketPerm Q hn v hv from hh J v hv
  intro J inst
  apply Fintype.induction_empty_option (P:=fun J _ => ∀ (v : J → V)
    (hv : Pairwise fun a b => OrthogonalVertices Q (v a) (v b)),
    ∃ l : List J, l.Nodup ∧ (∀ j,j∈l) ∧
      (l.map fun j => classTwistPerm Q (K:=K) hn (v j)).prod=classPacketPerm Q hn v hv) _ _ _ J
  · intro J L instL e ih
    let := Fintype.ofEquiv L e.symm
    intro v hv
    obtain ⟨l,hl,ha,he⟩ := ih (v∘e) (fun a b hab => hv (fun h => hab (e.injective h)))
    refine ⟨l.map e,hl.map e.injective,?_,?_⟩
    · intro j
      exact List.mem_map.mpr ⟨e.symm j,ha _,e.apply_symm_apply j⟩
    · rw [classPacketPerm_reindex Q hn v hv e]
      simpa only [List.map_map,Function.comp_def] using he
  · intro v hv
    refine ⟨[],List.nodup_nil,fun j => isEmptyElim j,?_⟩
    rw [List.map_nil,List.prod_nil,classPacketPerm_empty]
    rfl
  · intro J inst ih v hv
    obtain ⟨l,hl,ha,he⟩ := ih (v∘some) (fun a b hab => hv (fun h => hab (Option.some.inj h)))
    refine ⟨none::l.map some,?_,?_,?_⟩
    · simp only [List.nodup_cons,List.mem_map,Option.some_ne_none,and_false,exists_false,not_false_eq_true,
        true_and]
      exact hl.map (Option.some_injective _)
    · intro j
      cases j with
      | none => exact List.mem_cons_self
      | some j => exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨j,ha j,rfl⟩)
    · rw [List.map_cons,List.prod_cons,List.map_map,classPacketPerm_cons,← he]
      rfl

lemma classPacketPerm_toList {J : Type u} [Fintype J] (v : J → V)
    (hv : Pairwise fun a b => OrthogonalVertices Q (v a) (v b)) :
    ((Finset.univ : Finset J).toList.map fun j => classTwistPerm Q (K:=K) hn (v j)).prod=
      classPacketPerm Q hn v hv := by
  obtain ⟨l,hl,ha,he⟩ := classPacketPerm_enumeration Q (K:=K) hn v hv
  have hp : (Finset.univ : Finset J).toList.Perm l :=
    (List.perm_ext_iff_of_nodup (Finset.nodup_toList _) hl).mpr (fun j => by simp [ha])
  rw [← he]
  apply (hp.map _).prod_eq'
  rw [List.pairwise_map]
  apply (Finset.nodup_toList (Finset.univ : Finset J)).imp
  intro a b hab
  exact classTwistPerm_orthogonal Q hn (hv hab)

lemma positiveWordAction_eq_prod (w : List V) (x : FiniteHomotopyClass Q (K:=K)) :
    positiveWordAction Q w x=(w.map (classTwistPerm Q hn)).prod x := by
  induction w with
  | nil => rfl
  | cons a w ih => exact congrArg (classPositiveTwist Q a) ih

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
