import Mathlib
import OAI.Topology.ArtinGroups.Coxeter.ReducedWordProperty
import OAI.Topology.ArtinGroups.Complexes.PacketPermEnumeration
import OAI.Topology.ArtinGroups.Coxeter.AltListMap
import OAI.Topology.ArtinGroups.Coxeter.OrdinaryTwistBraid
import OAI.Topology.ArtinGroups.Complexes.HighestLocalGeneratorTest

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u v
open CoxeterExchange

attribute [local instance] Classical.decEq Classical.propDecidable
variable {V A : Type u} {K : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  (hn : ∀ a,Q.source a≠Q.target a)

lemma inverseWordAction_append (w v : List V) (x : FiniteHomotopyClass Q (K:=K)) :
    inverseWordAction Q (w++v) x=inverseWordAction Q v (inverseWordAction Q w x) := by
  induction w generalizing x with
  | nil => rfl
  | cons α w ih => exact ih (classNegativeTwist Q α x)

include hn in
lemma inverseWordAction_eq_of_positive (w v : List V)
    (h : ∀ x : FiniteHomotopyClass Q (K:=K),positiveWordAction Q w x=positiveWordAction Q v x)
    (x : FiniteHomotopyClass Q (K:=K)) :
    inverseWordAction Q w x=inverseWordAction Q v x := by
  calc
    inverseWordAction Q w x=
        inverseWordAction Q w (positiveWordAction Q v (inverseWordAction Q v x)) := by
      rw [positive_inverseWord Q hn]
    _=inverseWordAction Q w (positiveWordAction Q w (inverseWordAction Q v x)) := by rw [h]
    _=inverseWordAction Q v x := inverse_positiveWord Q hn w _

variable {T : Type v} [Fintype T] [DecidableEq T] (C : CoxeterMatrix T) (ι : T → V)
  (hmat : ∀ α β,ordinaryCoxeterMatrix Q (ι α) (ι β)=C α β)

include hn hmat

lemma mapped_inverseWord_property (w v : List T)
    (hw : C.toCoxeterSystem.IsReduced w) (hv : C.toCoxeterSystem.IsReduced v)
    (he : C.toCoxeterSystem.wordProd w=C.toCoxeterSystem.wordProd v)
    (x : FiniteHomotopyClass Q (K:=K)) :
    inverseWordAction Q (w.map ι) x=inverseWordAction Q (v.map ι) x := by
  apply inverseWordAction_eq_of_positive Q hn
  intro y
  have hb : ∀ α β,((altList α β (C α β)).map (fun α=>classTwistPerm Q (K:=K) hn (ι α))).prod=
      ((altList β α (C α β)).map (fun α=>classTwistPerm Q (K:=K) hn (ι α))).prod := by
    intro α β
    have hh:=ordinaryTwist_braid Q (K:=K) hn (ι α) (ι β)
    rw [hmat] at hh
    simpa only [← altList_map,List.map_map,Function.comp_def] using hh
  have hh:=reduced_word_property C.toCoxeterSystem (fun α=>classTwistPerm Q (K:=K) hn (ι α))
    hb w v hw hv he
  rw [positiveWordAction_eq_prod Q hn,positiveWordAction_eq_prod Q hn]
  simpa only [List.map_map,Function.comp_def] using
    congrArg (fun f : Equiv.Perm (FiniteHomotopyClass Q (K:=K))=>f y) hh

theorem longest_inverseWord_testUpper (w : List T)
    (hw : C.toCoxeterSystem.IsReduced w)
    (hd : ∀ α,C.toCoxeterSystem.length (C.toCoxeterSystem.wordProd w*C.toCoxeterSystem.simple α)+1=
      C.toCoxeterSystem.length (C.toCoxeterSystem.wordProd w))
    (x : FiniteHomotopyClass Q (K:=K)) (t : ℤ)
    (hx : ClassTestUpper Q x (Set.range ι) t) :
    ClassTestUpper Q (inverseWordAction Q (w.map ι) x) (Set.range ι) (t-1) := by
  rintro _ ⟨α,rfl⟩ l hl c
  let cs:=C.toCoxeterSystem
  obtain ⟨v,hv,he⟩:=cs.exists_isReduced (cs.wordProd w*cs.simple α)
  have hprod : cs.wordProd (v++[α])=cs.wordProd w := by
    rw [cs.wordProd_append,cs.wordProd_singleton,← he,_root_.mul_assoc,cs.simple_mul_simple_self,_root_.mul_one]
  have hvr : cs.IsReduced (v++[α]) := by
    change cs.length (cs.wordProd (v++[α]))=(v++[α]).length
    rw [hprod,List.length_append,List.length_singleton,← hv.eq,← he]
    exact (hd α).symm
  rw [mapped_inverseWord_property Q hn C ι hmat w (v++[α]) hw hvr hprod.symm,
    List.map_append,inverseWordAction_append]
  change ClassTestExact Q (ι α) l c
    (classNegativeTwist Q (ι α) (inverseWordAction Q (v.map ι) x))
  apply (classTestExact_negative_self Q hn _ (ι α) l c).mpr
  apply inverseWord_testUpper Q hn (v.map ι) x (Set.range ι) hx
    (fun β hβ=>by obtain ⟨γ,_,rfl⟩:=List.mem_map.mp hβ; exact ⟨γ,rfl⟩)
    (ι α) ⟨α,rfl⟩ (l+1) (by omega) (c-1)

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
