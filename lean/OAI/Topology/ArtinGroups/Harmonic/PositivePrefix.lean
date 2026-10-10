import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.PositiveSimpleLiftMul
import OAI.Topology.ArtinGroups.Coxeter.CommonWeakPrefixMaximal

namespace OAI

namespace HarmonicArtin
open CoxeterExchange

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type*} (M:CoxeterMatrix S)

def PositivePrefix (a b:PositiveArtin M) : Prop := ∃c:PositiveArtin M,b=a*c

lemma positivePrefix_refl (a:PositiveArtin M) : PositivePrefix M a a :=⟨1,(mul_one a).symm⟩
lemma positivePrefix_one (a:PositiveArtin M) : PositivePrefix M 1 a :=⟨a,(one_mul a).symm⟩
lemma positivePrefix_trans {a b c:PositiveArtin M} (hab:PositivePrefix M a b) (hbc:PositivePrefix M b c) : PositivePrefix M a c := by
  obtain ⟨u,hu⟩:=hab;obtain ⟨v,hv⟩:=hbc
  exact ⟨u*v,by rw [hv,hu,mul_assoc]⟩

lemma positivePrefix_degree {a b:PositiveArtin M} (h:PositivePrefix M a b) : positiveDegree M a≤positiveDegree M b := by
  obtain ⟨c,rfl⟩:=h
  rw [positiveDegree_mul];omega

lemma positivePrefix_eq_of_degree {a b:PositiveArtin M} (h:PositivePrefix M a b)
    (he:positiveDegree M a=positiveDegree M b) : a=b := by
  obtain ⟨c,rfl⟩:=h
  rw [positiveDegree_mul] at he
  have hc:c=1:=(positiveDegree_zero_iff M c).mp (by omega)
  rw [hc,mul_one]

lemma positivePrefix_antisymm {a b:PositiveArtin M} (hab:PositivePrefix M a b) (hba:PositivePrefix M b a) : a=b :=
  positivePrefix_eq_of_degree M hab (Nat.le_antisymm (positivePrefix_degree M hab) (positivePrefix_degree M hba))

variable [Fintype S]

lemma positivePrefix_simple_iff (u v:M.Group) :
    PositivePrefix M (positiveSimpleLift M u) (positiveSimpleLift M v) ↔ WeakPrefix M.toCoxeterSystem u v := by
  constructor
  · rintro ⟨c,hc⟩
    have hsimple:=(positive_simple_factors M (positiveSimpleLift M u) c v hc.symm).2
    have hm:=congrArg (positiveToCoxeter M) hc
    simp only [positiveToCoxeter_simpleLift,map_mul] at hm
    have he:positiveToCoxeter M c=u⁻¹*v:=by rw [hm,inv_mul_cancel_left]
    have hd:=congrArg (positiveDegree M) hc
    simp only [positiveDegree_simpleLift,positiveDegree_mul] at hd
    rw [hsimple,positiveDegree_simpleLift,he] at hd
    exact hd
  · intro h
    refine ⟨positiveSimpleLift M (u⁻¹*v),?_⟩
    have he:=positiveSimpleLift_mul M u (u⁻¹*v) (by simpa only [mul_inv_cancel_left] using (show M.toCoxeterSystem.length v=M.toCoxeterSystem.length u+M.toCoxeterSystem.length (u⁻¹*v) from h))
    simpa only [mul_inv_cancel_left] using he

lemma positivePrefix_of_simple_eq {a b:PositiveArtin M} {w:M.Group}
    (h:PositivePrefix M a b) (hb:b=positiveSimpleLift M w) :
    a=positiveSimpleLift M (positiveToCoxeter M a) := by
  obtain ⟨c,hc⟩:=h
  exact (positive_simple_factors M a c w (hc.symm.trans hb)).1

theorem exists_greatest_common_simplePrefix (u v:M.Group) :
    ∃g:M.Group,PositivePrefix M (positiveSimpleLift M g) (positiveSimpleLift M u) ∧
      PositivePrefix M (positiveSimpleLift M g) (positiveSimpleLift M v) ∧
      ∀a:PositiveArtin M,PositivePrefix M a (positiveSimpleLift M u)→
        PositivePrefix M a (positiveSimpleLift M v)→PositivePrefix M a (positiveSimpleLift M g) := by
  obtain ⟨g,hgu,hgv,hgreat⟩:=exists_greatest_common_weakPrefix M.toCoxeterSystem u v
  refine ⟨g,(positivePrefix_simple_iff M g u).mpr hgu,(positivePrefix_simple_iff M g v).mpr hgv,?_⟩
  intro a hau hav
  have he:=positivePrefix_of_simple_eq M hau rfl
  rw [he] at hau hav ⊢
  exact (positivePrefix_simple_iff M _ _).mpr (hgreat _
    ((positivePrefix_simple_iff M _ _).mp hau) ((positivePrefix_simple_iff M _ _).mp hav))

@[simp] lemma positiveSimpleLift_simple (s:S) : positiveSimpleLift M (M.toCoxeterSystem.simple s)=positiveGenerator M s := by
  have h:M.toCoxeterSystem.IsReduced [s]:=by
    change M.toCoxeterSystem.length (M.toCoxeterSystem.simple s)=1
    exact M.toCoxeterSystem.length_simple s
  exact positiveSimpleLift_word M [s] h

@[simp] lemma positiveSimpleLift_one : positiveSimpleLift M 1=1 := by
  have h:M.toCoxeterSystem.IsReduced []:=by
    change M.toCoxeterSystem.length 1=0
    exact M.toCoxeterSystem.length_one
  exact positiveSimpleLift_word M [] h

end HarmonicArtin

end OAI
