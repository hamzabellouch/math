import Mathlib
import OAI.Topology.ArtinGroups.Quivers.OffDiagonalVertexZero

namespace OAI

namespace HarmonicArtin.ReversibleQuiver
variable {V A:Type*} (Q:ReversibleQuiver V A)
attribute [local instance] Classical.decEq Classical.propDecidable

abbrev ProbeVertex (V:Type*) := V⊕(V×Bool)
abbrev ProbeArrow (V A:Type*) := A⊕(V×Bool×Bool)

def probeQuiver : ReversibleQuiver (ProbeVertex V) (ProbeArrow V A) where
  source
    | .inl a => .inl (Q.source a)
    | .inr (v,b,dir) => if dir then .inr (v,b) else .inl v
  target
    | .inl a => .inl (Q.target a)
    | .inr (v,b,dir) => if dir then .inl v else .inr (v,b)
  reverse :=
    { toFun := fun a => match a with
        | .inl a => .inl (Q.reverse a)
        | .inr (v,b,dir) => .inr (v,b,!dir)
      invFun := fun a => match a with
        | .inl a => .inl (Q.reverse a)
        | .inr (v,b,dir) => .inr (v,b,!dir)
      left_inv := by
        rintro (a|⟨v,b,dir⟩)
        · simp only [Q.reverse_reverse]
        · simp
      right_inv := by
        rintro (a|⟨v,b,dir⟩)
        · simp only [Q.reverse_reverse]
        · simp }
  reverse_reverse := by
    rintro (a|⟨v,b,dir⟩)
    · simp only [Equiv.coe_fn_mk,Q.reverse_reverse]
    · simp
  source_reverse := by
    rintro (a|⟨v,b,dir⟩)
    · simp only [Equiv.coe_fn_mk,Q.source_reverse]
    · cases dir <;> rfl
  target_reverse := by
    rintro (a|⟨v,b,dir⟩)
    · simp only [Equiv.coe_fn_mk,Q.target_reverse]
    · cases dir <;> rfl

lemma probeQuiver_no_loops (hn:∀a,Q.source a≠Q.target a) :
    ∀a,(probeQuiver Q).source a≠(probeQuiver Q).target a := by
  rintro (a|⟨v,b,dir⟩)
  · exact fun h=>hn a (Sum.inl.inj h)
  · cases dir <;> simp [probeQuiver]

lemma probe_source_iff (v:V) (b:Bool) (a:ProbeArrow V A) :
    (probeQuiver Q).source a=.inr (v,b) ↔ a=.inr (v,b,true) := by
  cases a with
  | inl a => simp [probeQuiver]
  | inr a => rcases a with ⟨w,c,dir⟩; cases dir <;> simp [probeQuiver]

lemma probe_target_iff (v:V) (b:Bool) (a:ProbeArrow V A) :
    (probeQuiver Q).target a=.inr (v,b) ↔ a=.inr (v,b,false) := by
  cases a with
  | inl a => simp [probeQuiver]
  | inr a => rcases a with ⟨w,c,dir⟩; cases dir <;> simp [probeQuiver]

namespace Zigzag.BasedComplex
variable {K I:Type*} [Field K] [Fintype V] [Fintype A] [Fintype I]
local notation "R" => probeQuiver Q

abbrev probeCoefficient (E:BasedComplex R (K:=K) I) (α:V) (n v:ℤ) :=
  {j:I // (E.placement j).color=.inl α ∧ (E.placement j).cochain=n ∧
    (E.placement j).internal=v-1}

lemma probeHomPath_arrow (E:BasedComplex R (K:=K) I) (α:V) (b:Bool)
    (ha:∀i,(E.placement i).color≠.inr (α,b)) (n v:ℤ)
    (t:HomPath R ((initialProjective R (.inr (α,b)) : BasedComplex R (K:=K) PUnit.{1})) E n v) :
    t.val.2.2=.inr (.inl (.inr (α,b,true))) := by
  rcases t with ⟨⟨i,j,p⟩,hs,ht,hc,hd⟩
  cases p with
  | inl w => exact False.elim (ha j (ht.symm.trans hs))
  | inr p => cases p with
    | inl a =>
      exact congrArg (fun a:ProbeArrow V A=>Sum.inr (Sum.inl a))
        ((probe_source_iff Q α b a).mp hs)
    | inr w => exact False.elim (ha j (ht.symm.trans hs))

noncomputable def probeHomPathEquiv (E:BasedComplex R (K:=K) I) (α:V) (b:Bool)
    (ha:∀i,(E.placement i).color≠.inr (α,b)) (n v:ℤ) :
    HomPath R ((initialProjective R (.inr (α,b)) : BasedComplex R (K:=K) PUnit.{1})) E n v ≃ probeCoefficient Q E α n v where
  toFun t := ⟨t.val.2.1,by
    have hp:=probeHomPath_arrow Q E α b ha n v t
    have ht:=t.property.2.1
    have hc:=t.property.2.2.1
    have hd:=t.property.2.2.2
    rw [hp] at ht hd
    change Sum.inl α=(E.placement t.val.2.1).color at ht
    change (E.placement t.val.2.1).cochain=0+n at hc
    change (1:ℤ)=v+0-(E.placement t.val.2.1).internal at hd
    exact ⟨ht.symm,by omega,by omega⟩⟩
  invFun j := ⟨(PUnit.unit,j.val,.inr (.inl (.inr (α,b,true)))),by
    refine ⟨rfl,j.property.1.symm,?_,?_⟩
    · change (E.placement j.val).cochain=0+n
      rw [j.property.2.1,zero_add]
    · change (1:ℤ)=v+0-(E.placement j.val).internal
      rw [j.property.2.2]; omega⟩
  left_inv t := by
    apply Subtype.ext
    apply Prod.ext
    · exact Subsingleton.elim _ _
    · exact Prod.ext rfl (probeHomPath_arrow Q E α b ha n v t).symm
  right_inv _ := rfl

lemma probeHomDimension (E:BasedComplex R (K:=K) I) (hE:E.IsMinimal R)
    (α:V) (b:Bool) (ha:∀i,(E.placement i).color≠.inr (α,b)) (n v:ℤ) :
    homDimension R ((initialProjective R (.inr (α,b)) : BasedComplex R (K:=K) PUnit.{1})) E n v=
      Nat.card (probeCoefficient Q E α n v) := by
  rw [absentProjective_homDimension R E hE _ ha]
  exact Nat.card_congr (probeHomPathEquiv Q E α b ha n v)

end Zigzag.BasedComplex
end HarmonicArtin.ReversibleQuiver

end OAI
