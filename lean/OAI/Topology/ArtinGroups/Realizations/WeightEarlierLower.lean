import Mathlib
import OAI.Topology.ArtinGroups.Realizations.WeightJoinKey
import OAI.Topology.ArtinGroups.Realizations.WeightDual

namespace OAI

namespace HarmonicArtin
attribute [local instance] Classical.decEq Classical.propDecidable
universe u
variable {P:Type u} [PartialOrder P]

abbrev WeightEarlierLower (r:P→P→Prop) (v:P) := {x:P // r x v ∧ x<v}
abbrev WeightEarlierUpper (r:P→P→Prop) (v:P) := {x:P // r x v ∧ v<x}

noncomputable def earlierLowerIso (r:P→P→Prop) (v:P) :
    WeightEarlierLower r v≃o {x:WeightEarlierLink r v // x.val<v} where
  toFun x:=⟨⟨x.val,x.property.1,Or.inl x.property.2.le⟩,x.property.2⟩
  invFun x:=⟨x.val.val,x.val.property.1,x.property⟩
  left_inv _:=rfl
  right_inv _:=rfl
  map_rel_iff':=by intros;rfl

noncomputable def earlierUpperIso (r:P→P→Prop) (hirr:∀x,¬r x x) (v:P) :
    WeightEarlierUpper r v≃o {x:WeightEarlierLink r v // ¬x.val<v} where
  toFun x:=⟨⟨x.val,x.property.1,Or.inr x.property.2.le⟩,not_lt_of_ge x.property.2.le⟩
  invFun x:=⟨x.val.val,x.val.property.1,by
    have hne : x.val.val≠v := by
      intro he
      have hr:=x.val.property.1
      rw [he] at hr
      exact hirr v hr
    rcases x.val.property.2 with h|h
    · exact (x.property (lt_of_le_of_ne h hne)).elim
    · exact lt_of_le_of_ne h hne.symm⟩
  left_inv _:=rfl
  right_inv _:=rfl
  map_rel_iff':=by intros;rfl

lemma weightLink_lower_cross (r:P→P→Prop) (hirr:∀x,¬r x x) (v:P)
    {a b:WeightEarlierLink r v} (ha:a.val<v) (hb:¬b.val<v) : a≤b := by
  rcases b.property.2 with h|h
  · rcases lt_or_eq_of_le h with hl|he
    · exact (hb hl).elim
    · have hr:=b.property.1
      rw [he] at hr
      exact (hirr v hr).elim
  · exact ha.le.trans h

theorem weightLink_contractible_of_lower (r:P→P→Prop) (hirr:∀x,¬r x x) (v:P)
    (k:P→ℕ) (N:ℕ) (hk:∀x,k x≤N) (hmono:StrictMono k)
    (h:ContractibleSpace (OrderWeights (WeightEarlierLower r v))) :
    ContractibleSpace (OrderWeights (WeightEarlierLink r v)) := by
  let A:Set (WeightEarlierLink r v):={x | x.val<v}
  have hA:ContractibleSpace (OrderWeights A):=(weightHomeomorph (earlierLowerIso r v)).contractibleSpace_iff.mp h
  apply weightJoin_contractible (N+1) A (fun x=>N-k x.val)
    (fun x _=>by omega) ?_ (weightLink_lower_cross r hirr v) hA
  intro x y hx hy hxy
  have hlt:k x.val<k y.val:=hmono hxy
  have hb:=hk y.val
  omega

theorem weightJoin_contractible_upper (N:ℕ) (A:Set P) (k:P→ℕ)
    (hk:∀x,x∈A → k x<N)
    (hmono:∀{x y},x∈A → y∈A → x<y → k x<k y)
    (hcross:∀{a b},a∈A → b∉A → a≤b)
    (hB:ContractibleSpace (OrderWeights (Aᶜ:Set P))) : ContractibleSpace (OrderWeights P) := by
  have hdual:ContractibleSpace (OrderWeights Pᵒᵈ):=by
    apply weightJoin_contractible N (Aᶜ:Set Pᵒᵈ) k
    · intro x hx
      exact hk x (not_not.mp hx)
    · intro x y hx hy hxy
      exact hmono (not_not.mp hy) (not_not.mp hx) hxy
    · intro a b ha hb
      exact hcross (not_not.mp hb) ha
    · exact (weightDualHomeomorph (P:=(Aᶜ:Set P))).contractibleSpace_iff.mp hB
  exact (weightDualHomeomorph (P:=P)).contractibleSpace_iff.mpr hdual

theorem weightLink_contractible_of_upper (r:P→P→Prop) (hirr:∀x,¬r x x) (v:P)
    (k:P→ℕ) (N:ℕ) (hk:∀x,k x≤N) (hmono:StrictMono k)
    (h:ContractibleSpace (OrderWeights (WeightEarlierUpper r v))) :
    ContractibleSpace (OrderWeights (WeightEarlierLink r v)) := by
  let A:Set (WeightEarlierLink r v):={x | x.val<v}
  have hB:ContractibleSpace (OrderWeights (Aᶜ:Set (WeightEarlierLink r v))):=
    (weightHomeomorph (earlierUpperIso r hirr v)).contractibleSpace_iff.mp h
  apply weightJoin_contractible_upper (N+1) A (fun x=>k x.val)
    (fun x _=>Nat.lt_succ_of_le (hk x.val))
    (by intro x y _ _ hxy;exact hmono hxy) (weightLink_lower_cross r hirr v) hB

lemma weightLink_nonempty_parts (r:P→P→Prop) (hirr:∀x,¬r x x) (v:P)
    (h:Nonempty (WeightEarlierLink r v)) :
    Nonempty (WeightEarlierLower r v) ∨ Nonempty (WeightEarlierUpper r v) := by
  obtain ⟨x,hx,hcmp⟩:=h
  have hne:x≠v:=by intro he;exact hirr v (he ▸ hx)
  exact hcmp.elim (fun h=>Or.inl ⟨x,hx,lt_of_le_of_ne h hne⟩)
    (fun h=>Or.inr ⟨x,hx,lt_of_le_of_ne h hne.symm⟩)

end HarmonicArtin

end OAI
