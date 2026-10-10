import Mathlib
import OAI.Topology.ArtinGroups.Realizations.ContractionPoint

namespace OAI

namespace HarmonicArtin
attribute [local instance] Classical.decEq Classical.propDecidable
universe u
variable {P:Type u} [PartialOrder P]

noncomputable def weightJoinKey (A:Set P) (d:P→ℕ) (x:P) : ℕ :=
  if x∈A then 0 else d x+1

def WeightJoinEarlier (A:Set P) (d:P→ℕ) (x y:P) : Prop :=
  Prod.Lex (·<·) WellOrderingRel (weightJoinKey A d x,x) (weightJoinKey A d y,y)

omit [PartialOrder P] in
lemma weightJoinEarlier_wf (A:Set P) (d:P→ℕ) : WellFounded (WeightJoinEarlier A d) :=
  InvImage.wf (fun x=>(weightJoinKey A d x,x))
    (wellFounded_lt.prod_lex WellOrderingRel.isWellOrder.wf)

omit [PartialOrder P] in
lemma weightJoinEarlier_iff (A:Set P) (d:P→ℕ) (x y:P) :
    WeightJoinEarlier A d x y ↔ weightJoinKey A d x<weightJoinKey A d y ∨
      weightJoinKey A d x=weightJoinKey A d y ∧ WellOrderingRel x y := Prod.lex_iff

omit [PartialOrder P] in
lemma weightJoinEarlier_total (A:Set P) (d:P→ℕ) (x y:P) (h:x≠y) :
    WeightJoinEarlier A d x y ∨ WeightJoinEarlier A d y x := by
  rw [weightJoinEarlier_iff,weightJoinEarlier_iff]
  rcases lt_trichotomy (weightJoinKey A d x) (weightJoinKey A d y) with h'|he|h'
  · exact Or.inl (Or.inl h')
  · rcases trichotomous_of WellOrderingRel x y with hl|he'|hr
    · exact Or.inl (Or.inr ⟨he,hl⟩)
    · exact (h he').elim
    · exact Or.inr (Or.inr ⟨he.symm,hr⟩)
  · exact Or.inr (Or.inl h')

omit [PartialOrder P] in
lemma weightJoinEarlier_initial (A:Set P) (d:P→ℕ) {x y:P} (hx:x∈A)
    (hy:WeightJoinEarlier A d y x) : y∈A := by
  by_contra hn
  rw [weightJoinEarlier_iff] at hy
  simp [weightJoinKey,hx,hn] at hy

omit [PartialOrder P] in
lemma weightJoinEarlier_old (A:Set P) (d:P→ℕ) {x y:P} (hx:x∈A) (hy:y∉A) :
    WeightJoinEarlier A d x y := by
  rw [weightJoinEarlier_iff]
  left
  simp [weightJoinKey,hx,hy]

theorem weightJoin_contractible (N:ℕ) : ∀{P:Type u} [PartialOrder P]
    (A:Set P) (d:P→ℕ),
    (∀x,x∉A → d x<N) →
    (∀{x y},x∉A → y∉A → x<y → d y<d x) →
    (∀{a b},a∈A → b∉A → a≤b) →
    ContractibleSpace (OrderWeights A) → ContractibleSpace (OrderWeights P) := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro P inst A d hb hd hcross hA
    let r:=WeightJoinEarlier A d
    apply orderWeights_contractible_of_initial r (weightJoinEarlier_wf A d)
      (weightJoinEarlier_total A d) A (weightJoinEarlier_initial A d) hA
    intro v hv
    let L:=WeightEarlierLink r v
    let A':Set L:={x | x.val∈A}
    have hne (x:L) : x.val≠v := by
      intro he
      have hr:=x.property.1
      rw [he] at hr
      exact (weightJoinEarlier_wf A d).irrefl.irrefl v hr
    have hupper (x:L) (hx:x∉A') : v<x.val := by
      have hr:WeightJoinEarlier A d x.val v:=x.property.1
      rw [weightJoinEarlier_iff] at hr
      have hx':x.val∉A:=hx
      simp [weightJoinKey,hx',hv] at hr
      rcases x.property.2 with hl|hu
      · have lt:x.val<v:=lt_of_le_of_ne hl (hne x)
        have :=hd hx' hv lt
        omega
      · exact lt_of_le_of_ne hu (hne x).symm
    let e:A≃oA':={
      toFun:=fun a=>⟨⟨a.val,weightJoinEarlier_old A d a.property hv,
        Or.inl (hcross a.property hv)⟩,a.property⟩
      invFun:=fun a=>⟨a.val.val,a.property⟩
      left_inv:=fun _=>rfl
      right_inv:=fun _=>rfl
      map_rel_iff':=by intros;rfl }
    have hA':ContractibleSpace (OrderWeights A'):=
      (weightHomeomorph e).contractibleSpace_iff.mp hA
    exact ih (d v) (hb v hv) A' (fun x:L=>d x.val)
      (fun x hx=>hd hv hx (hupper x hx))
      (by intro x y hx hy hxy;exact hd hx hy hxy)
      (by intro a b ha hb;exact hcross ha hb) hA'

end HarmonicArtin

end OAI
