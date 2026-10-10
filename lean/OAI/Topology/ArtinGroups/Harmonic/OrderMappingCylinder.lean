import Mathlib
import OAI.Topology.ArtinGroups.Realizations.NerveChain
import OAI.Topology.ArtinGroups.Realizations.NerveOrderRetractionEquiv

namespace OAI

namespace HarmonicArtin
open Simplicial

universe u
variable {P Q:Type u} [PartialOrder P] [PartialOrder Q]

def OrderMappingCylinder (_ : P→oQ) := P ⊕ Q

namespace OrderMappingCylinder
variable (f:P→oQ)

def le : OrderMappingCylinder f → OrderMappingCylinder f → Prop := fun x y=>match x,y with
  | .inl p,.inl p' => p≤p'
  | .inr q,.inr q' => q≤q'
  | .inl p,.inr q => f p≤q
  | .inr _,.inl _ => False

instance : PartialOrder (OrderMappingCylinder f) where
  le:=le f
  le_refl:=by intro x;cases x <;> exact le_refl _
  le_trans:=by
    intro x y z h k
    cases x with
    | inl p=>
      cases y with
      | inl p'=>
        cases z with
        | inl p''=>exact h.trans k
        | inr q=>exact (f.monotone h).trans k
      | inr q=>
        cases z with
        | inl p'=>exact k.elim
        | inr q'=>exact h.trans k
    | inr q=>
      cases y with
      | inl p=>exact h.elim
      | inr q'=>
        cases z with
        | inl p=>exact k.elim
        | inr q''=>exact h.trans k
  le_antisymm:=by
    intro x y h k
    cases x with
    | inl p=>
      cases y with
      | inl p'=>exact congrArg Sum.inl (le_antisymm h k)
      | inr q=>exact k.elim
    | inr q=>
      cases y with
      | inl p=>exact h.elim
      | inr q'=>exact congrArg Sum.inr (le_antisymm h k)

def left : P→oOrderMappingCylinder f := ⟨Sum.inl,fun _ _ h=>h⟩
def right : Q→oOrderMappingCylinder f := ⟨Sum.inr,fun _ _ h=>h⟩
def project : OrderMappingCylinder f→oQ where
  toFun:=Sum.elim f id
  monotone':=by
    intro x y h
    cases x with
    | inl p=>cases y with
      | inl p'=>exact f.monotone h
      | inr q=>exact h
    | inr q=>cases y with
      | inl p=>exact h.elim
      | inr q'=>exact h

lemma project_right : (project f).comp (right f)=OrderHom.id := by ext q;rfl
lemma le_right_project (x:OrderMappingCylinder f) : x≤right f (project f x) := by
  cases x <;> exact le_refl _

noncomputable def nerveEquiv : ContinuousMap.HomotopyEquiv
    |CategoryTheory.nerve (OrderMappingCylinder f)| |CategoryTheory.nerve Q| :=
  nerveOrderRetractionEquiv (project f) (right f) (project_right f) (le_right_project f)

lemma weights_contractible (h:ContractibleSpace (OrderWeights Q)) :
    ContractibleSpace (OrderWeights (OrderMappingCylinder f)) := by
  have hQ:=nerveWeightsHomeomorph.contractibleSpace_iff.mpr h
  exact nerveWeightsHomeomorph.contractibleSpace_iff.mp ((nerveEquiv f).contractibleSpace_iff.mpr hQ)

def old : Set (OrderMappingCylinder f) := Set.range (left f)

noncomputable def oldIso : P≃o old f where
  toFun p:=⟨left f p,⟨p,rfl⟩⟩
  invFun x:=Classical.choose x.property
  left_inv:=by intro p;exact Sum.inl.inj (Classical.choose_spec (show left f p∈old f from ⟨p,rfl⟩))
  right_inv:=by intro x;apply Subtype.ext;exact Classical.choose_spec x.property
  map_rel_iff':=by intros;rfl

lemma not_old_iff (x:OrderMappingCylinder f) : x∉old f ↔ ∃q,x=Sum.inr q := by
  cases x with
  | inl p=>
    constructor
    · intro hn;exact (hn ⟨p,rfl⟩).elim
    · rintro ⟨q,h⟩;cases h
  | inr q=>
    refine ⟨fun _=>⟨q,rfl⟩,?_⟩
    rintro _ ⟨p,h⟩
    cases h

def rank (k:P→ℕ) (l:Q→ℕ) (N:ℕ) : OrderMappingCylinder f→ℕ := fun x=>match x with
  | .inl p=>k p
  | .inr q=>N+1+l q

lemma rank_bound (k:P→ℕ) (l:Q→ℕ) (N L:ℕ) (hk:∀p,k p≤N) (hl:∀q,l q≤L)
    (x:OrderMappingCylinder f) : rank f k l N x≤N+1+L := by
  cases x with
  | inl p=>have:=hk p;dsimp [rank];omega
  | inr q=>have:=hl q;dsimp [rank];omega

lemma rank_strict (k:P→ℕ) (l:Q→ℕ) (N:ℕ) (hk:∀p,k p≤N)
    (hkm:StrictMono k) (hlm:StrictMono l) : StrictMono (rank f k l N) := by
  intro x y h
  rw [lt_iff_le_not_ge] at h
  cases x with
  | inl p=>cases y with
    | inl p'=>exact hkm (lt_iff_le_not_ge.mpr h)
    | inr q=>have:=hk p;dsimp [rank];omega
  | inr q=>cases y with
    | inl p=>exact h.1.elim
    | inr q'=>exact Nat.add_lt_add_left (hlm (lt_iff_le_not_ge.mpr h)) _

noncomputable def oldLowerIso (q:Q) : {p:P // f p≤q} ≃o
    {x:OrderMappingCylinder f // x∈old f ∧ x<Sum.inr q} where
  toFun p:=⟨Sum.inl p.val,⟨p.val,rfl⟩,lt_iff_le_not_ge.mpr ⟨p.property,not_false⟩⟩
  invFun x:=⟨Classical.choose x.property.1,by
    have h:=x.property.2.le
    rw [← Classical.choose_spec x.property.1] at h
    exact h⟩
  left_inv:=by
    intro p;apply Subtype.ext
    exact Sum.inl.inj (Classical.choose_spec (show Sum.inl p.val∈old f from ⟨p.val,rfl⟩))
  right_inv:=by intro x;apply Subtype.ext;exact Classical.choose_spec x.property.1
  map_rel_iff':=by intros;rfl

end OrderMappingCylinder
end HarmonicArtin

end OAI
