import Mathlib
import OAI.Topology.ArtinGroups.Realizations.OrderWeightsContractibleLower
import OAI.Topology.ArtinGroups.Harmonic.OrderMappingCylinder
import OAI.Topology.ArtinGroups.Realizations.WeightInsertRetract

namespace OAI

namespace HarmonicArtin
attribute [local instance] Classical.decEq Classical.propDecidable
variable {P : Type} [PartialOrder P] (f : P →o ℕ)

namespace NaturalCylinder

def earlier := WeightJoinEarlier (OrderMappingCylinder.old f) (OrderMappingCylinder.project f)

lemma inl_old (p : P) : (OrderMappingCylinder.left f p) ∈ OrderMappingCylinder.old f := ⟨p,rfl⟩
lemma inr_not_old (n : ℕ) : (OrderMappingCylinder.right f n) ∉ OrderMappingCylinder.old f := by
  rintro ⟨p,h⟩
  cases h

lemma earlier_inr_iff (m n : ℕ) : earlier f (OrderMappingCylinder.right f m) (OrderMappingCylinder.right f n) ↔ m < n := by
  rw [earlier,weightJoinEarlier_iff]
  simp only [weightJoinKey,ite_eq_right (inr_not_old f m),ite_eq_right (inr_not_old f n)]
  change (m+1<n+1 ∨ m+1=n+1 ∧ WellOrderingRel (OrderMappingCylinder.right f m) (OrderMappingCylinder.right f n)) ↔ m<n
  constructor
  · rintro (h|⟨he,hr⟩)
    · omega
    · have he' : m=n := by omega
      subst m
      exact (WellOrderingRel.isWellOrder.wf.irrefl.irrefl _ hr).elim
  · intro h; exact Or.inl (by omega)

lemma link_iff (x : OrderMappingCylinder f) (n : ℕ) :
    (earlier f x (OrderMappingCylinder.right f n) ∧ (x ≤ OrderMappingCylinder.right f n ∨ OrderMappingCylinder.right f n ≤ x)) ↔ x < OrderMappingCylinder.right f n := by
  cases x with
  | inl p =>
    have hr : earlier f (OrderMappingCylinder.left f p) (OrderMappingCylinder.right f n) :=
      weightJoinEarlier_old _ _ (inl_old f p) (inr_not_old f n)
    change (earlier f (OrderMappingCylinder.left f p) (OrderMappingCylinder.right f n) ∧ (f p ≤ n ∨ False)) ↔ OrderMappingCylinder.left f p < OrderMappingCylinder.right f n
    rw [lt_iff_le_not_ge]
    change (_ ∧ (f p≤n ∨ False)) ↔ (f p≤n ∧ ¬ False)
    simp only [hr,true_and,or_false,not_false_eq_true,and_true]
  | inr m =>
    change (earlier f (OrderMappingCylinder.right f m) (OrderMappingCylinder.right f n) ∧ (OrderMappingCylinder.right f m ≤ OrderMappingCylinder.right f n ∨ OrderMappingCylinder.right f n ≤ OrderMappingCylinder.right f m)) ↔ OrderMappingCylinder.right f m < OrderMappingCylinder.right f n
    rw [earlier_inr_iff]
    change (m < n ∧ (m ≤ n ∨ n ≤ m)) ↔ (m ≤ n ∧ ¬ n ≤ m)
    omega

noncomputable def linkIso (n : ℕ) :
    WeightEarlierLink (earlier f) (OrderMappingCylinder.right f n) ≃o {x : OrderMappingCylinder f // x < OrderMappingCylinder.right f n} where
  toFun x := ⟨x.val,(link_iff f x.val n).mp x.property⟩
  invFun x := ⟨x.val,(link_iff f x.val n).mpr x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := by intros; rfl

end NaturalCylinder

noncomputable def lowerOldIso {R : Type*} [PartialOrder R] (A : Set R) (v : R) :
    {x : {p : R // p < v} // x.val ∈ A} ≃o {x : R // x ∈ A ∧ x < v} where
  toFun x := ⟨x.val.val,x.property,x.val.property⟩
  invFun x := ⟨⟨x.val,x.property.2⟩,x.property.1⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := by intros; rfl

noncomputable def lowerOldLowerIso {R : Type*} [PartialOrder R] (A : Set R) (v : R)
    (w : {p : R // p < v}) :
    {x : {p : R // p < v} // x.val ∈ A ∧ x < w} ≃o {x : R // x ∈ A ∧ x < w.val} where
  toFun x := ⟨x.val.val,x.property.1,x.property.2⟩
  invFun x := ⟨⟨x.val,x.property.2.trans w.property⟩,x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := by intros; rfl

theorem naturalCylinder_lower_contractible (k : P → ℕ) (N : ℕ)
    (hk : ∀ p, k p ≤ N) (hkm : StrictMono k)
    (hf : ∀ n, ContractibleSpace (OrderWeights {p : P // f p ≤ n})) (n : ℕ) :
    ContractibleSpace (OrderWeights {x : OrderMappingCylinder f // x < OrderMappingCylinder.right f n}) := by
  let Q := {x : OrderMappingCylinder f // x < OrderMappingCylinder.right f n}
  let A : Set Q := {x | x.val ∈ OrderMappingCylinder.old f}
  let rank : Q → ℕ := fun x => OrderMappingCylinder.rank f k id N x.val
  have hrank : ∀ x, rank x ≤ N+n := by
    intro x
    cases hx : x.val with
    | inl p =>
      have hb := hk p
      change OrderMappingCylinder.rank f k id N x.val ≤ N+n
      rw [hx]
      change k p ≤ N+n
      omega
    | inr m =>
      have hh := x.property
      rw [hx] at hh
      change OrderMappingCylinder.right f m < OrderMappingCylinder.right f n at hh
      rw [lt_iff_le_not_ge] at hh
      change m ≤ n ∧ ¬ n ≤ m at hh
      change OrderMappingCylinder.rank f k id N x.val ≤ N+n
      rw [hx]
      change N+1+m ≤ N+n
      omega
  have hrankm : StrictMono rank := by
    intro x y h
    exact OrderMappingCylinder.rank_strict f k id N hk hkm (fun _ _ h => h) h
  have hA : ContractibleSpace (OrderWeights A) :=
    (weightHomeomorph (lowerOldIso (OrderMappingCylinder.old f) (OrderMappingCylinder.right f n))).contractibleSpace_iff.mpr
      ((weightHomeomorph (OrderMappingCylinder.oldLowerIso f n)).contractibleSpace_iff.mp (hf n))
  apply orderWeights_contractible_of_lower_fibers A rank (N+n) hrank hrankm hA
  intro v hv
  have hnv : v.val ∉ OrderMappingCylinder.old f := hv
  obtain ⟨m,hm⟩ := (OrderMappingCylinder.not_old_iff f v.val).mp hnv
  let e := lowerOldLowerIso (OrderMappingCylinder.old f) (OrderMappingCylinder.right f n) v
  rw [hm] at e
  exact (weightHomeomorph e).contractibleSpace_iff.mpr
    ((weightHomeomorph (OrderMappingCylinder.oldLowerIso f m)).contractibleSpace_iff.mp (hf m))

theorem orderWeights_contractible_of_natural_preimages (k : P → ℕ) (N : ℕ)
    (hk : ∀ p, k p ≤ N) (hkm : StrictMono k)
    (hf : ∀ n, ContractibleSpace (OrderWeights {p : P // f p ≤ n})) :
    ContractibleSpace (OrderWeights P) := by
  let r := NaturalCylinder.earlier f
  obtain ⟨g,hg⟩ := orderWeights_retract_of_initial r
    (weightJoinEarlier_wf _ _) (weightJoinEarlier_total _ _)
    (OrderMappingCylinder.old f) (weightJoinEarlier_initial _ _) (by
      intro v hv
      obtain ⟨n,rfl⟩ := (OrderMappingCylinder.not_old_iff f v).mp hv
      exact (weightHomeomorph (NaturalCylinder.linkIso f n)).contractibleSpace_iff.mpr
        (naturalCylinder_lower_contractible f k N hk hkm hf n))
  have hNat : ContractibleSpace (OrderWeights ℕ) :=
    nerveWeightsHomeomorph.contractibleSpace_iff.mp (nerve_orderBot_contractible ℕ)
  have hR := OrderMappingCylinder.weights_contractible f hNat
  have hA := contractible_of_continuous_retract
    (weightMapContinuous (weightInclusion (OrderMappingCylinder.old f))) g hg hR
  exact (weightHomeomorph (OrderMappingCylinder.oldIso f)).contractibleSpace_iff.mpr hA

end HarmonicArtin

end OAI
