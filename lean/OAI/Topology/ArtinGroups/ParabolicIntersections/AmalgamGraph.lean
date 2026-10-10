import OAI.Topology.ArtinGroups.ParabolicIntersections.Basic
import Mathlib.GroupTheory.PushoutI
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Combinatorics.SimpleGraph.Acyclic

namespace OAI

/-! The coset graph of a two-factor amalgam, with its genuine group action. -/
namespace HarmonicArtin.ParabolicIntersections.AmalgamTree
open Monoid
attribute [local instance] Classical.decEq Classical.propDecidable
variable {G : Bool → Type} [∀ b, Group (G b)] {H : Type} [Group H]
variable (φ : ∀ b, H →* G b)

abbrev Amalgam := Monoid.PushoutI φ
abbrev Factor (b : Bool) : Subgroup (Amalgam φ) := (PushoutI.of b).range
abbrev Vertex := Σ b : Bool, Amalgam φ ⧸ Factor φ b

def vertex (b : Bool) (g : Amalgam φ) : Vertex φ := ⟨b,QuotientGroup.mk g⟩

def graph : SimpleGraph (Vertex φ) where
  Adj u v := u.1≠v.1 ∧ ∃ g : Amalgam φ,
    u.2=(QuotientGroup.mk g : Amalgam φ ⧸ Factor φ u.1) ∧
    v.2=(QuotientGroup.mk g : Amalgam φ ⧸ Factor φ v.1)
  symm := ⟨by rintro u v ⟨hn,g,hu,hv⟩; exact ⟨hn.symm,g,hv,hu⟩⟩
  loopless := ⟨by rintro v ⟨h,_⟩; exact h rfl⟩

instance : MulAction (Amalgam φ) (Vertex φ) where
  smul g v := ⟨v.1,g • v.2⟩
  one_smul := by
    rintro ⟨b,v⟩
    change (⟨b,(1 : Amalgam φ) • v⟩ : Vertex φ)=⟨b,v⟩
    rw [one_smul]
  mul_smul := by
    rintro a b ⟨i,v⟩
    change (⟨i,(a*b) • v⟩ : Vertex φ)=⟨i,a • (b • v)⟩
    rw [mul_smul]

@[simp] lemma smul_vertex (g h : Amalgam φ) (b : Bool) :
    g • vertex φ b h=vertex φ b (g*h) := rfl

lemma vertex_adj (g : Amalgam φ) : (graph φ).Adj (vertex φ false g) (vertex φ true g) :=
  ⟨Bool.false_ne_true,g,rfl,rfl⟩

def translate (g : Amalgam φ) : graph φ →g graph φ where
  toFun := (g • ·)
  map_rel' := by
    rintro ⟨i,u⟩ ⟨j,v⟩ ⟨hn,h,hu,hv⟩
    refine ⟨hn,g*h,?_,?_⟩
    · change g • u=(QuotientGroup.mk (g*h) : Amalgam φ ⧸ Factor φ i)
      exact congrArg (fun x : Amalgam φ ⧸ Factor φ i => g • x) hu
    · change g • v=(QuotientGroup.mk (g*h) : Amalgam φ ⧸ Factor φ j)
      exact congrArg (fun x : Amalgam φ ⧸ Factor φ j => g • x) hv

lemma vertex_factor_fixed (b : Bool) (a : G b) :
    vertex φ b (PushoutI.of b a)=vertex φ b 1 := by
  apply Sigma.mk.inj_iff.mpr
  refine ⟨rfl,heq_of_eq ?_⟩
  apply QuotientGroup.eq.mpr
  change (PushoutI.of b a)⁻¹*1∈(PushoutI.of (φ := φ) b).range
  exact ⟨a⁻¹,by simp⟩

lemma root_to_base (b : Bool) :
    (graph φ).Reachable (vertex φ false 1) (vertex φ b 1) := by
  cases b
  · rfl
  · exact (vertex_adj φ 1).reachable

lemma base_to_base (b c : Bool) :
    (graph φ).Reachable (vertex φ b 1) (vertex φ c 1) :=
  (root_to_base φ b).symm.trans (root_to_base φ c)

lemma root_to_vertex (g : Amalgam φ) (b : Bool) :
    (graph φ).Reachable (vertex φ false 1) (vertex φ b g) := by
  suffices h : ∀ b, (graph φ).Reachable (vertex φ false 1) (vertex φ b g) from h b
  induction g using PushoutI.induction_on with
  | of i a =>
    intro b
    have h := (base_to_base φ i b).map (translate φ (PushoutI.of i a))
    change (graph φ).Reachable (vertex φ i (PushoutI.of i a*1))
      (vertex φ b (PushoutI.of i a*1)) at h
    simp only [mul_one,vertex_factor_fixed] at h
    exact (root_to_base φ i).trans h
  | base a =>
    intro b
    rw [←PushoutI.of_apply_eq_base φ false a]
    have h := (base_to_base φ false b).map (translate φ (PushoutI.of false (φ false a)))
    change (graph φ).Reachable (vertex φ false (PushoutI.of false (φ false a)*1))
      (vertex φ b (PushoutI.of false (φ false a)*1)) at h
    simpa only [mul_one,vertex_factor_fixed] using h
  | mul g h ihg ihh =>
    intro b
    have hh := (ihh b).map (translate φ g)
    change (graph φ).Reachable (vertex φ false (g*1)) (vertex φ b (g*h)) at hh
    rw [mul_one] at hh
    exact (ihg false).trans hh

theorem connected : (graph φ).Connected := by
  let : Nonempty (Vertex φ) := ⟨vertex φ false 1⟩
  refine ⟨?_⟩
  rintro ⟨b,u⟩ ⟨c,v⟩
  obtain ⟨g,rfl⟩ := Quotient.exists_rep u
  obtain ⟨h,rfl⟩ := Quotient.exists_rep v
  exact (root_to_vertex φ g b).symm.trans (root_to_vertex φ h c)

lemma vertex_stabilizer (b : Bool) (g : Amalgam φ) :
    MulAction.stabilizer (Amalgam φ) (vertex φ b g)=conjugate g (Factor φ b) := by
  ext a
  change (a • vertex φ b g=vertex φ b g) ↔ _
  rw [smul_vertex]
  simp only [vertex,Sigma.mk.inj_iff,heq_eq_eq,true_and,QuotientGroup.eq,mem_conjugate]
  constructor
  · intro h
    simpa only [mul_inv_rev,inv_inv,mul_assoc] using (Factor φ b).inv_mem h
  · intro h
    simpa only [mul_inv_rev,inv_inv,mul_assoc] using (Factor φ b).inv_mem h

lemma edge_stabilizer (hφ : ∀ b, Function.Injective (φ b)) (g : Amalgam φ) :
    MulAction.stabilizer (Amalgam φ) (vertex φ false g) ⊓
      MulAction.stabilizer (Amalgam φ) (vertex φ true g)=
        conjugate g (PushoutI.base φ).range := by
  rw [vertex_stabilizer,vertex_stabilizer,←conjugate_inf]
  congr 1
  exact PushoutI.inf_of_range_eq_base_range hφ Bool.false_ne_true

end HarmonicArtin.ParabolicIntersections.AmalgamTree

end OAI
