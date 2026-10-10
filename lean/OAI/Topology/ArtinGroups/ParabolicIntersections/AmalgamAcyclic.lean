import OAI.Topology.ArtinGroups.ParabolicIntersections.AmalgamReduced

namespace OAI

/-! The Bass--Serre coset graph is a tree: a cycle would be a nonempty
reduced word in the amalgam equal to an element of the edge group. -/
namespace HarmonicArtin.ParabolicIntersections.AmalgamTree
open Monoid
attribute [local instance] Classical.decEq Classical.propDecidable
variable {G : Bool → Type} [∀ b, Group (G b)] {H : Type} [Group H]
variable (φ : ∀ b, H →* G b)

lemma adj_representatives {u v : Vertex φ} (h : (graph φ).Adj u v) :
    ∃ g : Amalgam φ, u=vertex φ u.1 g ∧ v=vertex φ v.1 g := by
  obtain ⟨hn,g,hu,hv⟩ := h
  exact ⟨g,Sigma.ext rfl (heq_of_eq hu),Sigma.ext rfl (heq_of_eq hv)⟩

lemma vertex_eq_iff (b : Bool) (g h : Amalgam φ) :
    vertex φ b g=vertex φ b h ↔ g⁻¹*h∈Factor φ b := by
  simp only [vertex,Sigma.mk.inj_iff,heq_eq_eq,true_and,QuotientGroup.eq]

lemma base_le_factor (b : Bool) : (PushoutI.base φ).range≤Factor φ b := by
  rintro _ ⟨h,rfl⟩
  exact ⟨φ b h,PushoutI.of_apply_eq_base φ b h⟩

lemma vertex_eq_of_base (b : Bool) {g h : Amalgam φ}
    (he : g⁻¹*h∈(PushoutI.base φ).range) : vertex φ b g=vertex φ b h :=
  (vertex_eq_iff φ b g h).mpr (base_le_factor φ b he)

lemma other_endpoint_eq {u v w : Vertex φ} {g h : Amalgam φ}
    (hu : u=vertex φ u.1 g) (hw : w=vertex φ w.1 h)
    (huv : u.1≠v.1) (hvw : v.1≠w.1)
    (he : g⁻¹*h∈(PushoutI.base φ).range) : u=w := by
  have ht : u.1=w.1 := by
    cases hu' : u.1 <;> cases hv' : v.1 <;> cases hw' : w.1 <;> simp_all
  calc
    u = vertex φ u.1 g := hu
    _ = vertex φ u.1 h := vertex_eq_of_base φ u.1 he
    _ = vertex φ w.1 h := congrArg (fun b => vertex φ b h) ht
    _ = w := hw.symm

/-- No cycle is possible in the coset graph of an injective amalgam. -/
theorem acyclic (hφ : ∀ b, Function.Injective (φ b)) : (graph φ).IsAcyclic := by
  intro v p hp
  have hn : 0<p.length := lt_of_lt_of_le (by decide : 0<3) hp.three_le_length
  choose r hr using (fun i : Fin p.length => adj_representatives φ (p.adj_getVert_succ i.isLt))
  let e (i : ℕ) : Amalgam φ := if hi : i<p.length then r ⟨i,hi⟩ else r ⟨0,hn⟩
  have he (i : ℕ) (hi : i<p.length) :
      p.getVert i=vertex φ (p.getVert i).1 (e i) ∧
      p.getVert (i+1)=vertex φ (p.getVert (i+1)).1 (e i) := by
    dsimp only [e]
    rw [dite_eq_left hi]
    exact hr ⟨i,hi⟩
  have hend : e p.length=e 0 := by
    simp only [e,dite_eq_right (lt_irrefl _),dite_eq_left hn]
  have hlast : p.getVert p.length=p.getVert 0 := by simp
  let b (i : ℕ) := (p.getVert (i+1)).1
  have hf : ∀ i<p.length, (e i)⁻¹*e (i+1)∈Factor φ (b i) := by
    intro i hi
    apply (vertex_eq_iff φ (b i) _ _).mp
    have h₁ := (he i hi).2
    by_cases hi' : i+1<p.length
    · exact h₁.symm.trans (he (i+1) hi').1
    · have hi' : i+1=p.length := by omega
      rw [hi',hend]
      rw [hi'] at h₁
      simpa only [b,hi',hlast] using h₁.symm.trans (hlast.trans (he 0 hn).1)
  have hd : ∀ i<p.length, (e i)⁻¹*e (i+1)∉(PushoutI.base φ).range := by
    intro i hi hmem
    by_cases hi' : i+1<p.length
    · have heq : p.getVert i=p.getVert (i+2) := other_endpoint_eq φ
        (he i hi).1 (by simpa only [Nat.add_assoc] using (he (i+1) hi').2)
        (p.adj_getVert_succ hi).1 (by simpa only [Nat.add_assoc] using (p.adj_getVert_succ hi').1) hmem
      have hne := hp.getVert_sub_one_ne_getVert_add_one (i := i+1) (by omega)
      apply hne
      simpa only [Nat.add_sub_cancel,Nat.add_assoc] using heq
    · have hi' : i+1=p.length := by omega
      have hmem' : (e i)⁻¹*e 0∈(PushoutI.base φ).range := by simpa only [hi',hend] using hmem
      have heq : p.getVert i=p.getVert 1 := other_endpoint_eq φ
        (he i hi).1 (he 0 hn).2 (p.adj_getVert_succ hi).1
        (by simpa only [hi',hlast] using (p.adj_getVert_succ hn).1) hmem'
      have hi1 := hp.getVert_injOn' (by change i≤p.length-1; omega)
        (by change 1≤p.length-1; have := hp.three_le_length; omega) heq
      have := hp.three_le_length
      omega
  have ha : ∀ i, i+1<p.length → b i≠b (i+1) := by
    intro i hi
    exact (p.adj_getVert_succ hi).1
  have hnon := transition_not_base φ hφ e b p.length hn hf hd ha
  apply hnon
  rw [hend,inv_mul_cancel]
  exact (PushoutI.base φ).range.one_mem

/-- The Bass--Serre tree of an injective two-factor amalgam. -/
theorem isTree (hφ : ∀ b, Function.Injective (φ b)) : (graph φ).IsTree :=
  ⟨connected φ,acyclic φ hφ⟩

end HarmonicArtin.ParabolicIntersections.AmalgamTree

end OAI
